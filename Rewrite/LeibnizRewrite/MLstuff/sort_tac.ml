
open Errors
open Names
open Reductionops
open Term
open Evd
open Libnames
open Globnames
open Tacmach
open Tacticals
open Tactics
open Equality
open Auto
open Struct

(*  I. Relations entre constr et (constr,constr) tree *)

(* premi\`ere 'etape, mettre un constr sous la forme d'un
(constr,constr) tree et reciproquement *)

let rec tree_of_constr op c = match kind_of_term c with
  | App (op1,[|left;right|]) when Constr.equal op op1 -> 
      Node(op,(tree_of_constr op left),(tree_of_constr op right))
  | _ -> Leaf c

let rec constr_of_tree op = function
  Leaf(x) -> x
| Node(x,l,r)-> 
  mkApp (op,[|(constr_of_tree op l);(constr_of_tree op r)|])
| Bottom -> anomaly (Pp.str "constr_of_tree")


(* deuxi\`eme 'etape, traduire un (constr,constr) TACTIC en
tactique Coq 
On suppose que COM, ASSOC, ASSOC_inv et PERMUT correspondent
`a des lemmes ('egalit'es) et donc que l'on va leur
associer un cut suivi d'un rewrite
*)

(* s'equence 'el'ementaire associ'ee `a une permutation *)


let one_step_tac_of op typ t_perm t_com gls identity = 
let ac = id_of_string "AC_last" in
function 
    (PERMUT(Leaf a1,Leaf a2,rr),lleaf) ->
 let left = constr_of_tree op (Node(op,Leaf a1,Node(op,Leaf a2,rr)))
 and right= constr_of_tree op (Node(op,Leaf a2,Node(op,Leaf a1,rr)))
 in 
  let old_A = constr_of_tree op
        (cons_tree op (Node(op,Leaf a1,Node(op,Leaf a2,rr))) (List.rev lleaf))
  in
   let new_A = constr_of_tree op
        (cons_tree op (Node(op,Leaf a2,Node(op,Leaf a1,rr))) (List.rev lleaf))
  in 
   let t1 = whd_betadeltaiota (pf_env gls) (project gls)
	       (mkApp (Universes.constr_of_reference identity, [|typ;old_A;new_A|]))
  in 
   let t2 = whd_betadeltaiota (pf_env gls) (project gls) 
		    (applist (Universes.constr_of_reference t_perm,
		       [a1;a2;(constr_of_tree op rr)]))
 in
   Proofview.V82.of_tactic (Tacticals.New.tclTHENS (cut t1)
       [Tacticals.New.tclTRY
	    (Tacticals.New.tclTHEN
               (Tacticals.New.tclTHEN (introduction ac) (rewriteLR (mkVar ac)))
               (clear [ac])) ; 
(* (TRY  ((cut  (whd_betadeltaiota (Project gls)
        (applist (const_value (Project gls) T_perm,
             [a1;a2;(constr_of_tree op rr)]))))
          THENS 
       [red THEN  (auto NONE);
        (elim (nvar (string_of_id t_perm))) THEN (auto NONE)]))
    Probl`eme de constante opaque avec T_perm !!! *)
	 Tacticals.New.tclTRY
	   (Tacticals.New.tclTHEN
	      (simplest_elim t2)
	      default_auto) ])

   | (COM(Leaf a1,Leaf a2),lleaf) ->
       let left = constr_of_tree op (Node(op,Leaf a1,Leaf a2))
       and right =constr_of_tree op (Node(op,Leaf a2,Leaf a1)) in 
       let old_A = constr_of_tree op
		     (cons_tree op (Node(op,Leaf a1,Leaf a2)) 
			(List.rev lleaf)) in
       let new_A = constr_of_tree op
		     (cons_tree op (Node(op,Leaf a2,Leaf a1)) 
			(List.rev lleaf)) in
       let t1 = whd_betadeltaiota (pf_env gls) (project gls)
		  (mkApp (Universes.constr_of_reference identity,[|typ;old_A;new_A|])) in
       let t2 = whd_betadeltaiota (pf_env gls) (project gls)
			     (applist (Universes.constr_of_reference t_com,[a1;a2])) in
	 Proofview.V82.of_tactic (Tacticals.New.tclTHENS
           (cut t1)
	   [ Tacticals.New.tclTRY (Tacticals.New.tclTHEN 
		       (Tacticals.New.tclTHEN
			  (introduction ac) 
			  (rewriteLR (mkVar ac)))
		       (clear [ac]));
	     Tacticals.New.tclTRY (Tacticals.New.tclTHEN
		       (simplest_elim t2)
		       default_auto) ])
   | _ -> anomaly (Pp.str "Should not occur")
