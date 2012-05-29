
open Errors
open Names
open Term
open Libnames
open Globnames
open Reductionops
open Tacticals
open Tacmach
open Tactics
open Equality
open Coqlib
open Auto
open Pattern
open Frame

(*  I. Relations entre constr et (constr,constr) tree *)

(* premi\`ere 'etape, mettre un constr sous la forme d'un
(constr,constr) tree et reciproquement *)

let rec tree_of_constr op c = match kind_of_term c with
  | App (op1,[|left;right|]) when op = op1 -> 
      Node(op,(tree_of_constr op left),(tree_of_constr op right))
  | _ -> Leaf c

let rec constr_of_tree op = function
  Leaf(x) -> x
| Node(x,l,r)-> 
  mkApp (op,[|(constr_of_tree op l);(constr_of_tree op r)|])
| Bottom -> anomaly "constr_of_tree"

(* deuxi\`eme 'etape, traduire un (constr,constr) TACTIC en
tactique Coq 
On suppose que COM, ASSOC, ASSOC_inv et PERMUT correspondent
`a des lemmes ('egalit'es) et donc que l'on va leur
associer un cut suivi d'un rewrite
*)

(* s'equence 'el'ementaire associ'ee `a une permutation *)



let one_step_tac_of op typ id_perm id_com id_neutral unitl unitr gls identity =
let ac = id_of_string "AC_last" in
function 
    (PERMUT(Leaf a1,Leaf a2,rr),lleaf) ->


  let old_A = constr_of_tree op
        (cons_tree op (Node(op,Leaf a1,Node(op,Leaf a2,rr))) (List.rev lleaf))
  in
   let new_A = constr_of_tree op
        (cons_tree op (Node(op,Leaf a2,Node(op,Leaf a1,rr))) (List.rev lleaf))
  in
   let t_perm = constr_of_reference id_perm in
   let t1 = whd_betadeltaiota (pf_env gls) (project gls)
	      (mkApp (identity, [|typ;old_A;new_A|]))
   and t2 = whd_betadeltaiota (pf_env gls) (project gls)
	       (applist (t_perm, [a1;a2;(constr_of_tree op rr)]))
 in
   (tclTHENS
      (cut t1) 
      ([(tclTRY
	   (tclTHEN
	      (tclTHEN
		 (introduction ac)
		 (rewriteLR (mkVar ac)))
	      (clear [ac]))) ; 
	tclTRY
	  (tclTHEN
             (simplest_elim t2)
	     default_auto)]))

  | (COM(Leaf a1,Leaf a2),lleaf) ->


    let old_A = constr_of_tree op
        (cons_tree op (Node(op,Leaf a1,Leaf a2)) (List.rev lleaf))
    in
    let new_A = constr_of_tree op
        (cons_tree op (Node(op,Leaf a2,Leaf a1)) (List.rev lleaf))
     in
      let t_com = constr_of_reference id_com in
      let t1 = whd_betadeltaiota (pf_env gls) (project gls)
		  (mkApp (identity, [|typ;old_A;new_A|]))
      and t2 =
	whd_betadeltaiota (pf_env gls) (project gls) (applist (t_com,[a1;a2] ))
      in
      (tclTHENS
         (cut t1)
	 ([tclTRY
	     (tclTHEN
		(tclTHEN
		   (introduction ac) 
		   (rewriteLR (mkVar ac)))
		(clear [ac]));
	   tclTRY  
	     (tclTHEN
		(simplest_elim t2)
		default_auto)]))

   | (EXPAND(Leaf a,t),[]) ->     (apply unitl)

 (* was (resolve (const_of_id unitl)) *)

   | (EXPAND(t,Leaf a),[]) ->  (apply unitr)
 (* was  (resolve (const_of_id unitr)) *)

   | _ -> assert false (*Cette clause était absente dans la version initiale*)

let eq_pattern eq =
  let ty = Retyping.get_type_of (Global.env()) Evd.empty
    (constr_of_reference eq) in
  let nargs = List.length (fst (splay_prod (Global.env()) Evd.empty ty)) in
  if nargs <> 2 & nargs <> 3 then
    error "Can only deal with an equality of the form (eqname a b) or (eqname A a b)";
  PApp(PRef eq, 
    Array.init nargs
      (fun i -> PMeta (Some (Nameops.make_ident "X" (Some (i+1))))))
