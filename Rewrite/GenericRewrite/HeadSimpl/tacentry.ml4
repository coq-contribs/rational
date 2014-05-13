(* Contribution to the Coq Library, originally for V6.3 (July 1999) *)

open Libnames
open Globnames
open Proof_type
open Tacmach
open Tactics;;
open Tacticals;;
open Frame;;
open Basic;;
open Main;;

DECLARE PLUGIN "tacentry"

exception BAD_ARG;;

let execute id_typ id_op id_R id_simpl gls =
  let look = Universes.constr_of_reference in
  let op      = look id_op
  and simpl   = look id_simpl
  and typ     = look id_typ in
  let gls_c = pf_concl(gls) in
  if pf_is_matching gls (eq_pattern id_R) gls_c then
    let l = pf_matches gls (eq_pattern id_R) gls_c in
    let (typ,a,b) =
      match Names.Id.Map.bindings l with
	  [(_,typ);(_,a);(_,b)] -> (typ,a,b)
        | [(_,a);(_,b)]     -> (typ,a,b)
        | _        -> raise BAD_ARG in
    let a_tree = (tree_of_constr op a)
    and b_tree = (tree_of_constr op b) in
    match a_tree with
	Node(op,Leaf a_0,rA) ->
	  (match b_tree  with
	      Node(op,Leaf b_0,rB) ->
		let new_A = constr_of_tree op rA
		and new_B = constr_of_tree op rB in
		(apply simpl)
		(*(apply_term simpl [] ([a;new_A;new_B])*) gls
	    | _ -> raise BAD_ARG)
      | _ -> raise BAD_ARG
  else raise BAD_ARG
;;

let head_simpl id_typ id_op id_R id_eq id_com id_perm id_simpl id_neutral id_unitl id_unitr gls=
  let look = Universes.constr_of_reference in
  let op    = look id_op
  and typ   = look id_typ
  and eq    = look id_eq
  and n     = look id_neutral
  and unitl = look id_unitl
  and unitr = look id_unitr in
  let gls_c = pf_concl(gls) in
  if pf_is_matching gls (eq_pattern id_R) gls_c then
    let l = pf_matches gls (eq_pattern id_R) gls_c in
    let (typ,a,b) =
      (match Names.Id.Map.bindings l with
	  [(_,typ);(_,a);(_,b)]->(typ,a,b)
	| [(_,a);(_,b)] -> (typ,a,b)
	| _ -> raise BAD_ARG) in
    let a_tree = (tree_of_constr op a)
    and b_tree = (tree_of_constr op b) in
    try
      (let ltac_A,ltac_B = cOMMON_HEAD_SEARCH (op,a_tree,b_tree,n) in
       let one_step_coq =
         one_step_tac_of
           op typ id_perm id_com id_neutral unitl unitr gls eq in
       let action_A = tclTHENSEQ (List.map one_step_coq ltac_A) in
       let action_B = tclTHENSEQ (List.map one_step_coq ltac_B) in
       tclTHENSEQ [action_A; action_B; execute id_typ id_op id_R id_simpl]
         gls)
    with Do_nothing -> failwith
        "The tactic of Head Simplification cannot be applied here"
  else raise BAD_ARG
;;

(****** SYNTAXE POUR LA TACTIQUE AC_OF ***********)

TACTIC EXTEND HeadSimpl
  [ "HeadSimpl" global(typ) global(eq) global(op) global(com)
       global(perm) global(rel) global(simpl) global(unit)
       global(unitl) global(unitr)] ->
  [ Proofview.V82.tactic (head_simpl typ op rel eq com perm simpl unit unitl unitr) ]
END
