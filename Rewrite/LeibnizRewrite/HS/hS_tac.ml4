(* Contribution to the Coq Library, originally for V6.3 (July 1999) *)

(*i camlp4deps: "parsing/grammar.cma" i*)

open Errors
open Libnames
open Globnames
open Proof_type
open Tacmach
open Tactics
open Tacticals
open Pattern
open Hipattern
open Sort_tac
open Struct
open HS

exception BAD_ARG;;

let execute id_op id_simpl gls =
  let look = constr_of_reference
  in
    let op      = look id_op
    and simpl   = look id_simpl
      in
      let gls_c = pf_concl(gls)
      in
        let (_,(typ,a,b)) = find_eq_data_decompose gls gls_c
	in
 let a_tree = (tree_of_constr op a)
 and b_tree = (tree_of_constr op b)
             in
match a_tree with
   Node(op,Leaf a_0,rA) ->
   (match b_tree  with
       Node(op,Leaf b_0,rB) ->
 let new_A = constr_of_tree op rA
 and new_B = constr_of_tree op rB
  in      (apply simpl)
    (* was resolve (const_of_id id_simpl) *)
     (* (apply_term simpl [] ([a;new_A;new_B])*) gls
       | _ -> raise BAD_ARG
   )
  | _ -> raise BAD_ARG
;;

let hs_of id_op id_com id_perm identity id_simpl gls =
  let op    = constr_of_reference id_op in
  let gls_c = pf_concl(gls) in
    let (_,(typ,a,b)) = find_eq_data_decompose gls gls_c in
    let a_tree = (tree_of_constr op a)
    and b_tree = (tree_of_constr op b)
    in
    try
      let ltac_A,ltac_B = cOMMON_HEAD_SEARCH (op,a_tree,b_tree) in
      let one_step_coq = one_step_tac_of op typ id_perm id_com gls identity in
      let action_A = tclTHENSEQ (List.map one_step_coq ltac_A) in
      let action_B = tclTHENSEQ (List.map one_step_coq ltac_B) in
      tclTHENSEQ [action_A;action_B;execute id_op id_simpl] gls
    with _ -> error
        "The tactic of Head Simplification cannot be applied here"
;;

(****** SYNTAXE POUR LA TACTIQUE AC_OF ***********)

open Genarg

TACTIC EXTEND Hs_of
  [ "hs_of" global(eq) global(op) global(com) global(perm) global(simpl)]
    -> [ hs_of op com perm eq simpl ]
END
