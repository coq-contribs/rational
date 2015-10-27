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
open Proofview.Notations

DECLARE PLUGIN "hS_tac"

exception BAD_ARG;;

let execute id_op id_simpl =
  Proofview.Goal.nf_enter { enter = begin fun gl ->
    let look = Universes.constr_of_reference in
    let op      = look id_op in
    let simpl   = look id_simpl in
    let gls_c = Proofview.Goal.concl gl in
    let (_, _,(typ,a,b)) = find_eq_data_decompose gl gls_c in
    let a_tree = (tree_of_constr op a) in
    let b_tree = (tree_of_constr op b) in
    let (op, a_0, rA) = match a_tree with
    | Node (op, Leaf a_0, rA) -> (op, a_0, rA)
    | _ -> raise BAD_ARG
    in
    let (op, b_0, rB) = match b_tree with
    | Node (op, Leaf b_0, rB) -> (op, b_0, rB)
    | _ -> raise BAD_ARG
    in
    let _ = constr_of_tree op rA in
    let _ = constr_of_tree op rB in
    apply simpl
  end }

let hs_of id_op id_com id_perm identity id_simpl =
  Proofview.Goal.nf_enter begin fun gl ->
  let op    = Universes.constr_of_reference id_op in
  let gls_c = Proofview.Goal.concl gl in
    let (_, _, (typ,a,b)) = find_eq_data_decompose gl gls_c in
    let a_tree = (tree_of_constr op a) in
    let b_tree = (tree_of_constr op b) in
    try
      let ltac_A,ltac_B = cOMMON_HEAD_SEARCH (op,a_tree,b_tree) in
      let one_step_coq action = Proofview.V82.tactic (fun gl -> one_step_tac_of op typ id_perm id_com gl identity action gl) in
      let action_A = Tacticals.New.tclTHENLIST (List.map one_step_coq ltac_A) in
      let action_B = Tacticals.New.tclTHENLIST (List.map one_step_coq ltac_B) in
      Tacticals.New.tclTHENLIST [action_A;action_B;execute id_op id_simpl]
    with e when Errors.noncritical e ->
      Tacticals.New.tclZEROMSG (Pp.str "The tactic of Head Simplification cannot be applied here")
  end

(****** SYNTAXE POUR LA TACTIQUE AC_OF ***********)

open Genarg

TACTIC EXTEND Hs_of
  [ "hs_of" global(eq) global(op) global(com) global(perm) global(simpl)]
    -> [ hs_of op com perm eq simpl ]
END
