
open Libnames
open Globnames
open Proof_type
open Tacmach
open Tacticals
open Hipattern
open Sort_tac;;
open AC;;

DECLARE PLUGIN "aC_tac"

(* Elle prend en argument l'op'erateur, les lemmes de
commutativit'e, d'associativit'e, assoc_inv et permut et
rend une tactique automatique *)

exception BAD_ARG;;

let ac_of id_op id_com id_perm identity=
  Proofview.Goal.enter begin fun gl ->
  let look = Universes.constr_of_reference in
  let op    = look id_op
  and com   = look id_com
  and perm  = look id_perm in
  let gls_c = Proofview.Goal.concl gl in
  let (_, _, (typ,a,b)) = find_this_eq_data_decompose gl gls_c in
    let a_tree = (tree_of_constr op a)
    and b_tree = (tree_of_constr op b) in
    let tac_l = iDENTIFY (op,a_tree,b_tree) in
    let one_step_coq = Tacmach.New.of_old (fun gl -> one_step_tac_of op typ id_perm id_com gl identity) gl in
    Proofview.V82.tactic (fun gl -> tclTHENSEQ (List.map one_step_coq tac_l) gl)
  end

TACTIC EXTEND Ac_of
  [ "ac_of" global(eq) global(op) global(com) global(perm) ]
  -> [ ac_of op com perm eq ]
END
