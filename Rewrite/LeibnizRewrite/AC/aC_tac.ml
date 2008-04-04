
open Libnames
open Proof_type
open Tacmach
open Tacticals
open Hipattern
open Sort_tac;;
open AC;;

(* Elle prends en argument l'op'erateur, les lemmes de
commutativit'e, d'associativit'e, assoc_inv et permut et
rend une tactique automatique *)

exception BAD_ARG;;

let ac_of id_op id_com id_perm identity gls=
  let look = constr_of_reference in
  let op    = look id_op
  and com   = look id_com
  and perm  = look id_perm in
  let gls_c = pf_concl(gls) in 
  let (_,(typ,a,b)) = find_eq_data_decompose gls_c in
    let a_tree = (tree_of_constr op a)     
    and b_tree = (tree_of_constr op b) in
    let tac_l = iDENTIFY (op,a_tree,b_tree) in
    let one_step_coq = one_step_tac_of op typ id_perm id_com gls identity in
    tclTHENSEQ (List.map one_step_coq tac_l) gls

;;

TACTIC EXTEND Ac_of
  [ "ac_of" global(eq) global(op) global(com) global(perm) ] 
  -> [ ac_of op com perm eq ]
END
