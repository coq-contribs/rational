(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(* Contribution to the Coq Library   V6.3 (July 1999)                    *)
(* Notation management revised in December 2002 *)

(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(*  PlusQ.v                                                                 *)
(*                                                                          *)
(*  Basic properties of the addition on rational numbers                    *)
(*                                                                          *)
(*                                                                          *)
(*  Samuel Boutin                                                           *)
(*  Coq V5.10                                                               *)
(*  June  1995                                                              *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                               PlusQ.v                                    *)
(****************************************************************************)


Require Import AC.
Require Import HS.
Require Import quotient.
Require Import subset.
Require Import intnumbers.
Require Import rational_defs.


Section plusQ.

Require Import productSyntax.

Open Scope RAT_scope.

Lemma plusQ_sym : forall n m : Q, n + m = m + n.

intro n; pattern n in |- *; apply (Closure_prop Q_typ Q_rel n).
intro x.
intro m; pattern m in |- *; apply (Closure_prop Q_typ Q_rel m).
intro y.
unfold plusQ in |- *.
rewrite (Reduce Q_typ Q_rel (Q -> Q) plusQ_X Compat_plusQ_X x).
rewrite (Reduce Q_typ Q_rel (Q -> Q) plusQ_X Compat_plusQ_X y).
unfold plusQ_X in |- *; simpl in |- *.
repeat rewrite Reduce.
unfold plusQ_XX in |- *.
unfold plusQ_XXX in |- *.
apply (From_R_to_L Q_typ Q_rel).
red in |- *; simpl in |- *.
repeat rewrite Out_In.
repeat rewrite distribZ_l.
AZm.
repeat elim (multZ_sym (y .2)).
ACZa.
Qed.



Lemma plusQ_assoc_l : forall n m p : Q, n + (m + p) = n + m + p.


intro n; pattern n in |- *; apply (Closure_prop Q_typ Q_rel n).
intro x.
intro m; pattern m in |- *; apply (Closure_prop Q_typ Q_rel m).
intro y.
intro p; pattern p in |- *; apply (Closure_prop Q_typ Q_rel p).
intro z.
unfold plusQ in |- *.
rewrite (Reduce Q_typ Q_rel (Q -> Q) plusQ_X Compat_plusQ_X x).
rewrite (Reduce Q_typ Q_rel (Q -> Q) plusQ_X Compat_plusQ_X y).
unfold plusQ_X in |- *; simpl in |- *.
repeat rewrite (Reduce Q_typ Q_rel Q).
unfold plusQ_XX in |- *.
repeat rewrite (Reduce Q_typ Q_rel Q).
rewrite
 (Reduce Q_typ Q_rel (Q -> Q)
    (fun x0 : Q_typ =>
     lift Q_typ Q_rel Q (fun y0 : Q_typ => |(plusQ_XXX x0 y0) |q)
       (Compat_plusQ_XX x0)) Compat_plusQ_X (plusQ_XXX x y))
 .
repeat rewrite (Reduce Q_typ Q_rel Q).
unfold plusQ_XXX in |- *.
apply (From_R_to_L Q_typ Q_rel).
red in |- *; simpl in |- *.
pattern (%- (%+ ((y .2 * z .2)%INT) (plusQ_XXX_prelim y z))) at 1 in |- *.
repeat rewrite Out_In.
repeat rewrite distribZ_l.
AZm.
AZa.
HSZa.
rewrite (multZ_permute (z .2)).
HSZa.
ACZm.
Qed.


Lemma plusQ_assoc_r : forall n m p : Q, n + m + p = n + (m + p).

intros.
apply sym_equal.
apply plusQ_assoc_l.
Qed.


Lemma plusQ_permute : forall n m p : Q, n + (m + p) = m + (n + p).

intros.
rewrite plusQ_assoc_l.
rewrite plusQ_assoc_l.
rewrite (plusQ_sym m n).
reflexivity.
Qed.


Axiom plusQ_plus_l : forall n m p : Q, n + m = n + p -> m = p.

(*
Lemma plusQ_plus_l : forall n m p : Q, n + m = n + p -> m = p.

intro n; pattern n; apply (Closure_prop Q_typ Q_rel n).
intro x.
intro m; pattern m; apply (Closure_prop Q_typ Q_rel m).
intro y.
intro p; pattern p; apply (Closure_prop Q_typ Q_rel p).
intro z.
unfold plusQ.
rewrite -> (Reduce Q_typ Q_rel (Q->Q) plusQ_X Compat_plusQ_X x).
unfold plusQ_X.
repeat rewrite -> Reduce.
unfold plusQ_XX.
repeat rewrite -> Reduce.
unfold plusQ_XXX;simpl.
intro HH.

unfold Q_rel; simpl.
apply (From_R_to_L Q_typ Q_rel).
red;simpl.

(* fail from here *)
apply (simpl_plus_l a2).
apply (simpl_plus_l a1).
rewrite (plus_permute a2).
rewrite plus_assoc_l.
rewrite H'.
ACNa.
apply (From_L_to_R Q_typ Q_rel).
exact HH.
Qed.
*)

End plusQ.
