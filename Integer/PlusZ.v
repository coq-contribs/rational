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
(*  PlusZ.v                                                                 *)
(*                                                                          *)
(*  Basic properties of the addition on integers                            *)
(*                                                                          *)
(*                                                                          *)
(*  Samuel Boutin                                                           *)
(*  Coq V5.10                                                               *)
(*  June  1995                                                              *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                               PlusZ.v                                    *)
(****************************************************************************)


Require Import AC.
Require Import HS.
Require Import quotient.


Section PlusZ.

Require Import nat.
Require Import integer_defs.

(* To get operators of nat available, but we don't open nat as default...*)

Open Scope INT_scope.

Lemma plusZ_sym : forall n m : Z, n + m = m + n.

intro n; pattern n in |- *; apply (Closure_prop Z_typ Z_rel n).
simple induction x; intros a1 a2.
intro m; pattern m in |- *; apply (Closure_prop Z_typ Z_rel m).
simple induction x0; intros b1 b2.
unfold plusZ in |- *.
rewrite (Reduce Z_typ Z_rel (Z -> Z) plusZ_X Compat_plusZ_X (a1, a2)).
rewrite (Reduce Z_typ Z_rel (Z -> Z) plusZ_X Compat_plusZ_X (b1, b2)).
unfold plusZ_X in |- *; simpl in |- *.
repeat rewrite Reduce.
unfold plusZ_XX in |- *; simpl in |- *.
unfold plusZ_XXX in |- *; simpl in |- *.
apply (From_R_to_L Z_typ Z_rel).
red in |- *; simpl in |- *.
ACNa.
Qed.

Lemma plusZ_assoc_l : forall n m p : Z, n + (m + p) = n + m + p.

(* almost identical proof as previous lemma *)
intro n; pattern n in |- *; apply (Closure_prop Z_typ Z_rel n).
simple induction x; intros a1 a2.
intro m; pattern m in |- *; apply (Closure_prop Z_typ Z_rel m).
simple induction x0; intros b1 b2.
intro p; pattern p in |- *; apply (Closure_prop Z_typ Z_rel p).
simple induction x1; intros c1 c2.
unfold plusZ in |- *; simpl in |- *.
rewrite (Reduce Z_typ Z_rel (Z -> Z) plusZ_X Compat_plusZ_X (b1, b2)).
rewrite (Reduce Z_typ Z_rel (Z -> Z) plusZ_X Compat_plusZ_X (a1, a2)).
unfold plusZ_X in |- *; simpl in |- *.
repeat rewrite (Reduce Z_typ Z_rel Z).
unfold plusZ_XX in |- *; simpl in |- *.
repeat rewrite (Reduce Z_typ Z_rel Z).
unfold plusZ_XXX in |- *; simpl in |- *.
rewrite
 (Reduce Z_typ Z_rel (Z -> Z)
    (fun x : Z_typ =>
     lift Z_typ Z_rel Z
       (fun y : Z_typ => |((x .1 + y .1)%nat, (x .2 + y .2)%nat) |z)
       (Compat_plusZ_XX x)) Compat_plusZ_X ((a1 + b1)%nat, (a2 + b2)%nat))
 .
repeat rewrite (Reduce Z_typ Z_rel Z).
simpl in |- *.
apply (From_R_to_L Z_typ Z_rel).
red in |- *; simpl in |- *.
ACNa.
Qed.

Lemma plusZ_permute : forall n m p : Z, n + (m + p) = m + (n + p).

intro n; pattern n in |- *; apply (Closure_prop Z_typ Z_rel n).
simple induction x; intros a1 a2.
intro m; pattern m in |- *; apply (Closure_prop Z_typ Z_rel m).
simple induction x0; intros b1 b2.
intro p; pattern p in |- *; apply (Closure_prop Z_typ Z_rel p).
simple induction x1; intros c1 c2.
unfold plusZ in |- *; simpl in |- *.
rewrite (Reduce Z_typ Z_rel (Z -> Z) plusZ_X Compat_plusZ_X (b1, b2)).
rewrite (Reduce Z_typ Z_rel (Z -> Z) plusZ_X Compat_plusZ_X (a1, a2)).
unfold plusZ_X in |- *; simpl in |- *.
repeat rewrite (Reduce Z_typ Z_rel Z).
unfold plusZ_XX in |- *; simpl in |- *.
repeat rewrite (Reduce Z_typ Z_rel Z).
unfold plusZ_XXX in |- *; simpl in |- *.
apply (From_R_to_L Z_typ Z_rel).
red in |- *; simpl in |- *.
ACNa.
Qed.

Lemma plusZ_assoc_r : forall n m p : Z, n + m + p = n + (m + p).

intros.
elim plusZ_sym.
elim (plusZ_sym (n + m)).
rewrite <- (plusZ_assoc_l n m p).
auto.
Qed.


Lemma plusZ_plus_l : forall n m p : Z, n + m = n + p -> m = p.

intro n; pattern n in |- *; apply (Closure_prop Z_typ Z_rel n).
simple induction x; intros a1 a2.
intro m; pattern m in |- *; apply (Closure_prop Z_typ Z_rel m).
simple induction x0; intros b1 b2.
intro p; pattern p in |- *; apply (Closure_prop Z_typ Z_rel p).
simple induction x1; intros c1 c2.
unfold plusZ in |- *.
rewrite (Reduce Z_typ Z_rel (Z -> Z) plusZ_X Compat_plusZ_X (a1, a2)).
unfold plusZ_X in |- *.
repeat rewrite Reduce.
unfold plusZ_XX in |- *.
repeat rewrite Reduce.
unfold plusZ_XXX in |- *; simpl in |- *.
intro HH.
cut (Z_rel ((a1 + b1)%nat, (a2 + b2)%nat) ((a1 + c1)%nat, (a2 + c2)%nat)).
unfold Z_rel in |- *; simpl in |- *.
intro H'.
apply (From_R_to_L Z_typ Z_rel).
red in |- *; simpl in |- *.
apply (fun a b : nat => plus_reg_l a b a2).
apply (fun a b : nat => plus_reg_l a b a1).
rewrite (plus_permute a2).
rewrite plus_assoc.
rewrite H'.
ACNa.
apply (From_L_to_R Z_typ Z_rel).
exact HH.
Qed.

Lemma plusZ_O : forall n : Z, n + 0 = n.

intro n; pattern n in |- *; apply (Closure_prop Z_typ Z_rel n).
simple induction x; intros a1 a2.
unfold plusZ in |- *.
rewrite (Reduce Z_typ Z_rel (Z -> Z) plusZ_X Compat_plusZ_X (a1, a2)).
unfold plusZ_X in |- *.
repeat rewrite Reduce.
unfold plusZ_XX in |- *.
repeat rewrite Reduce.
unfold plusZ_XXX in |- *; simpl in |- *.
repeat elim (plus_comm 0).
simpl in |- *.
auto.
Qed.

End PlusZ.

