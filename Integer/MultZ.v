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
(*  MultZ.v                                                                 *)
(*                                                                          *)
(*  Basic properties of the multiplication on rational numbers              *)
(*                                                                          *)
(*                                                                          *)
(*  Samuel Boutin                                                           *)
(*  Coq V5.10                                                               *)
(*  June  1995                                                              *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                              MultZ.v                                     *)
(****************************************************************************)


Require Import AC.
Require Import HS.
Require Import quotient.
Require Import integer_defs.
Require Import PlusZ.


Section MultZ.

Require Import nat.

(* To get operators of nat available, but we don't open nat as default...*)

Open Scope INT_scope.

Lemma multZ_sym : forall n m : Z, n * m = m * n.

intro n; pattern n in |- *; apply (Closure_prop Z_typ Z_rel n).
simple induction x; intros a1 a2.
intro m; pattern m in |- *; apply (Closure_prop Z_typ Z_rel m).
simple induction x0; intros b1 b2.
unfold multZ in |- *.
rewrite (Reduce Z_typ Z_rel (Z -> Z) multZ_X Compat_multZ_X (a1, a2)).
rewrite (Reduce Z_typ Z_rel (Z -> Z) multZ_X Compat_multZ_X (b1, b2)).
unfold multZ_X in |- *; simpl in |- *.
repeat rewrite Reduce.
unfold multZ_XX in |- *; simpl in |- *.
repeat rewrite Reduce.
unfold multZ_XXX in |- *; simpl in |- *.
apply (From_R_to_L Z_typ Z_rel).
red in |- *; simpl in |- *.
repeat rewrite (mult_comm b1).
repeat rewrite (mult_comm b2).
ACNa.
Qed.


Lemma multZ_assoc_l : forall n m p : Z, n * (m * p) = n * m * p.

intro n; pattern n in |- *; apply (Closure_prop Z_typ Z_rel n).
simple induction x; intros a1 a2.
intro m; pattern m in |- *; apply (Closure_prop Z_typ Z_rel m).
simple induction x0; intros b1 b2.
intro p; pattern p in |- *; apply (Closure_prop Z_typ Z_rel p).
simple induction x1; intros c1 c2.
unfold multZ in |- *; simpl in |- *.
rewrite (Reduce Z_typ Z_rel (Z -> Z) multZ_X Compat_multZ_X (b1, b2)).
rewrite (Reduce Z_typ Z_rel (Z -> Z) multZ_X Compat_multZ_X (a1, a2)).
unfold multZ_X in |- *; simpl in |- *.
repeat rewrite (Reduce Z_typ Z_rel Z).
unfold multZ_XX in |- *; simpl in |- *.
repeat rewrite (Reduce Z_typ Z_rel Z).
unfold multZ_XXX in |- *; simpl in |- *.
rewrite
 (Reduce Z_typ Z_rel (Z -> Z)
    (fun x : Z_typ =>
     lift Z_typ Z_rel Z
       (fun y : Z_typ =>
        |((x .1 * y .1 + x .2 * y .2)%nat, (x .1 * y .2 + x .2 * y .1)%nat)
        |z) (Compat_multZ_XX x)) Compat_multZ_X
    ((a1 * b1 + a2 * b2)%nat, (a1 * b2 + a2 * b1)%nat))
 .
repeat rewrite (Reduce Z_typ Z_rel Z).
simpl in |- *.
apply (From_R_to_L Z_typ Z_rel).
red in |- *; simpl in |- *.
(* Apply distributivity to obtain normal form (a sum of products)       *)
repeat rewrite NATURAL.mult_plus_distr_l.
repeat rewrite mult_plus_distr_r.
ANm.
ANa.
(*         everything atom of the form a*b*c       *)
ACNa.
Qed.

Lemma multZ_permute : forall n m p : Z, n * (m * p) = m * (n * p).

(* almost exactly as previous lemma ! *)
intro n; pattern n in |- *; apply (Closure_prop Z_typ Z_rel n).
simple induction x; intros a1 a2.
intro m; pattern m in |- *; apply (Closure_prop Z_typ Z_rel m).
simple induction x0; intros b1 b2.
intro p; pattern p in |- *; apply (Closure_prop Z_typ Z_rel p).
simple induction x1; intros c1 c2.
unfold multZ in |- *; simpl in |- *.
rewrite (Reduce Z_typ Z_rel (Z -> Z) multZ_X Compat_multZ_X (b1, b2)).
rewrite (Reduce Z_typ Z_rel (Z -> Z) multZ_X Compat_multZ_X (a1, a2)).
unfold multZ_X in |- *; simpl in |- *.
repeat rewrite (Reduce Z_typ Z_rel Z).
unfold multZ_XX in |- *; simpl in |- *.
repeat rewrite (Reduce Z_typ Z_rel Z).
unfold multZ_XXX in |- *; simpl in |- *.
apply (From_R_to_L Z_typ Z_rel).
red in |- *; simpl in |- *.
repeat rewrite NATURAL.mult_plus_distr_l.
repeat rewrite mult_plus_distr_r.
ANm.
ANa.
repeat elim (mult_permute a1).
repeat elim (mult_permute a2).
ACNa.
Qed.


Lemma multZ_assoc_r : forall n m p : Z, n * m * p = n * (m * p).

intros.
elim multZ_sym.
elim (multZ_sym (n * m)).
elim (multZ_assoc_l n m p).
auto.
Qed.


Lemma multZ_O : forall n : Z, n * 0 = 0.

intro n; pattern n in |- *; apply (Closure_prop Z_typ Z_rel n).
simple induction x; intros a1 a2.
unfold multZ in |- *.
rewrite (Reduce Z_typ Z_rel (Z -> Z) multZ_X Compat_multZ_X (a1, a2)).
unfold multZ_X in |- *.
repeat rewrite Reduce.
unfold multZ_XX in |- *.
unfold multZ_XXX in |- *; simpl in |- *.
repeat elim (mult_comm 0).
simpl in |- *.
auto.
Qed.

(* Voici un lemme faux qu'on peut adapter avec n=/ 0 un de ces jours
Lemma multZ_mult_l  : (n,m,p:Z)  (n*m) = (n*p) ->  m = p.

Intro n; Pattern n; Apply (Closure_prop Z_typ Z_rel n).
Induction x; Intros a1 a2.
Intro m; Pattern m; Apply (Closure_prop Z_typ Z_rel m).
Induction x; Intros b1 b2.
Intro p; Pattern p; Apply (Closure_prop Z_typ Z_rel p).
Induction x; Intros c1 c2.
Unfold multZ.
Rewrite -> (Reduce Z_typ Z_rel Z->Z multZ_X Compat_multZ_X (a1,a2)).
Unfold multZ_X.
Repeat Rewrite -> Reduce.
Unfold multZ_XX.
Repeat Rewrite -> Reduce.
Unfold multZ_XXX;Simpl.
Intro HH.
Cut 'N: (Z_rel (a1 + b1,a2 + b2) (a1 + c1,a2 + c2)).
Unfold Z_rel; Simpl.
Intro H'.
Apply (From_R_to_L Z_typ Z_rel).
Red;Simpl.
Apply (simpl_plus_l a2).
Apply (simpl_plus_l a1).
Rewrite (plus_permute a2).
Rewrite plus_assoc_l.
Rewrite H'.
ACNa.


Red;Simpl.
Apply (simpl_mult_l a2).
Apply (simpl_mult_l a1).
Rewrite (mult_permute a2).
Rewrite mult_assoc_l.
Rewrite H'.
ACNa.

Apply (axiom_quotient Z_typ  Z_rel).
Subtree proved!
Qed.

*)


Lemma distribZ : forall n m p : Z, n * (m + p) = n * m + n * p.

intro n; pattern n in |- *; apply (Closure_prop Z_typ Z_rel n).
simple induction x; intros a1 a2.
intro m; pattern m in |- *; apply (Closure_prop Z_typ Z_rel m).
simple induction x0; intros b1 b2.
intro p; pattern p in |- *; apply (Closure_prop Z_typ Z_rel p).
simple induction x1; intros c1 c2.
unfold multZ in |- *.
rewrite (Reduce Z_typ Z_rel (Z -> Z) multZ_X Compat_multZ_X (a1, a2)).
unfold multZ_X in |- *.
repeat rewrite Reduce.
unfold multZ_XX in |- *.
repeat rewrite Reduce.
unfold multZ_XXX in |- *; simpl in |- *.
unfold plusZ in |- *.
rewrite (Reduce Z_typ Z_rel (Z -> Z) plusZ_X Compat_plusZ_X (b1, b2)).
rewrite
 (Reduce Z_typ Z_rel (Z -> Z) plusZ_X Compat_plusZ_X
    ((a1 * b1 + a2 * b2)%nat, (a1 * b2 + a2 * b1)%nat))
 .
unfold plusZ_X in |- *.
repeat rewrite Reduce.
unfold plusZ_XX in |- *.
repeat rewrite Reduce.
unfold plusZ_XXX in |- *; simpl in |- *.
apply (From_R_to_L Z_typ Z_rel).
red in |- *; simpl in |- *.
repeat rewrite NATURAL.mult_plus_distr_l.
ACNa.
Qed.

Lemma distribZ_l : forall n m p : Z, (m + p) * n = m * n + p * n.

intros.
repeat elim (multZ_sym n).
apply distribZ.
Qed.

(* TODO:

Lemma proof_plusQ : (n,m:Z)(Pos n)->(Pos m) ->(Pos n #z m).

Unfold Nonzero;Simpl.
Intro n; Pattern n; Apply (Closure_prop Z_typ Z_rel n).
Induction x; Intros a1 a2.
Intro m; Pattern m; Apply (Closure_prop Z_typ Z_rel m).
Induction x; Intros b1 b2.
Intros.
Unfold multZ;Simpl.
Rewrite -> (Reduce Z_typ Z_rel Z->Z multZ_X Compat_multZ_X (a1,a2)).
Unfold multZ_X;Simpl.
Rewrite -> (Reduce Z_typ Z_rel).
Unfold multZ_XX;Simpl.
Unfold multZ_XXX;Simpl.

*)
Axiom mult_minus : forall x y : Z, - x * y = - (x * y).


Lemma sign_simpl : forall x y : Z, x = y -> - x = - y.
intros. elim H. auto.
Qed.

End MultZ.