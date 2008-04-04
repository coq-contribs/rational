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
(*  integer_defs.v                                                               *)
(*                                                                          *)
(*  Definition of integers from natural numbers using quotient types        *)
(*                                                                          *)
(*                                                                          *)
(*  Samuel Boutin                                                           *)
(*  Coq V5.10                                                               *)
(*  June  1995                                                              *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                             integer_defs.v                                    *)
(****************************************************************************)


Require Import Arith.
Require Import quotient.
Require Import HS.
Require Import AC.

(*****************************************************************************)
(*                          Some basic stuff                                 *)
(*****************************************************************************)

Lemma eq_pair :
 forall (A B : Set) (x y : A * B), fst x = fst y -> snd x = snd y -> x = y.
intros A B.
simple induction x; intros x1 x2.
simple induction y; intros y1 y2.
simpl in |- *.
intros Hx Hy.
elim Hx.
elim Hy.
auto with arith.
Qed.


(*****************************************************************************)
(*                   Definition of Z as a quotient type                      *)
(*****************************************************************************)

Definition Z_typ := (nat * nat)%type.

Require Import nat.

(* Z is define as the symetric completion of the semi-group N *)


Definition Z_rel (x y : nat * nat) := x .1 + y .2 = y .1 + x .2.

Hint Unfold Z_rel.

Definition Z := Z_typ / Z_rel.

Notation "| c | 'z'" := (In Z_typ Z_rel c) (at level 20, c at level 0).

Notation "0" := (|(0, 0) |z) (at level 11) : INT_scope.
Notation "1" := (|(1, 0) |z) (at level 11) : INT_scope.

(*****************************************************************************
 unary_minus : Z -> Z 
*****************************************************************************)

Section Integers.

Definition swap (x : nat * nat) : Z := |(x .2, x .1) |z.

Lemma Compat_swap : Compat Z_typ Z_rel Z swap.

red in |- *.
simple induction x; intros x1 x2.
simple induction y; intros y1 y2.
unfold Z_rel, swap in |- *; simpl in |- *.
intro H.
apply (From_R_to_L Z_typ Z_rel).
red in |- *; simpl in |- *.
rewrite (plus_comm x2 y1).
rewrite <- H.
ACNa.
Qed.

Definition unary_minus : Z -> Z := lift Z_typ Z_rel Z swap Compat_swap.

(*****************************************************************************
 plusZ : Z -> Z -> Z
*****************************************************************************)

Definition plusZ_XXX (x y : Z_typ) : Z_typ := (x .1 + y .1, x .2 + y .2).

Definition plusZ_XX (x y : Z_typ) : Z := |(plusZ_XXX x y) |z.

Lemma Compat_plusZ_XX : forall x : Z_typ, Compat Z_typ Z_rel Z (plusZ_XX x).

simple induction x; intros x1 x2.
red in |- *.
simple induction x0; intros y1 y2.
simple induction y; intros z1 z2.
unfold Z_rel, plusZ_XX, plusZ_XXX in |- *; simpl in |- *.
intro H.
apply (From_R_to_L Z_typ Z_rel).
red in |- *; simpl in |- *.
ANa.
HSNa.
HSNa.
assumption.
Qed.

Definition plusZ_X (x : Z_typ) : Z -> Z :=
  lift Z_typ Z_rel Z (plusZ_XX x) (Compat_plusZ_XX x).

Lemma Compat_plusZ_X : Compat Z_typ Z_rel (Z -> Z) plusZ_X.

red in |- *.
simple induction x; intros x1 x2.
simple induction y; intros y1 y2.
unfold Z_rel in |- *; simpl in |- *.
intro H.
apply Ext.
intro z.
pattern z in |- *.
apply (Closure_prop Z_typ Z_rel z).
simple induction x0; intros a1 a2.
unfold plusZ_X in |- *.
repeat rewrite Reduce.
unfold plusZ_XX in |- *.
apply (From_R_to_L Z_typ Z_rel).
unfold Z_rel, plusZ_XXX in |- *; simpl in |- *.
ANa.
HSNa.
HSNa.
assumption.
Qed.

Definition plusZ : Z -> Z -> Z :=
  lift Z_typ Z_rel (Z -> Z) plusZ_X Compat_plusZ_X.

Infix "+" := plusZ (at level 50, left associativity) : INT_scope.

(*****************************************************************************)
(*                         multZ : Z -> Z -> Z                               *)
(*****************************************************************************)

Definition multZ_XXX (x y : Z_typ) : Z_typ :=
  (x .1 * y .1 + x .2 * y .2, x .1 * y .2 + x .2 * y .1).

Definition multZ_XX (x y : Z_typ) : Z := |(multZ_XXX x y) |z.

Lemma Compat_multZ_XX : forall x : Z_typ, Compat Z_typ Z_rel Z (multZ_XX x).

simple induction x; intros x1 x2.
red in |- *.
simple induction x0; intros y1 y2.
simple induction y; intros z1 z2.
unfold Z_rel, multZ_XX, multZ_XXX in |- *; simpl in |- *.
intro H.
apply (From_R_to_L Z_typ Z_rel).
red in |- *.
simpl in |- *.
ANa.
(*
  x : Z_typ
  x1 : nat
  x2 : nat
  x0 : Z_typ
  y1 : nat
  y2 : nat
  y : Z_typ
  z1 : nat
  z2 : nat
  H : y1 + z2=z1 + y2
  ============================
   x1*y1 + x2*y2 + x1*z2 + x2*z1=x1*z1 + x2*z2 + x1*y2 + x2*y1
*)
rewrite (plus_permute (x2 * y2)).
rewrite (plus_permute (x2 * z2)).
repeat rewrite <- NATURAL.mult_plus_distr_l.
rewrite (plus_comm y2).
rewrite <- H.
rewrite (plus_comm y1).
HSNa.
repeat rewrite <- NATURAL.mult_plus_distr_l.
elim H; auto with arith.
Qed.

Definition multZ_X (x : Z_typ) : Z -> Z :=
  lift Z_typ Z_rel Z (multZ_XX x) (Compat_multZ_XX x).

Lemma Compat_multZ_X : Compat Z_typ Z_rel (Z -> Z) multZ_X.

red in |- *.
simple induction x; intros x1 x2.
simple induction y; intros y1 y2.
unfold Z_rel in |- *; simpl in |- *.
intro H.
apply Ext.
intro z.
pattern z in |- *.
apply (Closure_prop Z_typ Z_rel z).
simple induction x0; intros a1 a2.
unfold multZ_X in |- *.
repeat rewrite Reduce.
unfold multZ_XX in |- *.
apply (From_R_to_L Z_typ Z_rel).
unfold Z_rel, multZ_XXX in |- *; simpl in |- *.
ANa.
repeat rewrite (plus_permute (x1 * a1)).
repeat rewrite (plus_permute (y1 * a1)).
repeat rewrite <- mult_plus_distr_r.
elim H.
HSNa.
repeat rewrite <- mult_plus_distr_r.
rewrite plus_comm.
rewrite <- H.
rewrite plus_comm.
auto with arith.
Qed.

Definition multZ : Z -> Z -> Z :=
  lift Z_typ Z_rel (Z -> Z) multZ_X Compat_multZ_X.

End Integers.

Arguments Scope unary_minus [INT_scope].

Notation "- z" := (unary_minus z) : INT_scope.
Infix "+" := plusZ (at level 50, left associativity) : INT_scope.
Infix "*" := multZ (at level 40, left associativity) : INT_scope.

Notation "p .1" := (fst p) (at level 20) : INT_scope.
Notation "p .2" := (snd p) (at level 20) : INT_scope.

Delimit Scope INT_scope with INT.
