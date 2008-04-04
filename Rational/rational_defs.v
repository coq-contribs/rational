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
(*  rational_defs.v                                                              *)
(*                                                                          *)
(*  In this we define rational numbers using quotient types and             *)
(*  subset types. We alos define addition and multiplication on             *)
(*  rational numbers                                                        *)
(*                                                                          *)
(*                                                                          *)
(*  Samuel Boutin                                                           *)
(*  Coq V5.10                                                               *)
(*  June  1995                                                              *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                             rational_defs.v                                   *)
(****************************************************************************)


Require Import quotient.
Require Import subset.
Require Import HS.
Require Import AC.

Require Import intnumbers.
Require Import productSyntax.

(* Overwrite the syntax of p.1 and p.2 *)

Open Scope INT_scope.

Definition Pos (z : Z) : Prop := 1 <= z.

Notation "%+  c1 c2" := (In_subset Z Pos c1 c2)
  (at level 20, c1, c2 at level 0).
Notation "%-  c" := (Out_subset Z Pos c)
  (at level 20, right associativity, c at level 0).

Notation "p .2" := (%- (p ^2)) (at level 20) : INT_scope.
Notation "p .1" := (fst p) (at level 20) : INT_scope.

Definition Q_typ := (Z * Z ! Pos)%type.

Definition Q_rel (x y : Q_typ) := x .1 * y .2 = y .1 * x .2.

Definition Q := Q_typ / Q_rel.

Notation "| c | 'q'" := (In Q_typ Q_rel c) (at level 20, c at level 0).

(*****************************************************************************
 plusQ : Q -> Q -> Q
*****************************************************************************)
Section Rationals.

Axiom plusQ_XXX_prelim : forall x y : Q_typ, 1 <= x .2 * y .2.

Definition plusQ_XXX (x y : Q_typ) :=
  (x .1 * y .2 + y .1 * x .2, %+ (x .2 * y .2) (plusQ_XXX_prelim x y)).

Definition plusQ_XX (x y : Q_typ) : Q := |(plusQ_XXX x y) |q.

Lemma Compat_plusQ_XX : forall x : Q_typ, Compat Q_typ Q_rel Q (plusQ_XX x).

red in |- *.
unfold Q_rel in |- *.
unfold plusQ_XX in |- *.
unfold plusQ_XXX in |- *.
intros x x0 y H.
apply (From_R_to_L Q_typ Q_rel).
red in |- *; simpl in |- *.
rewrite Out_In.
rewrite Out_In.
repeat rewrite distribZ_l.
AZm.
elim (multZ_sym (y .2)).
repeat elim (multZ_permute (y .2)).
repeat elim (multZ_permute (x0 .1)).
rewrite (multZ_assoc_l (x0 .1)).
rewrite H.
AZm.
elim (multZ_sym (x0 .2)).
repeat elim (multZ_permute (x0 .2)).
HSZa.
auto.
Qed.


Definition plusQ_X (x : Q_typ) : Q -> Q :=
  lift Q_typ Q_rel Q (plusQ_XX x) (Compat_plusQ_XX x).

Lemma Compat_plusQ_X : Compat Q_typ Q_rel (Q -> Q) plusQ_X.

red in |- *.
unfold Q_rel in |- *.
intros x1 y0 H0.
apply Ext.
unfold plusQ_X in |- *.
intro q.
pattern q in |- *.
apply (Closure_prop Q_typ Q_rel q).
intro.
repeat rewrite Reduce.
unfold plusQ_XX in |- *; simpl in |- *.
unfold plusQ_XXX in |- *.
apply (From_R_to_L Q_typ Q_rel).
red in |- *; simpl in |- *.
repeat rewrite Out_In.
repeat rewrite distribZ_l.
AZm.
repeat elim (multZ_permute (y0 .2)).
repeat elim (multZ_permute (x1 .1)).
rewrite (multZ_assoc_l (x1 .1)).
rewrite H0.
AZm.
elim (multZ_permute (x1 .2)).
HSZa.
repeat elim (multZ_permute (y0 .1)).
AZm.
repeat elim (multZ_permute (x1 .2)).
auto.
Qed.

Definition plusQ : Q -> Q -> Q :=
  lift Q_typ Q_rel (Q -> Q) plusQ_X Compat_plusQ_X.



(*****************************************************************************
 multQ : Q -> Q -> Q
*****************************************************************************)

Definition multQ_XXX (x y : Q_typ) :=
  (x .1 * y .1, %+ (x .2 * y .2) (plusQ_XXX_prelim x y)).

Definition multQ_XX (x y : Q_typ) : Q := |(multQ_XXX x y) |q.

Lemma Compat_multQ_XX : forall x : Q_typ, Compat Q_typ Q_rel Q (multQ_XX x).

red in |- *.
unfold Q_rel in |- *.
unfold multQ_XX in |- *.
unfold multQ_XXX in |- *.
intros x x2 y0 H0.
apply (From_R_to_L Q_typ Q_rel).
red in |- *; simpl in |- *.
repeat rewrite Out_In.
AZm.
elim (multZ_sym (y0 .2)).
repeat elim (multZ_permute (y0 .2)).
repeat elim (multZ_permute (x2 .1)).
rewrite (multZ_assoc_l (x2 .1)).
rewrite H0.
ACZm.
Qed.


Definition multQ_X (x : Q_typ) : Q -> Q :=
  lift Q_typ Q_rel Q (multQ_XX x) (Compat_multQ_XX x).

Lemma Compat_multQ_X : Compat Q_typ Q_rel (Q -> Q) multQ_X.

red in |- *.
unfold Q_rel in |- *.
intros x1 y0 H0.
apply Ext.
unfold multQ_X in |- *.
intro q.
pattern q in |- *.
apply (Closure_prop Q_typ Q_rel q).
intro.
repeat rewrite Reduce.
unfold multQ_XX in |- *; simpl in |- *.
unfold multQ_XXX in |- *.
apply (From_R_to_L Q_typ Q_rel).
red in |- *; simpl in |- *.
repeat rewrite Out_In.
AZm.
elim (multZ_permute (y0 .2)).
rewrite (multZ_assoc_l (x1 .1)).
rewrite H0.
ACZm.
Qed.


Definition multQ : Q -> Q -> Q :=
  lift Q_typ Q_rel (Q -> Q) multQ_X Compat_multQ_X.



End Rationals.

Infix "+" := plusQ (at level 50, left associativity) : RAT_scope.
Infix "*" := multQ (at level 40, left associativity) : RAT_scope.