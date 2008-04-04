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
(*  leZ.v                                                                   *)
(*                                                                          *)
(*  Basic properties of ``less or equal'' on integers                       *)
(*                                                                          *)
(*                                                                          *)
(*  Samuel Boutin                                                           *)
(*  Coq V5.10                                                               *)
(*  June  1995                                                              *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                               leZ.v                                      *)
(****************************************************************************)


Require Import leZ.
Require Import int.
Require Import quotient.
Require Import Arith.


Section leZproperties.

Require Import nat.
Require Import integer_defs.


Close Scope nat_scope.
Open Scope INT_scope.

Lemma Z_partition : forall z : Z, z <= - 1 \/ z = 0 \/ 1 <= z.

intro.
unfold unary_minus in |- *; simpl in |- *.
unfold swap in |- *; simpl in |- *.
rewrite Reduce; simpl in |- *.
apply (Closure_prop Z_typ Z_rel z).
simple induction x.
intros y y0.
elim (le_or_lt y y0); intro.
elim (le_lt_or_eq y y0 H); intro.
left.
red in |- *.
simpl in |- *.
unfold leZ_X in |- *; unfold leZ_XX in |- *.
repeat rewrite (Reduce_prop Z_typ Z_rel).
simpl in |- *.
elim plus_comm; simpl in |- *.
exact (lt_le_S y y0 H0).
right. left.
elim H0.
apply (From_R_to_L Z_typ Z_rel).
red in |- *; simpl in |- *.
elim plus_comm; simpl in |- *; auto with arith.
right. right.
red in |- *.
simpl in |- *.
unfold leZ_X in |- *; unfold leZ_XX in |- *.
repeat rewrite (Reduce_prop Z_typ Z_rel).
simpl in |- *.
elim plus_comm; simpl in |- *.
exact (lt_le_S y0 y H).
Qed.


Require Import Compare_dec.

Lemma Constructive_Z_partition :
 forall z : Z, {z <= - 1} + {z = 0} + {1 <= z}.

intro.
unfold unary_minus in |- *; simpl in |- *.
unfold swap in |- *; simpl in |- *.
rewrite Reduce; simpl in |- *.
apply (Closure Z_typ Z_rel z).
simple induction x.
intros y y0.
elim (le_lt_dec y y0); intro y1.
elim (le_lt_eq_dec y y0 y1); intro y2.
left.
left.
red in |- *.
simpl in |- *.
unfold leZ_X in |- *; unfold leZ_XX in |- *.
repeat rewrite (Reduce_prop Z_typ Z_rel).
simpl in |- *.
elim plus_comm; simpl in |- *.
exact (lt_le_S y y0 y2).
left. right.
elim y2.
apply (From_R_to_L Z_typ Z_rel).
red in |- *; simpl in |- *.
elim plus_comm; simpl in |- *; auto with arith.
right.
red in |- *.
simpl in |- *.
unfold leZ_X in |- *; unfold leZ_XX in |- *.
repeat rewrite (Reduce_prop Z_typ Z_rel).
simpl in |- *.
elim plus_comm; simpl in |- *.
exact (lt_le_S y0 y y1).
Qed.

Lemma S1 : forall z : Z, z <= - 1 /\ z = 0 -> False.

unfold unary_minus in |- *; simpl in |- *.
unfold swap in |- *; simpl in |- *.
rewrite Reduce; simpl in |- *.
simpl in |- *; intro.
apply (Closure_prop Z_typ Z_rel z).
simple induction x.
intros y y0 H.
elim H.
unfold leZ in |- *.
rewrite (Reduce_prop Z_typ Z_rel).
unfold leZ_X in |- *; unfold leZ_XX in |- *.
repeat rewrite (Reduce_prop Z_typ Z_rel).
simpl in |- *.
intros.
cut (Z_rel (y, y0) (0%nat, 0%nat)).
unfold Z_rel in |- *; simpl in |- *.
elim plus_comm; simpl in |- *.
intro.
cut (y + 1 <= y0)%nat.
elim plus_comm.
simpl in |- *.
elim H2.
intro.
elim (le_Sn_n y).
auto with arith.
auto with arith.
exact (From_L_to_R Z_typ Z_rel (y, y0) (0%nat, 0%nat) H1).
Qed.



Lemma S2 : forall z : Z, z = 0 /\ 1 <= z -> False.

unfold unary_minus in |- *; simpl in |- *.
unfold swap in |- *; simpl in |- *.
simpl in |- *; intro.
apply (Closure_prop Z_typ Z_rel z).
simple induction x.
intros y y0 H.
elim H.
unfold leZ in |- *.
rewrite (Reduce_prop Z_typ Z_rel).
unfold leZ_X in |- *; unfold leZ_XX in |- *.
repeat rewrite (Reduce_prop Z_typ Z_rel).
simpl in |- *.
intros.
cut (Z_rel (y, y0) (0%nat, 0%nat)).
unfold Z_rel in |- *; simpl in |- *.
elim plus_comm; simpl in |- *.
intro.
cut (1 + y0 <= y + 0)%nat.
elim (plus_comm 0).
simpl in |- *.
elim H2.
intro.
elim (le_Sn_n y).
auto with arith.
auto with arith.
exact (From_L_to_R Z_typ Z_rel (y, y0) (0%nat, 0%nat) H0).
Qed.

Open Scope nat_scope.

Lemma le_false : forall y y0 : nat, 1 + y0 <= y -> 1 + y <= y0 -> False.

intros.
cut (y <= 1 + y).
intro.
generalize (le_trans _ _ _ H H1).
intro.
generalize (le_trans _ _ _ H2 H0).
simpl in |- *; intro.
elim (le_Sn_n y0 H3).
simpl in |- *.
apply le_n_Sn.
Qed.


Lemma S3 : forall z : Z, (z <= - 1)%INT /\ (1 <= z)%INT -> False.

unfold unary_minus in |- *; simpl in |- *.
unfold swap in |- *; simpl in |- *.
rewrite Reduce.
simpl in |- *; intro.
apply (Closure_prop Z_typ Z_rel z).
simple induction x.
intros y y0 H.
elim H.
unfold leZ in |- *.
rewrite (Reduce_prop Z_typ Z_rel).
unfold leZ_X in |- *; unfold leZ_XX in |- *.
repeat rewrite (Reduce_prop Z_typ Z_rel).
simpl in |- *.
intros.
generalize H0.
elim plus_comm; simpl in |- *.
intro.
generalize H1.
elim plus_comm; simpl in |- *.
intro.
apply (le_false y y0); auto with arith.
Qed.


Inductive EXP (A : Prop) (P : A -> Prop) : Prop :=
    EXP_intro : forall x : A, P x -> EXP A P.


Lemma z_lt_O :
 forall z : Z,
 (fun z : Z => (z <= - 1)%INT) z ->
 EXP ((fun z : Z => (z <= - 1)%INT) z)
   (fun h : (fun z : Z => (z <= - 1)%INT) z =>
    Constructive_Z_partition z =
    inleft ((fun z : Z => (1 <= z)%INT) z)
      (left _ h)).

intros.
elim (Constructive_Z_partition z).
simple induction a; intros.
exists a0.
auto with arith.
elim (S1 z).
split; auto with arith.
intros.
elim (S3 z).
split; auto with arith.
Qed.


Lemma z_eq_O :
 forall z : Z,
 (fun z : Z => z = (0)%INT) z ->
 EXP ((fun z : Z => z = (0)%INT) z)
   (fun h : (fun z : Z => z = (0)%INT) z =>
    Constructive_Z_partition z =
    inleft ((fun z : Z => (1 <= z)%INT) z)
      (right _ h)).

simpl in |- *.
intros.
elim (Constructive_Z_partition z).
simple induction a; intros.
elim (S1 z). split; auto with arith.
exists b.
auto with arith.
intros.
elim (S2 z).
split; auto with arith.
Qed.

Lemma O_lt_z :
 forall z : Z,
 (1 <= z)%INT ->
 EXP (1 <= z)%INT
   (fun h : (1 <= z)%INT =>
    Constructive_Z_partition z =
    inright ({(z <= - 1)%INT} + {(z = 0%INT)}) h).

simpl in |- *.
intros.
elim (Constructive_Z_partition z).
simple induction a; intros.
elim (S3 z). split; auto with arith.
elim (S2 z).
split; auto with arith.
intro.
exists b.
unfold unary_minus in |- *; simpl in |- *.
unfold swap in |- *; simpl in |- *.
rewrite Reduce; simpl in |- *.
auto with arith.
Qed.

End leZproperties.
