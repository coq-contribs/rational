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
(*  Definition of ``less or equal'' on integers                             *)
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


Require Import nat.
Require Import quotient.
Require Import integer_defs.


Section LEZ.
 
Open Scope nat_scope.

Definition leZ_XX (y x : Z_typ) : Prop := x .1 + y .2 <= y .1 + x .2.

Require Import Le.

Lemma le_with_plus1 : forall p n m : nat, n <= m -> p + n <= p + m.
auto with arith.
Qed.

Lemma le_with_plus2 : forall p n m : nat, p + n <= p + m -> n <= m.
exact (fun p n m : nat => plus_le_reg_l n m p).
Qed.

Lemma tech1 :
 forall a1 a2 b1 b2 c1 c2 : nat,
 a1 + b2 = a2 + b1 -> c1 + a2 <= c2 + a1 -> c1 + b2 <= c2 + b1.

intros.
apply (le_with_plus2 a1).
elim (plus_permute c1).
rewrite H.
repeat elim (plus_comm b1).
repeat elim (plus_permute b1).
apply (le_with_plus1 b1).
elim (plus_comm c2).
auto with arith.
Qed.


Lemma Compat_leZ_XX : forall x : Z_typ, Compat_prop Z_typ Z_rel (leZ_XX x).

simple induction x; intros c2 c1.
red in |- *.
simple induction x0; intros a2 a1.
simple induction y; intros b2 b1.
unfold leZ_XX in |- *; simpl in |- *.
unfold Z_rel in |- *; simpl in |- *.
elim (plus_comm a1).
elim (plus_comm c1).
split.
intro.
elim (plus_comm c1).
apply (tech1 a1 a2 b1 b2 c1 c2).
elim H; auto with arith.
auto with arith.
elim (plus_comm c1).
intro.
apply (tech1 b1 b2 a1 a2 c1 c2).
elim (plus_comm a1).
elim H.
elim (plus_comm a2).
auto with arith.
auto with arith.
Qed.

Definition leZ_X (z : Z) (x : Z_typ) : Prop :=
  lift_prop Z_typ Z_rel (leZ_XX x) (Compat_leZ_XX x) z.


Lemma Compat_leZ_X : forall z : Z, Compat_prop Z_typ Z_rel (leZ_X z).

red in |- *.
simple induction x; intros a1 a2.
simple induction y; intros b1 b2.
unfold Z_rel in |- *; simpl in |- *.
apply (Closure_prop Z_typ Z_rel z).
unfold leZ_X in |- *.
simple induction x0; intros c1 c2.
repeat rewrite (Reduce_prop Z_typ Z_rel).
unfold leZ_XX in |- *; simpl in |- *.
intro.
repeat elim (plus_comm c2).
split.
intro.
apply (tech1 a1 a2 b1 b2 c1 c2).
elim (plus_comm b1).
elim H.
auto with arith.
auto with arith.
intro.
apply (tech1 b1 b2 a1 a2 c1 c2).
elim H.
elim (plus_comm b2).
auto with arith.
auto with arith.
Qed.

Definition leZ (z : Z) : Z -> Prop :=
  lift_prop Z_typ Z_rel (leZ_X z) (Compat_leZ_X z).

Infix "<=" := leZ (at level 70, no associativity) : INT_scope.

Open Scope INT_scope.

Definition ltZ (z1 z2 : Z) : Prop := z1 <= z2 /\ z1 <> z2.

End LEZ.

(* Export Infix notations *)

Arguments Scope leZ [INT_scope INT_scope].
Arguments Scope ltZ [INT_scope INT_scope].

Infix "<=" := leZ (at level 70, no associativity) : INT_scope.
Infix "<" := ltZ (at level 70, no associativity) : INT_scope.
