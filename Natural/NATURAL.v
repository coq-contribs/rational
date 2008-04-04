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
(*  NATURAL  .v                                                             *)
(*                                                                          *)
(* Defines (infix)  syntax for operations on nat                            *)
(* Defines tactics for addition and multiplication                          *)
(* Defines some additional properties for addition and multiplication       *)
(*                                                                          *)
(*                                                                          *)
(*                                                                          *)
(*  Samuel Boutin                                                           *)
(*  Coq V5.10                                                               *)
(*  June  1995                                                              *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                              NATURAL.v                                   *)
(****************************************************************************)


Require Export Arith.
Require Export Plus.
Require Export Mult.
Require Import AC.
Require Import HS.

Open Scope nat_scope.

Notation "p .1" := (fst p) (at level 20) : nat_scope.
Notation "p .2" := (snd p) (at level 20) : nat_scope.

(* Redefine explicitly 0 and 1 that are later redefine also in INT_scope *)

Notation "0" := 0 (at level 11) : nat_scope.
Notation "1" := 1 (at level 11) : nat_scope.

(* space around eq *)

Notation "t1  =  t2" := (t1 = t2) (at level 70). 

Section NAT.

(*************************************************************
PROPERTIES OF nat
*************************************************************

eq_S         : (n,m:nat)                   n=m->(S n)=(S m)
pred_Sn      : (m:nat)                              m=(pred (S m))

plus_sym     : (n,m:nat)                       n + m = m + n
plus_assoc_l : (n,m,p:nat)               n + (m + p) = (n + m) + p
plus_permute : (n,m,p:nat)               n + (m + p) = m + (n + p)
plus_assoc_r : (n,m,p:nat)               (n + m) + p = n + (m + p)
plus_n_O     : (n:nat)                             n = n + O
plus_n_Sm    : (n,m:nat)                   (S n + m) = n + (S m)
simpl_plus_l : (n,m,p:nat)       n + m = n + p =>  m = p

mult_sym         : (n,m:nat)                   n * m = m * n
mult_assoc_l     : (n,m,p:nat)           n * (m * p) = (n * m) * p
mult_permute     : (n,m,p:nat)           n * (m * p) = m * (n * p)
mult_assoc_r     : (n,m,p:nat)           (n * m) * p = n * (m * p)
mult_n_O         : (n:nat)                         O = n * O
mult_n_Sm        : (n,m:nat)             (n * m) + n = n * (S m)

mult_plus_distr   : (n,m,p:nat)           (n + m) * p = (n * p) + (m * p)
mult_plus_distr_l : (n,m,p:nat)           p * (n + m) = (p * n) + (p * m).
mult_minus_distr : (n,m,p:nat)           (n - m) * p = (n * p) - (m * p)

minus_n_O        : (n:nat)                         n = n - O
minus_n_n        : (n:nat)                         O = n - n

minus_plus_simpl : (n,m,p:nat)                 n - m = (p + n) - (p + m)
plus_minus       : (n,m,p:nat)        n = m + p => p = n - m

*************************************************************)

(* Decision AC for addition and multiplication on N*)

Lemma plus_simpl_l : forall n m p : nat, m = p -> n + m = n + p.
intros.
elim H; auto.
Qed.

Lemma mult_simpl_l : forall n m p : nat, m = p -> n * m = n * p.
intros.
elim H; auto.
Qed.

Lemma mult_permute : forall n m p : nat, n * (m * p) = m * (n * p).
intros.
elim (mult_comm p n).
elim (mult_assoc_reverse m p n).
elim (mult_comm n).
auto.
Qed.

Lemma mult_plus_distr_l : forall n m p : nat, p * (n + m) = p * n + p * m.
intros.
rewrite (mult_comm p).
rewrite (mult_plus_distr_r n m p).
repeat elim (mult_comm p); auto.
Qed.

End NAT.

Ltac CNa := intros; ac_of eq plus plus_comm plus_permute; auto.

Ltac ANa := intros; repeat elim plus_assoc.

Ltac ACNa :=
  intros; repeat elim plus_assoc; ac_of eq plus plus_comm plus_permute; auto.

Ltac HSNa := intros; hs_of eq plus plus_comm plus_permute plus_simpl_l.

Ltac CNm := intros; ac_of eq mult mult_comm mult_permute; auto.

Ltac ANm := intros; repeat elim mult_assoc.

Ltac ACNm :=
  intros; repeat elim mult_assoc; ac_of eq mult mult_comm mult_permute; auto.

Ltac HSNm := intros; hs_of eq mult mult_comm mult_permute mult_simpl_l.