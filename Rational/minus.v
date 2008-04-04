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
(*  minus.v                                                                 *)
(*                                                                          *)
(*  Unary and binaru minus operator on rational numbers                     *)
(*                                                                          *)
(*                                                                          *)
(*  Samuel Boutin                                                           *)
(*  Coq V5.10                                                               *)
(*  June  1995                                                              *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                              minus.v                                     *)
(****************************************************************************)


Require Import AC.
Require Import HS.
Require Import quotient.
Require Import subset.
Require Import intnumbers.
Require Import rational_defs.

Require Import productSyntax.

Section minus.

Open Scope INT_scope.

(*
(* TODO axiome `a supprimer  *)

Axiom sign_simpl : (x,y:Z) (x = y) -> -x = -y.
Axiom mult_minus : (x,y:Z) (-x) * y = - (x * y).
*)

Definition unary_minusQ_XX (x : Q_typ) := (- x .1, x ^2).


Definition unary_minusQ_X (x : Q_typ) : Q := |(unary_minusQ_XX x) |q.

Lemma Compat_unary_minusQ_X : Compat Q_typ Q_rel Q unary_minusQ_X.

red in |- *.
unfold Q_rel in |- *.
unfold unary_minusQ_X in |- *.
unfold unary_minusQ_XX in |- *.
intros.
apply (From_R_to_L Q_typ Q_rel).
red in |- *; simpl in |- *.
repeat rewrite mult_minus.
apply sign_simpl; auto.
Qed.


Definition unary_minusQ : Q -> Q :=
  lift Q_typ Q_rel Q unary_minusQ_X Compat_unary_minusQ_X.

End minus.

Notation "- x" := (unary_minusQ x) : RAT_scope.

Section binary_minus. 

Require Import PlusQ.

Open Scope RAT_scope.

Definition binary_minusQ (x y : Q) : Q := x + - y.

End binary_minus.