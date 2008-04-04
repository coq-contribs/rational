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
(* Revised December 2002 *)

(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(*  Z_to_Q.v                                                                *)
(*                                                                          *)
(*  Details of the coercion between integers and rationals                  *)
(*                                                                          *)
(*                                                                          *)
(*  Samuel Boutin                                                           *)
(*  Coq V5.10                                                               *)
(*  June  1995                                                              *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                              Z_to_Q.v                                    *)
(****************************************************************************)

Require Import quotient.
Require Import subset.
Require Import HS.
Require Import AC.
Require Import intnumbers.
Require Import rational_defs.

Section Integers_are_Rationals.

Require Import productSyntax.

Open Scope INT_scope.

Lemma one_is_a_denominator : 1 <= 1.

red in |- *; simpl in |- *.
rewrite (Reduce_prop Z_typ Z_rel).
red in |- *; simpl in |- *.
rewrite (Reduce_prop Z_typ Z_rel).
red in |- *; simpl in |- *.
apply le_n; auto.
Qed.

Definition fromZ_to_Q (x : Z) : Q := |(x, %+ (1) one_is_a_denominator) |q.


End Integers_are_Rationals.
(*
Grammar rational final :=
[ "{" integer:expr($c) "}" ] -> [<<(fromZ_to_Q $c)>>].
*)
