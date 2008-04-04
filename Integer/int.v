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
(*  int.v                                                                   *)
(*                                                                          *)
(*  Summary of basic arihmetic on integers                                  *)
(*                                                                          *)
(*                                                                          *)
(*  Samuel Boutin                                                           *)
(*  Coq V5.10                                                               *)
(*  June  1995                                                              *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                               int.v                                      *)
(****************************************************************************)


Require Import quotient.
Require Export integer_defs.
Require Export PlusZ.
Require Export MultZ.
Require Import AC.
Require Import HS.


Section INT.

(*******************************************************************
PROPERTIES OF Z
********************************************************************


plusZ_sym     : (n,m:Z)                       n + m = m + n
plusZ_assoc_l : (n,m,p:Z)              n + (m + p) = (n + m) + p
plusZ_permute : (n,m,p:Z)              n + (m + p) = m + (n + p)
plusZ_assoc_r : (n,m,p:Z)              (n + m) + p = n + (m + p)
plusZ_plus_l  : (n,m,p:Z)               n + m = n + p =>  m = p
plusZ_O       : (n:Z)                        n + 0 = n      

multZ_sym         : (n,m:Z)                   n*m = m*n
multZ_assoc_l     : (n,m,p:Z)             n*(m*p) = (n*m)*p
multZ_permute     : (n,m,p:Z)             n*(m*p) = m*(n*p)
multZ_assoc_r     : (n,m,p:Z)             (n*m)*p = n*(m*p)
multZ_O           : (n:Z)                    n*0 = 0

distribZ_l : (n,m,p:Z)           (n + m)*p = (n*p) + (m*p)
distribZ   : (n,m,p:Z)           p*(n + m) = (p*n) + (p*m).

*********************************************************************)

Open Scope INT_scope.

(* Tactiques de d'ecision AC pour l'addition sur Z.*)

Axiom plusZ_simpl_l : forall n m p : Z, m = p -> n + m = n + p.

Axiom multZ_simpl_l : forall n m p : Z, m = p -> n * m = n * p.

End INT.

Ltac CZa := intros; ac_of eq plusZ plusZ_sym plusZ_permute; auto.

Ltac AZa := intros; repeat elim plusZ_assoc_l.

Ltac ACZa :=
  intros; repeat elim plusZ_assoc_l; ac_of eq plusZ plusZ_sym plusZ_permute;
   auto.

Ltac HSZa := intros; hs_of eq plusZ plusZ_sym plusZ_permute plusZ_simpl_l.

(* Tactiques de d'ecision AC pour la multiplication sur Z.*)

Ltac CZm := intros; ac_of eq multZ multZ_sym multZ_permute; auto.

Ltac AZm := intros; repeat elim multZ_assoc_l.

Ltac ACZm :=
  intros; repeat elim multZ_assoc_l; ac_of eq multZ multZ_sym multZ_permute;
   auto.

Ltac HSZm := intros; hs_of eq multZ multZ_sym multZ_permute multZ_simpl_l.