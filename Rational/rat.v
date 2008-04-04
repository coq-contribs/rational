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
(*  rat.v                                                                   *)
(*                                                                          *)
(*  Summary of rational arithmetic                                          *)
(*                                                                          *)
(*                                                                          *)
(*  Samuel Boutin                                                           *)
(*  Coq V5.10                                                               *)
(*  June  1995                                                              *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                                rat.v                                     *)
(****************************************************************************)


Require Import quotient.
Require Import subset.
Require Import intnumbers.
Require Export rational_defs.
Require Export PlusQ.
Require Export MultQ.
Require Import AC.
Require Import HS.

Section rat.



(*******************************************************************
PROPERTIES OF Q
********************************************************************

plusQ_sym     : (n,m:Q)                       n + m = m + n
plusQ_assoc_l : (n,m,p:Q)              n + (m + p) = (n + m) + p
plusQ_permute : (n,m,p:Q)              n + (m + p) = m + (n + p)
plusQ_assoc_r : (n,m,p:Q)              (n + m) + p = n + (m + p)
plusQ_plus_l  : (n,m,p:Q)               n + m = n + p =>  m = p

multQ_sym         : (n,m:Q)                   n*m = m*n
multQ_assoc_l     : (n,m,p:Q)             n*(m*p) = (n*m)*p
multQ_permute     : (n,m,p:Q)             n*(m*p) = m*(n*p)
multQ_assoc_r     : (n,m,p:Q)             (n*m)*p = n*(m*p)

distribQ_l : (n,m,p:Q)           (n + m)*p = (n*p) + (m*p)
distribQ   : (n,m,p:Q)           p*(n + m) = (p*n) + (p*m).

*********************************************************************)

(* Tactiques de d'ecision AC pour l'addition sur Q.*)

Open Scope RAT_scope.

Lemma plusQ_simpl_l : forall n m p : Q, m = p -> n + m = n + p.
intros. elim H. auto. Qed.

Lemma multQ_simpl_l : forall n m p : Q, m = p -> n * m = n * p.
intros. elim H. auto. Qed.

End rat.

Ltac CQa := intros; ac_of eq plusQ plusQ_sym plusQ_permute; auto.

Ltac AQa := intros; repeat elim plusQ_assoc_l.

Ltac ACQa :=
  intros; repeat elim plusQ_assoc_l; ac_of eq plusQ plusQ_sym plusQ_permute;
   auto.

Ltac HSQa := intros; hs_of eq plusQ plusQ_sym plusQ_permute plusQ_simpl_l.

(* Tactiques de d'ecision AC pour la multiplication sur Z.*)

Ltac CQm := intros; ac_of eq multQ multQ_sym multQ_permute; auto.

Ltac AQm := intros; repeat elim multQ_assoc_l.

Ltac ACQm :=
  intros; repeat elim multQ_assoc_l; ac_of eq multQ multQ_sym multQ_permute;
   auto.

Ltac HSQm := intros; hs_of eq multQ multQ_sym multQ_permute multQ_simpl_l.