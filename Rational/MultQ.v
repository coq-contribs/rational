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
(*  MultQ.v                                                                 *)
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
(*                               MultQ.v                                    *)
(****************************************************************************)


Require Import AC.
Require Import HS.
Require Import quotient.
Require Import subset.
Require Import intnumbers.
Require Import rational_defs.
Require Import PlusQ.


Section MultQ.

Open Scope RAT_scope.

Lemma multQ_sym : forall n m : Q, n * m = m * n.

intro n; pattern n in |- *; apply (Closure_prop Q_typ Q_rel n).
intro x.
intro m; pattern m in |- *; apply (Closure_prop Q_typ Q_rel m).
intro y.
unfold multQ in |- *.
rewrite (Reduce Q_typ Q_rel (Q -> Q) multQ_X Compat_multQ_X x).
rewrite (Reduce Q_typ Q_rel (Q -> Q) multQ_X Compat_multQ_X y).
unfold multQ_X in |- *; simpl in |- *.
repeat rewrite Reduce.
unfold multQ_XX in |- *.
unfold multQ_XXX in |- *.
apply (From_R_to_L Q_typ Q_rel).
red in |- *; simpl in |- *.
repeat rewrite Out_In.
ACZm.
Qed.


Lemma multQ_assoc_l : forall n m p : Q, n * (m * p) = n * m * p.

intro n; pattern n in |- *; apply (Closure_prop Q_typ Q_rel n).
intro x.
intro m; pattern m in |- *; apply (Closure_prop Q_typ Q_rel m).
intro y.
intro p; pattern p in |- *; apply (Closure_prop Q_typ Q_rel p).
intro z.
unfold multQ in |- *.
rewrite (Reduce Q_typ Q_rel (Q -> Q) multQ_X Compat_multQ_X x).
rewrite (Reduce Q_typ Q_rel (Q -> Q) multQ_X Compat_multQ_X y).
unfold multQ_X in |- *; simpl in |- *.
repeat rewrite (Reduce Q_typ Q_rel Q).
unfold multQ_XX in |- *.
repeat rewrite (Reduce Q_typ Q_rel Q).
rewrite
 (Reduce Q_typ Q_rel (Q -> Q)
    (fun x0 : Q_typ =>
     lift Q_typ Q_rel Q (fun y0 : Q_typ => |(multQ_XXX x0 y0) |q)
       (Compat_multQ_XX x0)) Compat_multQ_X (multQ_XXX x y))
 .
repeat rewrite (Reduce Q_typ Q_rel Q).
unfold multQ_XXX in |- *.
apply (From_R_to_L Q_typ Q_rel).
red in |- *; simpl in |- *.
repeat rewrite Out_In.
ACZm.
Qed.


Lemma multQ_permute : forall n m p : Q, n * (m * p) = m * (n * p).

intro n; pattern n in |- *; apply (Closure_prop Q_typ Q_rel n).
intro x.
intro m; pattern m in |- *; apply (Closure_prop Q_typ Q_rel m).
intro y.
intro p; pattern p in |- *; apply (Closure_prop Q_typ Q_rel p).
intro z.
unfold multQ in |- *.
rewrite (Reduce Q_typ Q_rel (Q -> Q) multQ_X Compat_multQ_X x).
rewrite (Reduce Q_typ Q_rel (Q -> Q) multQ_X Compat_multQ_X y).
unfold multQ_X in |- *; simpl in |- *.
repeat rewrite (Reduce Q_typ Q_rel Q).
unfold multQ_XX in |- *.
repeat rewrite (Reduce Q_typ Q_rel Q).
unfold multQ_XXX in |- *.
apply (From_R_to_L Q_typ Q_rel).
red in |- *; simpl in |- *.
repeat rewrite Out_In.
ACZm.
Qed.


Lemma multQ_assoc_r : forall n m p : Q, n * m * p = n * (m * p).

intros.
elim multQ_sym.
elim (multQ_sym (n * m)).
elim (multQ_assoc_l n m p).
auto.
Qed.

Lemma distribQ : forall n m p : Q, n * (m + p) = n * m + n * p.

intro n; pattern n in |- *; apply (Closure_prop Q_typ Q_rel n).
intro x.
intro m; pattern m in |- *; apply (Closure_prop Q_typ Q_rel m).
intro y.
intro p; pattern p in |- *; apply (Closure_prop Q_typ Q_rel p).
intro z.
unfold multQ in |- *.
rewrite (Reduce Q_typ Q_rel (Q -> Q) multQ_X Compat_multQ_X x).
unfold multQ_X in |- *.
repeat rewrite Reduce.
unfold multQ_XX in |- *.
repeat rewrite Reduce.
unfold multQ_XXX in |- *; simpl in |- *.
unfold plusQ in |- *.
rewrite (Reduce Q_typ Q_rel (Q -> Q) plusQ_X Compat_plusQ_X y).
rewrite
 (Reduce Q_typ Q_rel (Q -> Q) plusQ_X Compat_plusQ_X
    ((x .1 * y .1)%INT, %+ ((x .2 * y .2)%INT) (plusQ_XXX_prelim x y)))
 .
unfold plusQ_X in |- *.
repeat rewrite Reduce.
unfold plusQ_XX in |- *.
repeat rewrite Reduce.
unfold plusQ_XXX in |- *; simpl in |- *.
apply (From_R_to_L Q_typ Q_rel).
red in |- *; simpl in |- *.
repeat rewrite Out_In.
AZm.
repeat rewrite distribZ_l.
repeat rewrite distribZ.
AZm.
rewrite (multZ_permute (z .2) (x .2)).
rewrite (multZ_permute (y .2) (x .2)).
HSZa.
ACZm.
Qed.



Lemma distribQ_l : forall n m p : Q, (m + p) * n = m * n + p * n.

intros.
repeat elim (multQ_sym n).
apply distribQ.
Qed.



End MultQ.
