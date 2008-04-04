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
(*  extensionality.v                                                        *)
(*                                                                          *)
(*  Functional extensionality can be deduced from the axioms on quotient    *)
(*  together with the xi-rule as shown in this file                         *)
(*                                                                          *)
(*                                                                          *)
(*  Samuel Boutin                                                           *)
(*  Coq V5.10                                                               *)
(*  June  1995                                                              *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                            extensionality.v                              *)
(****************************************************************************)



(*   WARNING:
If the axiom Reduce on quotients 
(Axiom Reduce : (A:Set)(R:A->A->Prop)(B:Set)(f:A->B) 
      (c:(Compat A R B f))(a:A)
     (lift A R B f c (In A R a)) = (f a).)
was defined for DEFINITIONAL IDENTITY and not LEIBNIZ IDENTITY
then eta rule is sufficient to derive extensionality from the
axioms for quotient as this is mention by Jacobs or Hofmann
in his thesis
*)


Require Import quotient.


Section Extensionality.

Variable A : Set.
Variable B : Set.

Definition U := A -> B.

Definition eq_ext (f g : U) := forall x : A, f x = g x.

Definition E := U / eq_ext.

Definition PX (x : A) (f : U) := f x.

(* We now prove that for x:A, (P x) induces a function from E to B *)

Lemma Compat_PX : forall x : A, Compat U eq_ext B (PX x).

intro.
unfold Compat in |- *.
unfold eq_ext in |- *.
unfold PX in |- *; simpl in |- *.
intros.
exact (H x).
Qed.

Definition P (x : A) := lift U eq_ext B (PX x) (Compat_PX x).

Definition Reform (f : E) (x : A) := P x f.

(* A formulation of (xi)-rule in case eta is given *)
Axiom xi : forall f g : U, (forall x : A, f x = g x) -> f = g.

Lemma Rf_is_f : forall f : U, Reform (In U eq_ext f) = f.

intros.
unfold Reform in |- *.
unfold P in |- *.
apply
 (xi (fun x : A => lift U eq_ext B (PX x) (Compat_PX x) (In U eq_ext f)) f).
(* Here if the axiom Reduce was defined for definitional identity,
eta reduction would be sufficient to conclude this lemma *)
intro.
rewrite Reduce.
unfold PX in |- *.
auto.
Qed.

Lemma extensionality : forall f g : A -> B, eq_ext f g -> f = g.

intros.
rewrite <- (Rf_is_f f).
rewrite <- (Rf_is_f g).
elim (From_R_to_L U eq_ext f g).
auto.
assumption.
Qed.

End Extensionality.
