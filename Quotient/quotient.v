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
(*  quotient.v                                                              *)
(*                                                                          *)
(*  Definition of basic tools to build quotient types                       *)
(*  Our proposal is equivalent to what is used in Lego or Nuprl             *)
(*  but also to what Barthes, Hofmann, Jacobs, Hermida use in different     *)
(*  recent papers                                                           *)
(*                                                                          *)
(*                                                                          *)
(*  Samuel Boutin                                                           *)
(*  Coq V5.10                                                               *)
(*  June  1995                                                              *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                              quotient.v                                  *)
(****************************************************************************)




(* The following parameter is the constructor of quotient types *)

Parameter MK_QUO : forall (A : Set) (R : A -> A -> Prop), Set.

(* Compat explains the compatibility of a function f:A->B  w.r.t
the relation R:A->A->Prop *)

Definition Compat (A : Set) (R : A -> A -> Prop) (B : Set) 
  (f : A -> B) := forall x y : A, R x y -> f x = f y.

(* the same for a predicate *)

Definition Compat_prop (A : Set) (R : A -> A -> Prop) 
  (P : A -> Prop) := forall x y : A, R x y -> (P x <-> P y).

(* If f is a a compatible function from A to B, then
(lift ....f) is the corresponding function on A/R  *)

Axiom
  lift :
    forall (A : Set) (R : A -> A -> Prop) (B : Set) (f : A -> B),
    Compat A R B f -> MK_QUO A R -> B.

(* The same for a predicate *)
Axiom
  lift_prop :
    forall (A : Set) (R : A -> A -> Prop) (P : A -> Prop),
    Compat_prop A R P -> MK_QUO A R -> Prop.


(****************************************************************************
WE CAN AVOID THE FOLLOWING DEFINITIONS:

Definition Compat_Prop := [A:Set][R:A->A->Prop][B:Type][P:A->B]
                    (x,y:A)(R x y) -> (P x) <-> (P y).

Axiom lift_Prop :  (A:Set)(R:A->A->Prop)(B:Type)(P:A->B)
                  (Compat_prop A R B P) -> (MK_QUO A R) -> Prop.
******************************************************************************)


(* (In ... x) is the congruence class of x w.r.t R *)
Parameter In : forall (A : Set) (R : A -> A -> Prop), A -> MK_QUO A R.

(* two equivalence classes are leibniz equal iff their
representant are R-related *)

Axiom
  From_R_to_L :
    forall (A : Set) (R : A -> A -> Prop) (x y : A),
    R x y -> In A R x = In A R y.

(* The converse should also be true when R is ``effective'' *)
Axiom
  From_L_to_R :
    forall (A : Set) (R : A -> A -> Prop) (x y : A),
    In A R x = In A R y -> R x y.

(* The following axiom summarizes in the formula:
----------------------------------
     (lift ...f)(in..x) = (f x)
---------------------------------
 This is a reduction in the impredicative axiomatisation of
quotient types or in the setoid model.
But here we just have this for leibniz identity.
(not for definitional identity) *)

Axiom
  Reduce :
    forall (A : Set) (R : A -> A -> Prop) (B : Set) 
      (f : A -> B) (c : Compat A R B f) (a : A),
    lift A R B f c (In A R a) = f a. 

Axiom
  Reduce_prop :
    forall (A : Set) (R : A -> A -> Prop) (f : A -> Prop)
      (c : Compat_prop A R f) (a : A), lift_prop A R f c (In A R a) = f a. 


(* To prove something on a quotient, it is enough to prove it
on equivalence classes: Do not forget the paradigm quotient <-> type
so that it is not obvious that all the object of type A/R are 
equivalence classes. So we need the following axiom *)

Axiom
  Closure :
    forall (A : Set) (R : A -> A -> Prop) (X : MK_QUO A R)
      (P : MK_QUO A R -> Set), (forall x : A, P (In A R x)) -> P X.

(* the same for predicates*)

Axiom
  Closure_prop :
    forall (A : Set) (R : A -> A -> Prop) (X : MK_QUO A R)
      (P : MK_QUO A R -> Prop), (forall x : A, P (In A R x)) -> P X.

(* We set functionnal identity but it is not necessary to implement
real numbers with Coq *)

Axiom
  Ext : forall (A B : Set) (f g : A -> B), (forall x : A, f x = g x) -> f = g.

(* It is proved in the file extensionality.v that functional extensionality
can be derived from the previous set of axioms and the axiom xi *)


(* Syntax for quotients *)
 
Notation "| c |" := (In _ _ c) (at level 20, c at level 0).
Notation "c / c2" := (MK_QUO c c2) : type_scope.
