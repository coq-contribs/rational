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
(*  subset.v                                                                *)
(*                                                                          *)
(*  Definition of subsets as types                                          *)
(*                                                                          *)
(*                                                                          *)
(*  Samuel Boutin                                                           *)
(*  Coq V5.10                                                               *)
(*  June  1995                                                              *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                              subset.v                                    *)
(****************************************************************************)


(* 
We define subset as types in the same way as quotients:
like in the deliverable model where a subset is a type
and a predicate on that type.
The alternative consisting of using a strong sum to encode
this feature suffers from the fact that we need to
use proof irrelevance if we want two
objects (a,pa) (a,pb) with pa,pb:(P a) to be identified.
*)

(* Definition of a subset: *)

Parameter MK_SUBSET : forall (A : Set) (R : A -> Prop), Set.

(* An element of a subset is an element of the underlying type
with a proof that this element satisfies the underlying predicate *)

Parameter
  In_subset : forall (A : Set) (R : A -> Prop) (a : A), R a -> MK_SUBSET A R.

(* Every element of a subset is an element of the underlying type *)

Parameter Out_subset : forall (A : Set) (R : A -> Prop), MK_SUBSET A R -> A.

(* Every element of the subset should satisfy the underlying predicate *)

Parameter
  proof :
    forall (A : Set) (R : A -> Prop) (t : MK_SUBSET A R),
    R (Out_subset A R t).

(* Rewrite rules explaining coercion principles between the subset and its 
underlying type *)

Axiom
  In_Out :
    forall (A : Set) (R : A -> Prop) (t : MK_SUBSET A R)
      (p : R (Out_subset A R t)), In_subset A R (Out_subset A R t) p = t.

Axiom
  Out_In :
    forall (A : Set) (R : A -> Prop) (t : A) (p : R t),
    Out_subset A R (In_subset A R t p) = t.

(* Without proof irrelevance we should identify two element of a subset
as soon as their projection on the ground type are leibniz equal *)

Axiom
  Canonic :
    forall (A : Set) (R : A -> Prop) (t : A) (p p' : R t),
    In_subset A R t p = In_subset A R t p'.

(* Closure axioms defining the canonical form of objects of a subset type *)

Axiom
  Prop_closure :
    forall (A : Set) (R : A -> Prop) (P : MK_SUBSET A R -> Prop)
      (x : MK_SUBSET A R),
    (forall (y : A) (p : R y), P (In_subset A R y p)) -> P x.

Axiom
  Set_closure :
    forall (A : Set) (R : A -> Prop) (P : MK_SUBSET A R -> Set)
      (x : MK_SUBSET A R),
    (forall (y : A) (p : R y), P (In_subset A R y p)) -> P x.


(* Notation for subsets: *)

Notation "c ! p" := (MK_SUBSET c p) (at level 20).

Notation "%+ c" := (In_subset _ _ _ c) (at level 20).

(*
Require quotient.

Grammar constr constr1 := 
  mksub [ constr0($c) "!" constr0($c2) ] -> [ (MK_SUBSET $c $c2) ].

Syntax constr 
  level 1:
  MK_SUBSET [ (MK_QUO $c $c1) ] -> [$c: L "!" $c1:L].
*)