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
(*  Absz.v                                                                  *)
(*                                                                          *)
(*  Definition of the absolute value on integers                            *)
(*                                                                          *)
(*                                                                          *)
(*  Samuel Boutin                                                           *)
(*  Coq V5.10                                                               *)
(*  June  1995                                                              *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                               Absz.v                                     *)
(****************************************************************************)


Require Import quotient.
Require Import Arith.

Section AbsZ.

Require Import integer.

Lemma ABSZ : forall z : Z, Z.

intro z.
elim (Constructive_Z_partition z).
simple induction 1.
intro.
exact (- z)%INT.
intro.
exact z.
intro.
exact z.
Defined.

(* On a construit le terme:

ABSZ_O < Print ABSZ.
ABSZ =
[z:Z]
 (sumor_rec {(leZ z |((O,(S O)))|)}+{z=|((O,O))|} (leZ |(((S O),O))| z)
   [_:({(leZ z |((O,(S O)))|)}+{z=|((O,O))|})+{(leZ |(((S O),O))| z)}]Z
   [y:{(leZ z |((O,(S O)))|)}+{z=|((O,O))|}]
    (sumbool_rec (leZ z |((O,(S O)))|) z=|((O,O))|
      [_:{(leZ z |((O,(S O)))|)}+{z=|((O,O))|}]Z
      [_:(leZ z |((O,(S O)))|)](unary_minus z) [_:z=|((O,O))|]z y)
   [_:(leZ |(((S O),O))| z)]z (Constructive_Z_partition z))
     : Z->Z

Rappel:


( Syntax sumbool "{_}+{_}". )
Inductive sumbool [A,B:Prop] : Set
    := left  : A -> ({A}+{B}) 
     | right : B -> ({A}+{B}).

*)

Open Scope INT_scope.

Lemma ABSZ_neg : forall z : Z, z <= - 1 -> ABSZ z = - z.

intros.
elim (z_lt_O z H).
intros.
unfold ABSZ in |- *.
rewrite H0; simpl in |- *.
auto with arith.
Qed.

Lemma ABSZ_O : forall z : Z, z = 0 -> ABSZ z = z. 

intros.
elim (z_eq_O z H).
intros.
unfold ABSZ in |- *.
rewrite H0; simpl in |- *.
auto with arith.
Qed.


Lemma ABSZ_pos : forall z : Z, 1 <= z -> ABSZ z = z.

intros.
elim (O_lt_z z H).
intros.
unfold ABSZ in |- *.
rewrite H0; simpl in |- *.
auto with arith.
Qed.

Opaque ABSZ.

End AbsZ.