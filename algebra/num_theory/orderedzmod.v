(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import ssrAC div fintype path bigop order finset fingroup.
From mathcomp Require Import ssralg poly.

(******************************************************************************)
(*                            Number structures                               *)
(*                                                                            *)
(* NB: See CONTRIBUTING.md for an introduction to HB concepts and commands.   *)
(*                                                                            *)
(* This file defines some classes to manipulate number structures, i.e,       *)
(* structures with an order and a norm. To use this file, insert              *)
(* "Import Num.Theory." before your scripts. You can also "Import Num.Def."   *)
(* to enjoy shorter notations (e.g., minr instead of Num.min, lerif instead   *)
(* of Num.leif, etc.).                                                        *)
(*                                                                            *)
(* This file defines the following number structures:                         *)
(*                                                                            *)
(*    porderNmodType == join of Order.POrder and GRing.Nmodule                *)
(*                      The HB class is called POrderNmodule.                 *)
(*    porderZmodType == join of Order.POrder and GRing.Zmodule                *)
(*                      The HB class is called POrderZmodule.                 *)
(*  porderedNmodType == porderNmodType such that                              *)
(*                      the order is translation invariant.                   *)
(*                      The HB class is called POrderedNmodule.               *)
(*  porderedZmodType == porderZmodType such that                              *)
(*                      the order is translation invariant.                   *)
(*                      The HB class is called POrderedZmodule.               *)
(*       numZmodType == porderedZmodType such that                            *)
(*                      the real line (i.e. the comparable to 0)              *)
(*                      is totally ordered                                    *)
(*                                                                            *)
(* The ordering symbols and notations (<, <=, >, >=, _ <= _ ?= iff _,         *)
(* _ < _ ?<= if _, >=<, and ><) and lattice operations (meet and join)        *)
(* defined in order.v are redefined for the ring_display in the ring_scope    *)
(* (%R). 0-ary ordering symbols for the ring_display have the suffix "%R",    *)
(* e.g., <%R. All the other ordering notations are the same as order.v.       *)
(*                                                                            *)
(* Over these structures, we have the following operations:                   *)
(*  x \is a Num.pos <=> x is positive (:= x > 0)                              *)
(*  x \is a Num.neg <=> x is negative (:= x < 0)                              *)
(* x \is a Num.nneg <=> x is positive or 0 (:= x >= 0)                        *)
(* x \is a Num.npos <=> x is negative or 0 (:= x <= 0)                        *)
(* x \is a Num.real <=> x is real (:= x >= 0 or x < 0)                        *)
(*                                                                            *)
(* - list of prefixes :                                                       *)
(*   p : positive                                                             *)
(*   n : negative                                                             *)
(*   sp : strictly positive                                                   *)
(*   sn : strictly negative                                                   *)
(*   i : interior = in [0, 1] or ]0, 1[                                       *)
(*   e : exterior = in [1, +oo[ or ]1; +oo[                                   *)
(*   w : non strict (weak) monotony                                           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "n .-root" (format "n .-root").
Reserved Notation "'i".
Reserved Notation "'Re z" (at level 10, z at level 8).
Reserved Notation "'Im z" (at level 10, z at level 8).

Local Open Scope order_scope.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Import Order.TTheory GRing.Theory.

Fact ring_display : Order.disp_t. Proof. exact. Qed.

Module Num.

#[short(type="porderNmodType")]
HB.structure Definition POrderNmodule :=
  { R of Order.isPOrder ring_display R & GRing.Nmodule R}.
#[short(type="porderZmodType")]
HB.structure Definition POrderZmodule :=
  { R of Order.isPOrder ring_display R & GRing.Zmodule R}.

HB.mixin Record Add_isMono R of POrderNmodule R := {
  lerD2l : forall x : R, {mono +%R x : y z / y <= z}
}.

(* TODO provide the positive cone definition of porderZmodType *)
(* HB.factory Record ZmodulePositiveCone_isPOrdered of GRing.Zmodule R *)
(*    & Order.isPOrder ring_display R := { *)
(*   (* TODO: is posnum the right name? *) *)
(*   posnum : {pred R}; *)
(*   posnum0 :  *)

#[short(type="porderedNmodType")]
HB.structure Definition POrderedNmodule :=
  { R of POrderNmodule R & Add_isMono R}.
#[short(type="porderedZmodType")]
HB.structure Definition POrderedZmodule :=
  { R of GRing.Zmodule R & POrderedNmodule R}.

HB.mixin Record POrderedZmodule_hasTransCmp R of GRing.Nmodule R
    & Order.isPOrder ring_display R := {
  comparabler_trans : transitive (Order.comparable : rel R)
}.
#[short(type="numZmodType")]
HB.structure Definition NumZmodule :=
  {R of POrderedZmodule_hasTransCmp R & POrderedZmodule R}.

Bind Scope ring_scope with POrderNmodule.sort.
Bind Scope ring_scope with POrderZmodule.sort.
Bind Scope ring_scope with POrderedZmodule.sort.
Bind Scope ring_scope with POrderedZmodule.sort.
Bind Scope ring_scope with NumZmodule.sort.

Module Export Def.

Notation ler := (@Order.le ring_display _) (only parsing).
Notation "@ 'ler' R" := (@Order.le ring_display R)
  (at level 10, R at level 8, only parsing) : function_scope.
Notation ltr := (@Order.lt ring_display _) (only parsing).
Notation "@ 'ltr' R" := (@Order.lt ring_display R)
  (at level 10, R at level 8, only parsing) : function_scope.
Notation ger := (@Order.ge ring_display _) (only parsing).
Notation "@ 'ger' R" := (@Order.ge ring_display R)
  (at level 10, R at level 8, only parsing) : function_scope.
Notation gtr := (@Order.gt ring_display _) (only parsing).
Notation "@ 'gtr' R" := (@Order.gt ring_display R)
  (at level 10, R at level 8, only parsing) : function_scope.
Notation lerif := (@Order.leif ring_display _) (only parsing).
Notation "@ 'lerif' R" := (@Order.leif ring_display R)
  (at level 10, R at level 8, only parsing) : function_scope.
Notation lterif := (@Order.lteif ring_display _) (only parsing).
Notation "@ 'lteif' R" := (@Order.lteif ring_display R)
  (at level 10, R at level 8, only parsing) : function_scope.
Notation comparabler := (@Order.comparable ring_display _) (only parsing).
Notation "@ 'comparabler' R" := (@Order.comparable ring_display R)
  (at level 10, R at level 8, only parsing) : function_scope.
Notation maxr := (@Order.max ring_display _).
Notation "@ 'maxr' R" := (@Order.max ring_display R)
  (at level 10, R at level 8, only parsing) : function_scope.
Notation minr := (@Order.min ring_display _).
Notation "@ 'minr' R" := (@Order.min ring_display R)
  (at level 10, R at level 8, only parsing) : function_scope.

Section Def.
Context {R : porderNmodType}.

Definition Rpos_pred := fun x : R => 0 < x.
Definition Rpos : qualifier 0 R := [qualify x | Rpos_pred x].
Definition Rneg_pred := fun x : R => x < 0.
Definition Rneg : qualifier 0 R := [qualify x : R | Rneg_pred x].
Definition Rnneg_pred := fun x : R => 0 <= x.
Definition Rnneg : qualifier 0 R := [qualify x : R | Rnneg_pred x].
Definition Rnpos_pred := fun x : R => x <= 0.
Definition Rnpos : qualifier 0 R := [qualify x : R | Rnpos_pred x].
Definition Rreal_pred := fun x : R => (0 <= x) || (x <= 0).
Definition Rreal : qualifier 0 R := [qualify x : R | Rreal_pred x].

End Def.

Arguments Rpos_pred _ _ /.
Arguments Rneg_pred _ _ /.
Arguments Rnneg_pred _ _ /.
Arguments Rreal_pred _ _ /.
End Def.

(* Shorter qualified names, when Num.Def is not imported. *)
Notation le := ler (only parsing).
Notation lt := ltr (only parsing).
Notation ge := ger (only parsing).
Notation gt := gtr (only parsing).
Notation leif := lerif (only parsing).
Notation lteif := lterif (only parsing).
Notation comparable := comparabler (only parsing).
Notation max := maxr.
Notation min := minr.
Notation pos := Rpos.
Notation neg := Rneg.
Notation nneg := Rnneg.
Notation npos := Rnpos.
Notation real := Rreal.

(* (Exported) symbolic syntax. *)
Module Import Syntax.

Notation "<=%R" := le : function_scope.
Notation ">=%R" := ge : function_scope.
Notation "<%R" := lt : function_scope.
Notation ">%R" := gt : function_scope.
Notation "<?=%R" := leif : function_scope.
Notation "<?<=%R" := lteif : function_scope.
Notation ">=<%R" := comparable : function_scope.
Notation "><%R" := (fun x y => ~~ (comparable x y)) : function_scope.

Notation "<= y" := (ge y) : ring_scope.
Notation "<= y :> T" := (<= (y : T)) (only parsing) : ring_scope.
Notation ">= y"  := (le y) : ring_scope.
Notation ">= y :> T" := (>= (y : T)) (only parsing) : ring_scope.

Notation "< y" := (gt y) : ring_scope.
Notation "< y :> T" := (< (y : T)) (only parsing) : ring_scope.
Notation "> y" := (lt y) : ring_scope.
Notation "> y :> T" := (> (y : T)) (only parsing) : ring_scope.

Notation "x <= y" := (le x y) : ring_scope.
Notation "x <= y :> T" := ((x : T) <= (y : T)) (only parsing) : ring_scope.
Notation "x >= y" := (y <= x) (only parsing) : ring_scope.
Notation "x >= y :> T" := ((x : T) >= (y : T)) (only parsing) : ring_scope.

Notation "x < y"  := (lt x y) : ring_scope.
Notation "x < y :> T" := ((x : T) < (y : T)) (only parsing) : ring_scope.
Notation "x > y"  := (y < x) (only parsing) : ring_scope.
Notation "x > y :> T" := ((x : T) > (y : T)) (only parsing) : ring_scope.

Notation "x <= y <= z" := ((x <= y) && (y <= z)) : ring_scope.
Notation "x < y <= z" := ((x < y) && (y <= z)) : ring_scope.
Notation "x <= y < z" := ((x <= y) && (y < z)) : ring_scope.
Notation "x < y < z" := ((x < y) && (y < z)) : ring_scope.

Notation "x <= y ?= 'iff' C" := (lerif x y C) : ring_scope.
Notation "x <= y ?= 'iff' C :> R" := ((x : R) <= (y : R) ?= iff C)
  (only parsing) : ring_scope.

Notation "x < y ?<= 'if' C" := (lterif x y C) : ring_scope.
Notation "x < y ?<= 'if' C :> R" := ((x : R) < (y : R) ?<= if C)
  (only parsing) : ring_scope.

Notation ">=< y" := [pred x | comparable x y] : ring_scope.
Notation ">=< y :> T" := (>=< (y : T)) (only parsing) : ring_scope.
Notation "x >=< y" := (comparable x y) : ring_scope.

Notation ">< y" := [pred x | ~~ comparable x y] : ring_scope.
Notation ">< y :> T" := (>< (y : T)) (only parsing) : ring_scope.
Notation "x >< y" := (~~ (comparable x y)) : ring_scope.

Export Order.PreOCoercions.

End Syntax.

Module Export Theory.

End Theory.

Module Exports. HB.reexport. End Exports.
End Num.
Export Num.Syntax Num.Exports.
