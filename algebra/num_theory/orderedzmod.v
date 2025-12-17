(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import ssrAC div fintype path bigop order finset fingroup.
From mathcomp Require Import ssralg poly.

(******************************************************************************)
(*                    Number structures (orderedzmod.v)                       *)
(*                                                                            *)
(* NB: See CONTRIBUTING.md for an introduction to HB concepts and commands.   *)
(*                                                                            *)
(* NB: The header of ssrnum.v explains how to use the files in this directory.*)
(*                                                                            *)
(* This file defines the following number structures:                         *)
(*                                                                            *)
(*  porderZmodType == join of Order.POrder and GRing.Zmodule                  *)
(*                    The HB class is called POrderedZmodule.                 *)
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

Local Open Scope order_scope.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Import Order.TTheory GRing.Theory.

Fact ring_display : Order.disp_t. Proof. exact. Qed.

Module Num.
  
HB.structure Definition BasePOrderedZmodule :=
  { R of Order.BasePreorder ring_display R & GRing.BaseZmodule R }.

#[short(type="porderZmodType")]
HB.structure Definition POrderedZmodule :=
  { R of Order.isPOrder ring_display R & GRing.Zmodule R }.

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
Context {R : porderZmodType}.

Definition pos_num_pred := fun x : R => 0 < x.
Definition pos_num : qualifier 0 R := [qualify x | pos_num_pred x].
Definition neg_num_pred := fun x : R => x < 0.
Definition neg_num : qualifier 0 R := [qualify x : R | neg_num_pred x].
Definition nneg_num_pred := fun x : R => 0 <= x.
Definition nneg_num : qualifier 0 R := [qualify x : R | nneg_num_pred x].
Definition npos_num_pred := fun x : R => x <= 0.
Definition npos_num : qualifier 0 R := [qualify x : R | npos_num_pred x].
Definition real_num_pred := fun x : R => (0 <= x) || (x <= 0).
Definition real_num : qualifier 0 R := [qualify x : R | real_num_pred x].

End Def.

Arguments pos_num_pred _ _ /.
Arguments neg_num_pred _ _ /.
Arguments nneg_num_pred _ _ /.
Arguments real_num_pred _ _ /.

#[deprecated(since="mathcomp 2.5.0", use=pos_num_pred)]
Notation Rpos_pred := pos_num_pred (only parsing).
#[deprecated(since="mathcomp 2.5.0", use=pos_num)]
Notation Rpos := pos_num (only parsing).
#[deprecated(since="mathcomp 2.5.0", use=neg_num_pred)]
Notation Rneg_pred := neg_num_pred (only parsing).
#[deprecated(since="mathcomp 2.5.0", use=neg_num)]
Notation Rneg := neg_num (only parsing).
#[deprecated(since="mathcomp 2.5.0", use=nneg_num_pred)]
Notation Rnneg_pred := nneg_num_pred (only parsing).
#[deprecated(since="mathcomp 2.5.0", use=nneg_num)]
Notation Rnneg := nneg_num (only parsing).
#[deprecated(since="mathcomp 2.5.0", use=npos_num_pred)]
Notation Rnpos_pred := npos_num_pred (only parsing).
#[deprecated(since="mathcomp 2.5.0", use=npos_num)]
Notation Rnpos := npos_num (only parsing).
#[deprecated(since="mathcomp 2.5.0", use=real_num_pred)]
Notation Rreal_pred := real_num_pred (only parsing).
#[deprecated(since="mathcomp 2.5.0", use=real_num)]
Notation Rreal := real_num (only parsing).

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
Notation pos := pos_num.
Notation neg := neg_num.
Notation nneg := nneg_num.
Notation npos := npos_num.
Notation real := real_num.

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
