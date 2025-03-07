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
(*  porderNmodType   == join of Order.POrder and GRing.Nmodule                *)
(*                      The HB class is called POrderNmodule.                 *)
(*  porderZmodType   == join of Order.POrder and GRing.Zmodule                *)
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

Reserved Notation "n .-root" (at level 2, format "n .-root").
Reserved Notation "'i" (at level 0).
Reserved Notation "'Re z" (at level 10, z at level 8).
Reserved Notation "'Im z" (at level 10, z at level 8).

Reserved Notation "x %:E" (at level 2, format "x %:E").
Reserved Notation "x %:dE" (at level 2, format "x %:dE").
Reserved Notation "x +? y" (at level 50, format "x  +?  y").
Reserved Notation "x *? y" (at level 50, format "x  *?  y").
Reserved Notation "'\bar' x" (at level 2, format "'\bar'  x").
Reserved Notation "'\bar' '^d' x" (at level 2, format "'\bar' '^d'  x").
Reserved Notation "{ 'posnum' '\bar' R }" (at level 0,
  format "{ 'posnum'  '\bar'  R }").
Reserved Notation "{ 'nonneg' '\bar' R }" (at level 0,
  format "{ 'nonneg'  '\bar'  R }").

Declare Scope ereal_dual_scope.
Declare Scope ereal_scope.
Local Open Scope order_scope.
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

Module Export Def.
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

Export Order.POCoercions.

End Syntax.

Module Export Theory.
Section porderZmodTypeTheory.
Variable (R : porderedZmodType).
Implicit Types (x y : R).

(* Monotony of addition *)

Lemma lerD2l x : {mono +%R x : y z / y <= z}.
Proof. exact: lerD2l. Qed.

Lemma lerD2r x : {mono +%R^~ x : y z / y <= z}.
Proof. by move=> y z; rewrite ![_ + x]addrC lerD2l. Qed.

Lemma ltrD2r x : {mono +%R^~ x : y z / y < z}.
Proof. by move=> y z; rewrite !lt_neqAle lerD2r (inj_eq (addIr _)). Qed.

Lemma ltrD2l x : {mono +%R x : y z / y < z}.
Proof. by move=> y z; rewrite !lt_neqAle lerD2l (inj_eq (addrI _)). Qed.

Definition lerD2 := (lerD2l, lerD2r).
Definition ltrD2 := (ltrD2l, ltrD2r).
Definition lterD2 := (lerD2, ltrD2).

(* Comparison and negation / opposite. *)

Lemma subr_ge0 x y : (0 <= x - y) = (y <= x).
Proof. by rewrite -(@lerD2r y) addrNK add0r. Qed.

Lemma oppr_ge0 x : (0 <= - x) = (x <= 0).
Proof. by rewrite -sub0r subr_ge0. Qed.

Lemma subr_gt0 x y : (0 < y - x) = (x < y).
Proof. by rewrite !lt_def subr_eq0 subr_ge0. Qed.

Lemma subr_le0  x y : (y - x <= 0) = (y <= x).
Proof. by rewrite -[LHS]subr_ge0 opprB add0r subr_ge0. Qed.  (* FIXME: rewrite pattern *)

Lemma subr_lt0  x y : (y - x < 0) = (y < x).
Proof. by rewrite -[LHS]subr_gt0 opprB add0r subr_gt0. Qed.  (* FIXME: rewrite pattern *)

Lemma lerN2 : {mono -%R : x y /~ x <= y :> R}.
Proof. by move=> x y /=; rewrite -subr_ge0 opprK addrC subr_ge0. Qed.
Hint Resolve lerN2 : core.
Lemma ltrN2 : {mono -%R : x y /~ x < y :> R}.
Proof. by move=> x y /=; rewrite leW_nmono. Qed.
Hint Resolve ltrN2 : core.
Definition lterN2 := (lerN2, ltrN2).

Lemma lerNr x y : (x <= - y) = (y <= - x).
Proof. by rewrite (monoRL opprK lerN2). Qed.

Lemma ltrNr x y : (x < - y) = (y < - x).
Proof. by rewrite (monoRL opprK (leW_nmono _)). Qed.

Definition lterNr := (lerNr, ltrNr).

Lemma lerNl x y : (- x <= y) = (- y <= x).
Proof. by rewrite (monoLR opprK lerN2). Qed.

Lemma ltrNl x y : (- x < y) = (- y < x).
Proof. by rewrite (monoLR opprK (leW_nmono _)). Qed.

Definition lterNl := (lerNl, ltrNl).

Definition subr_lte0 := (subr_le0, subr_lt0).
Definition subr_gte0 := (subr_ge0, subr_gt0).
Definition subr_cp0 := (subr_lte0, subr_gte0).

(* Addition, subtraction and transitivity *)
Lemma lerD x y z t : x <= y -> z <= t -> x + z <= y + t.
Proof. by move=> lxy lzt; rewrite (@le_trans _ _ (y + z)) ?lterD2. Qed.

Lemma ler_ltD x y z t : x <= y -> z < t -> x + z < y + t.
Proof. by move=> lxy lzt; rewrite (@le_lt_trans _ _ (y + z)) ?lterD2. Qed.

Lemma ltr_leD x y z t : x < y -> z <= t -> x + z < y + t.
Proof. by move=> lxy lzt; rewrite (@lt_le_trans _ _ (y + z)) ?lterD2. Qed.

Lemma ltrD x y z t : x < y -> z < t -> x + z < y + t.
Proof. by move=> lxy lzt; rewrite ltr_leD // ltW. Qed.

Lemma lerB x y z t : x <= y -> t <= z -> x - z <= y - t.
Proof. by move=> lxy ltz; rewrite lerD // lterN2. Qed.

Lemma ler_ltB x y z t : x <= y -> t < z -> x - z < y - t.
Proof. by move=> lxy lzt; rewrite ler_ltD // lterN2. Qed.

Lemma ltr_leB x y z t : x < y -> t <= z -> x - z < y - t.
Proof. by move=> lxy lzt; rewrite ltr_leD // lterN2. Qed.

Lemma ltrB x y z t : x < y -> t < z -> x - z < y - t.
Proof. by move=> lxy lzt; rewrite ltrD // lterN2. Qed.

Lemma lerBlDr x y z : (x - y <= z) = (x <= z + y).
Proof. by rewrite (monoLR (addrK _) (lerD2r _)). Qed.

Lemma ltrBlDr x y z : (x - y < z) = (x < z + y).
Proof. by rewrite (monoLR (addrK _) (ltrD2r _)). Qed.

Lemma lerBrDr x y z : (x <= y - z) = (x + z <= y).
Proof. by rewrite (monoLR (addrNK _) (lerD2r _)). Qed.

Lemma ltrBrDr x y z : (x < y - z) = (x + z < y).
Proof. by rewrite (monoLR (addrNK _) (ltrD2r _)). Qed.

Definition lerBDr := (lerBlDr, lerBrDr).
Definition ltrBDr := (ltrBlDr, ltrBrDr).
Definition lterBDr := (lerBDr, ltrBDr).

Lemma lerBlDl x y z : (x - y <= z) = (x <= y + z).
Proof. by rewrite lterBDr addrC. Qed.

Lemma ltrBlDl x y z : (x - y < z) = (x < y + z).
Proof. by rewrite lterBDr addrC. Qed.

Lemma lerBrDl x y z : (x <= y - z) = (z + x <= y).
Proof. by rewrite lerBrDr addrC. Qed.

Lemma ltrBrDl x y z : (x < y - z) = (z + x < y).
Proof. by rewrite lterBDr addrC. Qed.

Definition lerBDl := (lerBlDl, lerBrDl).
Definition ltrBDl := (ltrBlDl, ltrBrDl).
Definition lterBDl := (lerBDl, ltrBDl).

Lemma lerDl x y : (x <= x + y) = (0 <= y).
Proof. by rewrite -{1}[x]addr0 lterD2. Qed.

Lemma ltrDl x y : (x < x + y) = (0 < y).
Proof. by rewrite -{1}[x]addr0 lterD2. Qed.

Lemma lerDr x y : (x <= y + x) = (0 <= y).
Proof. by rewrite -{1}[x]add0r lterD2. Qed.

Lemma ltrDr x y : (x < y + x) = (0 < y).
Proof. by rewrite -{1}[x]add0r lterD2. Qed.

Lemma gerDl x y : (x + y <= x) = (y <= 0).
Proof. by rewrite -{2}[x]addr0 lterD2. Qed.

Lemma gerBl x y : (x - y <= x) = (0 <= y).
Proof. by rewrite lerBlDl lerDr. Qed.

Lemma gtrDl x y : (x + y < x) = (y < 0).
Proof. by rewrite -{2}[x]addr0 lterD2. Qed.

Lemma gtrBl x y : (x - y < x) = (0 < y).
Proof. by rewrite ltrBlDl ltrDr. Qed.

Lemma gerDr x y : (y + x <= x) = (y <= 0).
Proof. by rewrite -{2}[x]add0r lterD2. Qed.

Lemma gtrDr x y : (y + x < x) = (y < 0).
Proof. by rewrite -{2}[x]add0r lterD2. Qed.

Definition cprD := (lerDl, lerDr, gerDl, gerDl,
                    ltrDl, ltrDr, gtrDl, gtrDl).

Lemma addr_ge0 x y : 0 <= x -> 0 <= y -> 0 <= x + y.
Proof.
move=> x_ge0 y_ge0; have := lerD2r y 0 x.
by rewrite add0r x_ge0 => /(le_trans y_ge0).
Qed.

Lemma addr_gt0 x y : 0 < x -> 0 < y -> 0 < x + y.
Proof.
move=> x_gt0 y_gt0; have := ltrD2r y 0 x.
by rewrite add0r x_gt0 => /(lt_trans y_gt0).
Qed.

Lemma posrE x : (x \is Num.pos) = (0 < x). Proof. by []. Qed.
Lemma nnegrE x : (x \is Num.nneg) = (0 <= x). Proof. by []. Qed.
Lemma realE x : (x \is Num.real) = (0 <= x) || (x <= 0). Proof. by []. Qed.
Lemma negrE x : (x \is Num.neg) = (x < 0). Proof. by []. Qed.
Lemma nposrE x : (x \is Num.npos) = (x <= 0). Proof. by []. Qed.

Lemma le0r x : (0 <= x) = (x == 0) || (0 < x).
Proof. by rewrite le_eqVlt eq_sym. Qed.
Lemma lt0r x : (0 < x) = (x != 0) && (0 <= x). Proof. exact: lt_def. Qed.

Lemma lt0r_neq0 (x : R) : 0 < x -> x != 0. Proof. by move=> /gt_eqF ->. Qed.
Lemma ltr0_neq0 (x : R) : x < 0 -> x != 0. Proof. by move=> /lt_eqF ->. Qed.

(* Ordered ring properties. *)

Lemma oppr_gt0 x : (0 < - x) = (x < 0). Proof. by rewrite ltrNr oppr0. Qed.

Definition oppr_gte0 := (oppr_ge0, oppr_gt0).

Lemma oppr_le0 x : (- x <= 0) = (0 <= x). Proof. by rewrite lerNl oppr0. Qed.

Lemma oppr_lt0 x : (- x < 0) = (0 < x). Proof. by rewrite ltrNl oppr0. Qed.

Lemma gtrN x : 0 < x -> - x < x.
Proof. by move=> n0; rewrite -subr_lt0 -opprD oppr_lt0 addr_gt0. Qed.

Definition oppr_lte0 := (oppr_le0, oppr_lt0).
Definition oppr_cp0 := (oppr_gte0, oppr_lte0).
Definition lterNE := (oppr_cp0, lterN2).

Lemma ge0_cp x : 0 <= x -> (- x <= 0) * (- x <= x).
Proof. by move=> hx; rewrite oppr_cp0 hx (@le_trans _ _ 0) ?oppr_cp0. Qed.

Lemma gt0_cp x : 0 < x ->
  (0 <= x) * (- x <= 0) * (- x <= x) * (- x < 0) * (- x < x).
Proof.
move=> hx; move: (ltW hx) => hx'; rewrite !ge0_cp hx' //.
by rewrite oppr_cp0 hx // (@lt_trans _ _ 0) ?oppr_cp0.
Qed.

Lemma le0_cp x : x <= 0 -> (0 <= - x) * (x <= - x).
Proof. by move=> hx; rewrite oppr_cp0 hx (@le_trans _ _ 0) ?oppr_cp0. Qed.

Lemma lt0_cp x :
  x < 0 -> (x <= 0) * (0 <= - x) * (x <= - x) * (0 < - x) * (x < - x).
Proof.
move=> hx; move: (ltW hx) => hx'; rewrite !le0_cp // hx'.
by rewrite oppr_cp0 hx // (@lt_trans _ _ 0) ?oppr_cp0.
Qed.

(* Addition with left member known to be positive/negative *)
Lemma ler_wpDl y x z : 0 <= x -> y <= z -> y <= x + z.
Proof. by move=> *; rewrite -[y]add0r lerD. Qed.

Lemma ltr_wpDl y x z : 0 <= x -> y < z -> y < x + z.
Proof. by move=> *; rewrite -[y]add0r ler_ltD. Qed.

Lemma ltr_pwDl y x z : 0 < x -> y <= z -> y < x + z.
Proof. by move=> *; rewrite -[y]add0r ltr_leD. Qed.

Lemma ltr_pDl y x z : 0 < x -> y < z -> y < x + z.
Proof. by move=> *; rewrite -[y]add0r ltrD. Qed.

Lemma ler_wnDl y x z : x <= 0 -> y <= z -> x + y <= z.
Proof. by move=> *; rewrite -[z]add0r lerD. Qed.

Lemma ltr_wnDl y x z : x <= 0 -> y < z -> x + y < z.
Proof. by move=> *; rewrite -[z]add0r ler_ltD. Qed.

Lemma ltr_nwDl y x z : x < 0 -> y <= z -> x + y < z.
Proof. by move=> *; rewrite -[z]add0r ltr_leD. Qed.

Lemma ltr_nDl y x z : x < 0 -> y < z -> x + y < z.
Proof. by move=> *; rewrite -[z]add0r ltrD. Qed.

(* Addition with right member we know positive/negative *)
Lemma ler_wpDr y x z : 0 <= x -> y <= z -> y <= z + x.
Proof. by move=> *; rewrite addrC ler_wpDl. Qed.

Lemma ltr_wpDr y x z : 0 <= x -> y < z -> y < z + x.
Proof. by move=> *; rewrite addrC ltr_wpDl. Qed.

Lemma ltr_pwDr y x z : 0 < x -> y <= z -> y < z + x.
Proof. by move=> *; rewrite addrC ltr_pwDl. Qed.

Lemma ltr_pDr y x z : 0 < x -> y < z -> y < z + x.
Proof. by move=> *; rewrite addrC ltr_pDl. Qed.

Lemma ler_wnDr y x z : x <= 0 -> y <= z -> y + x <= z.
Proof. by move=> *; rewrite addrC ler_wnDl. Qed.

Lemma ltr_wnDr y x z : x <= 0 -> y < z -> y + x < z.
Proof. by move=> *; rewrite addrC ltr_wnDl. Qed.

Lemma ltr_nwDr y x z : x < 0 -> y <= z -> y + x < z.
Proof. by move=> *; rewrite addrC ltr_nwDl. Qed.

Lemma ltr_nDr y x z : x < 0 -> y < z -> y + x < z.
Proof. by move=> *; rewrite addrC ltr_nDl. Qed.

(* x and y have the same sign and their sum is null *)
Lemma paddr_eq0 (x y : R) :
  0 <= x -> 0 <= y -> (x + y == 0) = (x == 0) && (y == 0).
Proof.
rewrite le0r; case/orP=> [/eqP->|hx]; first by rewrite add0r eqxx.
by rewrite (gt_eqF hx) /= => hy; rewrite gt_eqF // ltr_pwDl.
Qed.

Lemma naddr_eq0 (x y : R) :
  x <= 0 -> y <= 0 -> (x + y == 0) = (x == 0) && (y == 0).
Proof.
by move=> lex0 ley0; rewrite -oppr_eq0 opprD paddr_eq0 ?oppr_cp0 // !oppr_eq0.
Qed.

Lemma addr_ss_eq0 (x y : R) :
    (0 <= x) && (0 <= y) || (x <= 0) && (y <= 0) ->
  (x + y == 0) = (x == 0) && (y == 0).
Proof. by case/orP=> /andP []; [apply: paddr_eq0 | apply: naddr_eq0]. Qed.

(* big sum and ler *)
Lemma sumr_ge0 I (r : seq I) (P : pred I) (F : I -> R) :
  (forall i, P i -> (0 <= F i)) -> 0 <= \sum_(i <- r | P i) (F i).
Proof. exact: (big_ind _ _ (@ler_wpDl 0)). Qed.

Lemma ler_sum I (r : seq I) (P : pred I) (F G : I -> R) :
    (forall i, P i -> F i <= G i) ->
  \sum_(i <- r | P i) F i <= \sum_(i <- r | P i) G i.
Proof. exact: (big_ind2 _ (lexx _) lerD). Qed.

Lemma ler_sum_nat (m n : nat) (F G : nat -> R) :
  (forall i, (m <= i < n)%N -> F i <= G i) ->
  \sum_(m <= i < n) F i <= \sum_(m <= i < n) G i.
Proof. by move=> le_FG; rewrite !big_nat ler_sum. Qed.

Lemma psumr_eq0 (I : eqType) (r : seq I) (P : pred I) (F : I -> R) :
    (forall i, P i -> 0 <= F i) ->
  (\sum_(i <- r | P i) (F i) == 0) = (all (fun i => (P i) ==> (F i == 0)) r).
Proof.
elim: r=> [|a r ihr hr] /=; rewrite (big_nil, big_cons); first by rewrite eqxx.
by case: ifP=> pa /=; rewrite ?paddr_eq0 ?ihr ?hr // sumr_ge0.
Qed.

(* :TODO: Cyril : See which form to keep *)
Lemma psumr_eq0P (I : finType) (P : pred I) (F : I -> R) :
     (forall i, P i -> 0 <= F i) -> \sum_(i | P i) F i = 0 ->
  (forall i, P i -> F i = 0).
Proof.
move=> F_ge0 /eqP; rewrite psumr_eq0 // -big_all big_andE => /forallP hF i Pi.
by move: (hF i); rewrite implyTb Pi /= => /eqP.
Qed.

Lemma psumr_neq0 (I : eqType) (r : seq I) (P : pred I) (F : I -> R) :
    (forall i, P i -> 0 <= F i) ->
  (\sum_(i <- r | P i) (F i) != 0) = (has (fun i => P i && (0 < F i)) r).
Proof.
move=> F_ge0; rewrite psumr_eq0// -has_predC; apply: eq_has => x /=.
by case Px: (P x); rewrite //= lt_def F_ge0 ?andbT.
Qed.

Lemma psumr_neq0P (I : finType) (P : pred I) (F : I -> R) :
     (forall i, P i -> 0 <= F i) -> \sum_(i | P i) F i <> 0 ->
  (exists i, P i && (0 < F i)).
Proof. by move=> ? /eqP; rewrite psumr_neq0// => /hasP[x _ ?]; exists x. Qed.

Lemma ltr_wpMn2r n : (0 < n)%N -> {homo (@GRing.natmul R)^~ n : x y / x < y}.
Proof.
elim: n => // -[|n] IHn _ x y ltxy//.
by rewrite mulrS [in ltRHS]mulrS ltrD// IHn.
Qed.

Lemma ler_wMn2r n : {homo (@GRing.natmul R)^~ n : x y / x <= y}.
Proof. by case: n => // n; exact/ltW_homo/ltr_wpMn2r. Qed.

Lemma mulrn_wge0 x n : 0 <= x -> 0 <= x *+ n.
Proof. by move=> /(ler_wMn2r n); rewrite mul0rn. Qed.

Lemma mulrn_wle0 x n : x <= 0 -> x *+ n <= 0.
Proof. by move=> /(ler_wMn2r n); rewrite mul0rn. Qed.

Lemma ler_wpMn2l x :
  0 <= x -> {homo (@GRing.natmul R x) : m n / (m <= n)%N >-> m <= n}.
Proof. by move=> xge0 m n /subnK <-; rewrite mulrnDr ler_wpDl ?mulrn_wge0. Qed.

Lemma ler_wnMn2l x :
  x <= 0 -> {homo (@GRing.natmul R x) : m n / (n <= m)%N >-> m <= n}.
Proof.
by move=> xle0 m n hmn /=; rewrite -lerN2 -!mulNrn ler_wpMn2l // oppr_cp0.
Qed.

(* TODO negative versions *)
Lemma mulrn_lgt0 x n : (0 < n)%N -> (0 < x) -> (0 < x *+ n).
Proof.
move=> + xgt0; elim: n => // n IHn _; rewrite mulrS (lt_le_trans xgt0)// lerDl.
by case: n IHn => // n /(_ _)/ltW->.
Qed.

Lemma pmulrIn x : x > 0 -> injective (GRing.natmul x).
Proof.
move=> x_neq0 m n /eqP; wlog lt_mn : m n / (m < n)%N => [hwlog|].
  by case: (ltngtP m n) => // [|+ /eqP/esym/eqP] => /hwlog/[apply].
by rewrite eq_sym -subr_eq0 -mulrnBr 1?ltnW// gt_eqF// mulrn_lgt0// subn_gt0.
Qed.

Lemma ler_pMn2l x :
  0 < x -> {mono (@GRing.natmul R x) : m n / (m <= n)%N >-> m <= n}.
Proof.
move=> x_gt0; apply: le_mono; elim=> [|m IHm] [|n]//= lt_mn.
 by rewrite mulr0n mulrn_lgt0.
by rewrite !mulrS ler_ltD// IHm.
Qed.

Lemma ltr_pMn2l x :
  0 < x -> {mono (@GRing.natmul R x) : m n / (m < n)%N >-> m < n}.
Proof. by move=> x_gt0; apply: leW_mono (ler_pMn2l _). Qed.

Lemma ler_nMn2l x :
  x < 0 -> {mono (@GRing.natmul R x) : m n / (n <= m)%N >-> m <= n}.
Proof. by move=> xlt0 m n /=; rewrite -lerN2 -!mulNrn ler_pMn2l// oppr_gt0. Qed.

Lemma ltr_nMn2l x :
  x < 0 -> {mono (@GRing.natmul R x) : m n / (n < m)%N >-> m < n}.
Proof. by move=> x_lt0; apply: leW_nmono (ler_nMn2l _). Qed.

Fact nneg_addr_closed : addr_closed (@Num.nneg R).
Proof. by split; [apply: lexx | apply: addr_ge0]. Qed.
HB.instance Definition _ := GRing.isAddClosed.Build R Rnneg_pred
  nneg_addr_closed.

Fact real_oppr_closed : oppr_closed (@Num.real R).
Proof. by move=> x; rewrite /= !realE oppr_ge0 orbC -!oppr_ge0 opprK. Qed.
HB.instance Definition _ := GRing.isOppClosed.Build R Rreal_pred
  real_oppr_closed.

Lemma real0 : 0%R \is @Num.real R. Proof. by rewrite qualifE/= lexx. Qed.
#[local] Hint Resolve real0 : core.

(* Comparability in a numDomain *)

Lemma comparable0r x : (0 >=< x)%R = (x \is Num.real). Proof. by []. Qed.

Lemma comparabler0 x : (x >=< 0)%R = (x \is Num.real).
Proof. by rewrite comparable_sym. Qed.

Lemma subr_comparable0 x y : (x - y >=< 0)%R = (x >=< y)%R.
Proof. by rewrite /Num.comparable subr_ge0 subr_le0. Qed.

Lemma comparablerE x y : (x >=< y)%R = (x - y \is Num.real).
Proof. by rewrite -comparabler0 subr_comparable0. Qed.

(* Properties of the real subset. *)

Lemma ger0_real x : 0 <= x -> x \is Num.real.
Proof. by rewrite realE => ->. Qed.

Lemma ler0_real x : x <= 0 -> x \is Num.real.
Proof. by rewrite realE orbC => ->. Qed.

Lemma gtr0_real x : 0 < x -> x \is Num.real. Proof. by move=> /ltW/ger0_real. Qed.

Lemma ltr0_real x : x < 0 -> x \is Num.real. Proof. by move=> /ltW/ler0_real. Qed.

Lemma big_real x0 op I (P : pred I) F (s : seq I) :
  {in Num.real &, forall x y, op x y \is Num.real} -> x0 \is Num.real ->
  {in P, forall i, F i \is Num.real} -> \big[op/x0]_(i <- s | P i) F i \is Num.real.
Proof. exact: comparable_bigr. Qed.

Lemma addr_min_max x y : min x y + max x y = x + y.
Proof. by rewrite /min /max; case: ifP => //; rewrite addrC. Qed.

Lemma addr_max_min x y : max x y + min x y = x + y.
Proof. by rewrite addrC addr_min_max. Qed.

Lemma minr_to_max x y : min x y = x + y - max x y.
Proof. by rewrite -[x + y]addr_min_max addrK. Qed.

Lemma maxr_to_min x y : max x y = x + y - min x y.
Proof. by rewrite -[x + y]addr_max_min addrK. Qed.

Lemma lteifNl C x y : - x < y ?<= if C = (- y < x ?<= if C).
Proof. by case: C; rewrite /= lterNl. Qed.

Lemma lteifNr C x y : x < - y ?<= if C = (y < - x ?<= if C).
Proof. by case: C; rewrite /= lterNr. Qed.

Lemma lteif0Nr C x : 0 < - x ?<= if C = (x < 0 ?<= if C).
Proof. by case: C; rewrite /= (oppr_ge0, oppr_gt0). Qed.

Lemma lteifNr0 C x : - x < 0 ?<= if C = (0 < x ?<= if C).
Proof. by case: C; rewrite /= (oppr_le0, oppr_lt0). Qed.

Lemma lteifN2 C : {mono -%R : x y /~ x < y ?<= if C :> R}.
Proof. by case: C => ? ?; rewrite /= lterN2. Qed.

Definition lteif_oppE := (lteif0Nr, lteifNr0, lteifN2).

Lemma lteifD2l C x : {mono +%R x : y z / y < z ?<= if C}.
Proof. by case: C => ? ?; rewrite /= lterD2. Qed.

Lemma lteifD2r C x : {mono +%R^~ x : y z / y < z ?<= if C}.
Proof. by case: C => ? ?; rewrite /= lterD2. Qed.

Definition lteifD2 := (lteifD2l, lteifD2r).

Lemma lteifBlDr C x y z : (x - y < z ?<= if C) = (x < z + y ?<= if C).
Proof. by case: C; rewrite /= lterBDr. Qed.

Lemma lteifBrDr C x y z : (x < y - z ?<= if C) = (x + z < y ?<= if C).
Proof. by case: C; rewrite /= lterBDr. Qed.

Definition lteifBDr := (lteifBlDr, lteifBrDr).

Lemma lteifBlDl C x y z : (x - y < z ?<= if C) = (x < y + z ?<= if C).
Proof. by case: C; rewrite /= lterBDl. Qed.

Lemma lteifBrDl C x y z : (x < y - z ?<= if C) = (z + x < y ?<= if C).
Proof. by case: C; rewrite /= lterBDl. Qed.

Definition lteifBDl := (lteifBlDl, lteifBrDl).

End porderZmodTypeTheory.

#[global]
Hint Extern 0 (is_true (0 \is Num.real)) => solve [apply: real0] : core.
#[global] Hint Resolve lerN2 ltrN2 : core.

Arguments real0 {R}.
Arguments lerN2 {R}.
Arguments ltrN2 {R}.

Section NumZmoduleTheory.
Variable (R : numZmodType).
Implicit Types (x y : R).

Lemma comparabler_trans : transitive (Num.comparable : rel R).
Proof. exact: comparabler_trans. Qed.

Lemma ger_leVge x y : 0 <= x -> 0 <= y -> (x <= y) || (y <= x).
Proof.
by move=> /ge_comparable + /le_comparable => /comparabler_trans/[apply].
Qed.

Fact real_addr_closed : addr_closed (@Num.real R).
Proof.
split=> [|x y Rx Ry]; first by rewrite realE lexx.
without loss{Rx} x_ge0: x y Ry / 0 <= x.
  case/orP: Rx => [? | x_le0]; first exact.
  by rewrite -rpredN opprD; apply; rewrite ?rpredN ?oppr_ge0.
case/orP: Ry => [y_ge0 | y_le0]; first by rewrite realE -nnegrE rpredD.
by rewrite realE -[y]opprK orbC -oppr_ge0 opprB !subr_ge0 ger_leVge ?oppr_ge0.
Qed.
HB.instance Definition _ := GRing.isAddClosed.Build R Rreal_pred
  real_addr_closed.

Lemma ler_leVge x y : x <= 0 -> y <= 0 -> (x <= y) || (y <= x).
Proof. by rewrite -!oppr_ge0 => /(ger_leVge _) /[apply]; rewrite !lerN2. Qed.

Lemma real_leVge x y : x \is Num.real -> y \is Num.real -> (x <= y) || (y <= x).
Proof. by rewrite -comparabler0 -comparable0r => /comparabler_trans P/P. Qed.

Lemma real_comparable x y : x \is Num.real -> y \is Num.real -> x >=< y.
Proof. exact: real_leVge. Qed.

Lemma realB : {in Num.real &, forall x y, x - y \is Num.real}.
Proof. exact: rpredB. Qed.

Lemma realN : {mono (@GRing.opp R) : x / x \is Num.real}.
Proof. exact: rpredN. Qed.

Lemma realBC x y : (x - y \is Num.real) = (y - x \is Num.real).
Proof. exact: rpredBC. Qed.

Lemma realD : {in Num.real &, forall x y, x + y \is Num.real}.
Proof. exact: rpredD. Qed.


(* TODO: should work for semiring *)
(* Lemma real1 : 1%R \is @real R. Proof. exact: rpred1. Qed. *)
(* Lemma realn n : n%:R \is @real R. Proof. exact: rpred_nat. Qed. *)
(* #[local] Hint Resolve real0 real1 : core. *)

Lemma sum_real I (P : pred I) (F : I -> R) (s : seq I) :
  {in P, forall i, F i \is Num.real} -> \sum_(i <- s | P i) F i \is Num.real.
Proof. by apply/big_real; [apply: rpredD | apply: rpred0]. Qed.

(* dichotomy and trichotomy *)

Lemma zmod_leP x y : x \is Num.real -> y \is Num.real ->
  Order.le_xor_gt x y (min y x) (min x y) (max y x) (max x y)
                 (x <= y) (y < x).
Proof. by move=> xR yR; apply: comparable_leP; exact: real_leVge. Qed.

Lemma zmod_ltP x y : x \is Num.real -> y \is Num.real ->
  Order.lt_xor_ge x y (min y x) (min x y) (max y x) (max x y)
             (y <= x) (x < y).
Proof. by move=> xR yR; apply: comparable_ltP; exact: real_leVge. Qed.

Lemma zmod_ltgtP x y : x \is Num.real -> y \is Num.real ->
  Order.compare x y (min y x) (min x y) (max y x) (max x y)
               (y == x) (x == y) (x >= y) (x <= y) (x > y) (x < y).
Proof. by move=> xR yR; apply: comparable_ltgtP; exact: real_leVge. Qed.

Lemma real_ltNge : {in real &, forall x y, (x < y) = ~~ (y <= x)}.
Proof. by move=> x y xR yR /=; case: zmod_leP. Qed.

Lemma real_leNgt : {in real &, forall x y, (x <= y) = ~~ (y < x)}.
Proof. by move=> x y xR yR /=; case: zmod_leP. Qed.

Variant ger0_xor_lt0 (x : R) : R -> R -> R -> R ->
    bool -> bool -> Set :=
  | Ger0NotLt0 of 0 <= x : ger0_xor_lt0 x 0 0 x x  false true
  | Ltr0NotGe0 of x < 0  : ger0_xor_lt0 x x x 0 0 true false.

Variant ler0_xor_gt0 (x : R) : R -> R -> R -> R ->
   bool -> bool -> Set :=
  | Ler0NotLe0 of x <= 0 : ler0_xor_gt0 x x x 0 0 false true
  | Gtr0NotGt0 of 0 < x  : ler0_xor_gt0 x 0 0 x x true false.

Variant comparer0 x : R -> R -> R -> R ->
    bool -> bool -> bool -> bool -> bool -> bool -> Set :=
  | ComparerGt0 of 0 < x : comparer0 x 0 0 x x false false false true false true
  | ComparerLt0 of x < 0 : comparer0 x x x 0 0 false false true false true false
  | ComparerEq0 of x = 0 : comparer0 x 0 0 0 0 true true true true false false.

Lemma zmod_ge0P x : x \is Num.real -> ger0_xor_lt0 x
   (min 0 x) (min x 0) (max 0 x) (max x 0) (x < 0) (0 <= x).
Proof.
move=> hx; case: comparable_leP;
by rewrite ?subr0 ?sub0r //; constructor.
Qed.

Lemma zmod_le0P x : x \is Num.real -> ler0_xor_gt0 x
  (min 0 x) (min x 0) (max 0 x) (max x 0)
  (0 < x) (x <= 0).
Proof.
move=> hx; case: comparable_ltP;
by rewrite ?subr0 ?sub0r //; constructor.
Qed.

Lemma zmod_ltgt0P x : x \is Num.real ->
  comparer0 x (min 0 x) (min x 0) (max 0 x) (max x 0)
            (0 == x) (x == 0) (x <= 0) (0 <= x) (x < 0) (x > 0).
Proof.
move=> hx; case: (@comparable_ltgtP _ _ 0 x);
by rewrite ?subr0 ?sub0r //; constructor.
Qed.

Lemma max_real : {in real &, forall x y, max x y \is Num.real}.
Proof. exact: comparable_maxr. Qed.

Lemma min_real : {in real &, forall x y, min x y \is Num.real}.
Proof. exact: comparable_minr. Qed.

Lemma bigmax_real I x0 (r : seq I) (P : pred I) (f : I -> R):
  x0 \is Num.real -> {in P, forall i : I, f i \is Num.real} ->
  \big[max/x0]_(i <- r | P i) f i \is Num.real.
Proof. exact/big_real/max_real. Qed.

Lemma bigmin_real I x0 (r : seq I) (P : pred I) (f : I -> R):
  x0 \is Num.real -> {in P, forall i : I, f i \is Num.real} ->
  \big[min/x0]_(i <- r | P i) f i \is Num.real.
Proof. exact/big_real/min_real. Qed.

Lemma real_neqr_lt : {in real &, forall x y, (x != y) = (x < y) || (y < x)}.
Proof. by move=> * /=; case: zmod_ltgtP. Qed.

Lemma lerB_real x y : x <= y -> y - x \is Num.real.
Proof. by move=> le_xy; rewrite ger0_real // subr_ge0. Qed.

Lemma gerB_real x y : x <= y -> x - y \is Num.real.
Proof. by move=> le_xy; rewrite ler0_real // subr_le0. Qed.

Lemma ler_real y x : x <= y -> (x \is Num.real) = (y \is Num.real).
Proof. by move=> le_xy; rewrite -(addrNK x y) rpredDl ?lerB_real. Qed.

Lemma ger_real x y : y <= x -> (x \is Num.real) = (y \is Num.real).
Proof. by move=> le_yx; rewrite -(ler_real le_yx). Qed.

Lemma Nreal_leF x y : y \is Num.real -> x \notin real -> (x <= y) = false.
Proof. by move=> yR; apply: contraNF=> /ler_real->. Qed.

Lemma Nreal_geF x y : y \is Num.real -> x \notin real -> (y <= x) = false.
Proof. by move=> yR; apply: contraNF=> /ger_real->. Qed.

Lemma Nreal_ltF x y : y \is Num.real -> x \notin real -> (x < y) = false.
Proof. by move=> yR xNR; rewrite lt_def Nreal_leF ?andbF. Qed.

Lemma Nreal_gtF x y : y \is Num.real -> x \notin real -> (y < x) = false.
Proof. by move=> yR xNR; rewrite lt_def Nreal_geF ?andbF. Qed.

(* real wlog *)

Lemma real_wlog_ler P :
    (forall a b, P b a -> P a b) -> (forall a b, a <= b -> P a b) ->
  forall a b : R, a \is Num.real -> b \is Num.real -> P a b.
Proof.
move=> sP hP a b ha hb; wlog: a b ha hb / a <= b => [hwlog|]; last exact: hP.
by case: (@zmod_leP a b)=> // [/hP //|/ltW hba]; apply/sP/hP.
Qed.

Lemma real_wlog_ltr P :
    (forall a, P a a) -> (forall a b, (P b a -> P a b)) ->
    (forall a b, a < b -> P a b) ->
  forall a b : R, a \is Num.real -> b \is Num.real -> P a b.
Proof.
move=> rP sP hP; apply: real_wlog_ler=> // a b.
by rewrite le_eqVlt; case: eqVneq => [->|] //= _ /hP.
Qed.


Lemma real_oppr_max : {in real &, {morph -%R : x y / max x y >-> min x y : R}}.
Proof.
by move=> x y xr yr; rewrite !(fun_if, if_arg) ltrN2; case: zmod_ltgtP => // ->.
Qed.

Lemma real_oppr_min : {in real &, {morph -%R : x y / min x y >-> max x y : R}}.
Proof.
by move=> x y xr yr; rewrite -[RHS]opprK real_oppr_max ?realN// !opprK.
Qed.

Lemma real_addr_minl : {in real & real & real, @left_distributive R R +%R min}.
Proof.
by move=> x y z xr yr zr; case: (@zmod_leP (_ + _)); rewrite ?rpredD//;
   rewrite lterD2; case: zmod_leP.
Qed.

Lemma real_addr_minr : {in real & real & real, @right_distributive R R +%R min}.
Proof. by move=> x y z xr yr zr; rewrite !(addrC x) real_addr_minl. Qed.

Lemma real_addr_maxl : {in real & real & real, @left_distributive R R +%R max}.
Proof.
by move=> x y z xr yr zr; case: (@zmod_leP (_ + _)); rewrite ?realD//;
   rewrite lterD2; case: zmod_leP.
Qed.

Lemma real_addr_maxr : {in real & real & real, @right_distributive R R +%R max}.
Proof. by move=> x y z xr yr zr; rewrite !(addrC x) real_addr_maxl. Qed.

End NumZmoduleTheory.

Arguments comparabler_trans {_ _ _ _}.

Section OrderedZmodMonotonyTheoryForReals.
Local Open Scope order_scope.

Variables (R R' : numZmodType) (D : pred R) (f : R -> R') (f' : R -> nat).
Implicit Types (m n p : nat) (x y z : R) (u v w : R').

Lemma real_mono :
  {homo f : x y / x < y} -> {in real &, {mono f : x y / x <= y}}.
Proof.
move=> mf x y xR yR /=; have [lt_xy | le_yx] := zmod_leP xR yR.
  by rewrite ltW_homo.
by rewrite lt_geF ?mf.
Qed.

Lemma real_nmono :
  {homo f : x y /~ x < y} -> {in real &, {mono f : x y /~ x <= y}}.
Proof.
move=> mf x y xR yR /=; have [lt_xy|le_yx] := zmod_ltP xR yR.
  by rewrite lt_geF ?mf.
by rewrite ltW_nhomo.
Qed.

Lemma real_mono_in :
    {in D &, {homo f : x y / x < y}} ->
  {in [pred x in D | x \is real] &, {mono f : x y / x <= y}}.
Proof.
move=> Dmf x y /andP[hx xR] /andP[hy yR] /=.
have [lt_xy|le_yx] := zmod_leP xR yR; first by rewrite (ltW_homo_in Dmf).
by rewrite lt_geF ?Dmf.
Qed.

Lemma real_nmono_in :
    {in D &, {homo f : x y /~ x < y}} ->
  {in [pred x in D | x \is real] &, {mono f : x y /~ x <= y}}.
Proof.
move=> Dmf x y /andP[hx xR] /andP[hy yR] /=.
have [lt_xy|le_yx] := zmod_ltP xR yR; last by rewrite (ltW_nhomo_in Dmf).
by rewrite lt_geF ?Dmf.
Qed.

Lemma realn_mono : {homo f' : x y / x < y >-> (x < y)} ->
  {in real &, {mono f' : x y / x <= y >-> (x <= y)}}.
Proof.
move=> mf x y xR yR /=; have [lt_xy | le_yx] := zmod_leP xR yR.
  by rewrite ltW_homo.
by rewrite lt_geF ?mf.
Qed.

Lemma realn_nmono : {homo f' : x y / y < x >-> (x < y)} ->
  {in real &, {mono f' : x y / y <= x >-> (x <= y)}}.
Proof.
move=> mf x y xR yR /=; have [lt_xy|le_yx] := zmod_ltP xR yR.
  by rewrite lt_geF ?mf.
by rewrite ltW_nhomo.
Qed.

Lemma realn_mono_in : {in D &, {homo f' : x y / x < y >-> (x < y)}} ->
  {in [pred x in D | x \is real] &, {mono f' : x y / x <= y >-> (x <= y)}}.
Proof.
move=> Dmf x y /andP[hx xR] /andP[hy yR] /=.
have [lt_xy|le_yx] := zmod_leP xR yR; first by rewrite (ltW_homo_in Dmf).
by rewrite lt_geF ?Dmf.
Qed.

Lemma realn_nmono_in : {in D &, {homo f' : x y / y < x >-> (x < y)}} ->
  {in [pred x in D | x \is real] &, {mono f' : x y / y <= x >-> (x <= y)}}.
Proof.
move=> Dmf x y /andP[hx xR] /andP[hy yR] /=.
have [lt_xy|le_yx] := zmod_ltP xR yR; last by rewrite (ltW_nhomo_in Dmf).
by rewrite lt_geF ?Dmf.
Qed.

End OrderedZmodMonotonyTheoryForReals.
End Theory.

Module Exports. HB.reexport. End Exports.
End Num.
Export Num.Syntax Num.Exports.
