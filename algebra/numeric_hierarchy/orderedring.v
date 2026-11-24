(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype bigop finset fingroup nmodule order.
From mathcomp Require Import rings_modules_and_algebras divalg orderedzmod.

(******************************************************************************)
(*                Ordered ring structures (orderedring.v)                     *)
(*                                                                            *)
(* NB: See CONTRIBUTING.md for an introduction to HB concepts and commands.   *)
(*                                                                            *)
(* NB: The header of ssrnum.v explains how to use the files in this directory.*)
(*                                                                            *)
(* This file defines the following ordered ring structures:                   *)
(*                                                                            *)
(*         porderRingType == join of Order.POrder and GRing.Ring              *)
(*                           The HB class is called POrderRing.               *)
(*          orderRingType == join of Order.Order and GRing.Ring               *)
(*                           The HB class is called OrderRing.                *)
(*       porderedRingType == porderRingType such that a product of            *)
(*                           nonnegative elements is nonnegative.             *)
(*                           The HB class is called POrderedRing.             *)
(*     porderedNzRingType == join of POrderedRing and GRing.NzRing.           *)
(*                           The HB class is called POrderedNzRing.           *)
(*        orderedRingType == orderRingType such that a product of             *)
(*                           nonnegative elements is nonnegative.             *)
(*                           The HB class is called OrderedRing.              *)
(* strictPOrderedRingType == porderNzRingType such that a product of          *)
(*                           positive elements is positive.                   *)
(*                           The HB class is called StrictPOrderedRing.       *)
(*    numPOrderedRingType == strictPOrderedRingType such that the real line   *)
(*                           is totally ordered and if any two of x, y, x * y *)
(*                           are real, then the third one is real as well.    *)
(*                           The HB class is called NumPOrderedRing.          *)
(*  strictOrderedRingType == orderNzRingType such that a product of           *)
(*                           positive elements is positive.                   *)
(*                           The HB class is called StrictOrderedRing.        *)
(*    porderedIdomainType == join of StrictPOrderedRing and                   *)
(*                           GRing.IntegralDomain.                            *)
(*                           The HB class is called POrderedIntegralDomain.   *)
(* numPOrderedIdomainType == join of NumPOrderedRing and GRing.IntegralDomain.*)
(*                           The HB class is called NumPOrderedIntegralDomain.*)
(*     orderedIdomainType == join of StrictOrderedRing and                    *)
(*                           GRing.IntegralDomain.                            *)
(*                           The HB class is called OrderedIntegralDomain.    *)
(*                                                                            *)
(* Over these structures, we have the following operations:                   *)
(*         Num.sg x == sign of x: equal to 0 iff x = 0, to 1 iff x > 0, and   *)
(*                     to -1 in all other cases (including x < 0)             *)
(*                                                                            *)
(* - list of prefixes :                                                       *)
(*   p : positive                                                             *)
(*   n : negative                                                             *)
(*   sp : strictly positive                                                   *)
(*   sn : strictly negative                                                   *)
(*   i : interior = in [0, 1] or ]0, 1[                                       *)
(*   e : exterior = in [1, +oo[ or ]1; +oo[                                   *)
(*   w : non strict (weak) monotony                                           *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Import Order.Theory GRing.Theory Num.Def orderedzmod.Num.

Module Num.

(**************)
(* STRUCTURES *)
(**************)

#[short(type="porderRingType")]
HB.structure Definition POrderRing :=
  { R of GRing.Ring R & Num.POrderZmodule R }.

#[short(type="orderRingType")]
HB.structure Definition OrderRing :=
  { R of GRing.Ring R & Num.OrderZmodule R }.

HB.mixin Record Ring_isPOrdered R & POrderRing R := {
  ler01 : 0 <= 1 :> R;
  mulr_ge0 : forall x y : R, 0 <= x -> 0 <= y -> 0 <= x * y
}.

#[short(type="porderedRingType")]
HB.structure Definition POrderedRing :=
  { R of GRing.Ring R & Num.POrderedZmodule R & Ring_isPOrdered R }.

#[short(type="porderedNzRingType")]
HB.structure Definition POrderedNzRing :=
  { R of GRing.NzRing R & Num.POrderedZmodule R & Ring_isPOrdered R }.

#[short(type="orderedRingType")]
HB.structure Definition OrderedRing :=
  { R of GRing.Ring R & Num.OrderedZmodule R & Ring_isPOrdered R }.

#[short(type="orderedNzRingType")]
HB.structure Definition OrderedNzRing :=
  { R of GRing.NzRing R & Num.OrderedZmodule R & Ring_isPOrdered R }.

HB.mixin Record POrderRing_isStrictPOrdered R & POrderRing R := {
  mulr_gt0 : forall x y : R, 0 < x -> 0 < y -> 0 < x * y
}.

#[short(type="strictPOrderedRingType")]
HB.structure Definition StrictPOrderedRing :=
  { R of POrderedRing R & GRing.NzRing R & POrderRing_isStrictPOrdered R }.

HB.mixin Record Ring_hasNumMul R & POrderRing R := {
  realMr : forall x y : R,
    x != 0 -> x \is real -> (x * y \is real) = (y \is real);
  realrM : forall x y : R,
    y != 0 -> y \is real -> (x * y \is real) = (x \is real);
}.

#[short(type="numPOrderedRingType")]
HB.structure Definition NumPOrderedRing :=
  { R of StrictPOrderedRing R
      & POrderedZmodule_hasTransCmp R & Ring_hasNumMul R }.

#[short(type="strictOrderedRingType")]
HB.structure Definition StrictOrderedRing :=
  { R of NumPOrderedRing R & Order.Total _ R }.

#[short(type="porderedIdomainType")]
HB.structure Definition POrderedIntegralDomain :=
  { R of StrictPOrderedRing R & GRing.IntegralDomain R }.

#[short(type="numPOrderedIdomainType")]
HB.structure Definition NumPOrderedIntegralDomain :=
  { R of POrderedIntegralDomain R
      & POrderedZmodule_hasTransCmp R & Ring_hasNumMul R }.

#[short(type="orderedIdomainType")]
HB.structure Definition OrderedIntegralDomain :=
  { R of NumPOrderedIntegralDomain R & StrictOrderedRing R }.

Module OrderedRingExports.
Bind Scope ring_scope with
  POrderRing.sort OrderRing.sort POrderedRing.sort POrderedNzRing.sort
  OrderedRing.sort OrderedNzRing.sort StrictPOrderedRing.sort
  NumPOrderedRing.sort StrictOrderedRing.sort POrderedIntegralDomain.sort
  NumPOrderedIntegralDomain.sort OrderedIntegralDomain.sort.
End OrderedRingExports.
HB.export OrderedRingExports.

Module Export Def.

Export Num.Def.

Section POrderRingDef.
Context {R : porderRingType}.

Definition sgr (x : R) : R := if x == 0 then 0 else if x < 0 then -1 else 1.

End POrderRingDef.

End Def.

Notation sg := sgr.

(**********)
(* THEORY *)
(**********)

Module Export Theory.

Export Num.Theory.

Section pordered_theory.
Context (R : porderedRingType).
Implicit Types x y : R.

Lemma ler01 : 0 <= 1 :> R.
Proof. exact: ler01. Qed.
Lemma mulr_ge0 x y : 0 <= x -> 0 <= y -> 0 <= x * y.
Proof. exact: mulr_ge0. Qed.

Lemma mulr_ge0_le0 (x y : R) : 0 <= x -> y <= 0 -> x * y <= 0.
Proof.
by rewrite -oppr_ge0 => /mulr_ge0 /[apply]; rewrite mulrN oppr_ge0.
Qed.

Lemma mulr_le0_ge0 (x y : R) : x <= 0 -> 0 <= y -> x * y <= 0.
Proof.
by rewrite -oppr_ge0 => /mulr_ge0 /[apply]; rewrite mulNr oppr_ge0.
Qed.

Lemma mulr_le0 (x y : R) : x <= 0 -> y <= 0 -> 0 <= x * y.
Proof.
by rewrite -!oppr_ge0 => /mulr_ge0 /[apply]; rewrite mulrNN.
Qed.

Local Fact nneg_mulr_closed : mulr_closed (@nneg R).
Proof.
by split=> [|x y]; [ rewrite nnegrE ler01 | exact: mulr_ge0 ].
Qed.
#[export]
HB.instance Definition _ := GRing.isMulClosed.Build R nneg_num_pred
  nneg_mulr_closed.

Local Fact real_mulr_closed : mulr_closed (@real R).
Proof.
split=> [|x y]; first by rewrite realE ler01.
rewrite !realE => /orP[] x0 /orP[] y0; apply/orP.
- by left; apply: mulr_ge0.
- by right; apply: mulr_ge0_le0.
- by right; apply: mulr_le0_ge0.
- by left; apply: mulr_le0.
Qed.
#[export]
HB.instance Definition _ := GRing.isMulClosed.Build R real_num_pred
  real_mulr_closed.

Lemma ler0n n : 0 <= n%:R :> R.
Proof. by apply: mulrn_wge0; exact: ler01. Qed.

Local Hint Extern 0 (is_true (@Order.le ring_display _ _ _)) =>
  solve [apply: ler01 | apply: ler0n] : core.

Lemma lerN10 : -1 <= 0 :> R. Proof. by rewrite oppr_le0. Qed.

Lemma ler_wpM2l x : 0 <= x -> {homo *%R x : y z / y <= z}.
Proof.
by move=> x_ge0 y z yz; rewrite -subr_ge0 -mulrBr mulr_ge0 // subr_ge0.
Qed.

Lemma ler_wpM2r x : 0 <= x -> {homo *%R^~ x : y z / y <= z}.
Proof.
by move=> x_ge0 y z yz; rewrite -subr_ge0 -mulrBl mulr_ge0 // subr_ge0.
Qed.

Lemma ler_wnM2l x : x <= 0 -> {homo *%R x : y z /~ y <= z}.
Proof. by move=> x_le0 y z leyz; rewrite -![x * _]mulrNN ler_wpM2l ?lterNE. Qed.

Lemma ler_wnM2r x : x <= 0 -> {homo *%R^~ x : y z /~ y <= z}.
Proof. by move=> x_le0 y z leyz; rewrite -![_ * x]mulrNN ler_wpM2r ?lterNE. Qed.

(* Binary forms, for backchaining. *)

Lemma ler_pM x1 y1 x2 y2 :
  0 <= x1 -> 0 <= x2 -> x1 <= y1 -> x2 <= y2 -> x1 * x2 <= y1 * y2.
Proof.
move=> x1ge0 x2ge0 le_xy1 le_xy2; have y1ge0 := le_trans x1ge0 le_xy1.
exact: le_trans (ler_wpM2r x2ge0 le_xy1) (ler_wpM2l y1ge0 le_xy2).
Qed.

Lemma real1 : 1 \is @real R. Proof. exact: rpred1. Qed.
Lemma realn n : n%:R \is @real R.
Proof. by rewrite ger0_real ?ler0n. Qed.
#[local] Hint Resolve real1 : core.

Lemma prodr_ge0 I r (P : pred I) (E : I -> R) :
  (forall i, P i -> 0 <= E i) -> 0 <= \prod_(i <- r | P i) E i.
Proof. by move=> Ege0; rewrite -nnegrE rpred_prod. Qed.

Lemma prod_real I (P : pred I) (F : I -> R) (s : seq I) :
  {in P, forall i, F i \is real} -> \prod_(i <- s | P i) F i \is real.
Proof. by apply/big_real; [apply: rpredM | apply: rpred1]. Qed.

Lemma ler_prod I r (P : pred I) (E1 E2 : I -> R) :
    (forall i, P i -> 0 <= E1 i <= E2 i) ->
  \prod_(i <- r | P i) E1 i <= \prod_(i <- r | P i) E2 i.
Proof.
move=> leE12; elim/(big_load (fun x => 0 <= x)): _.
elim/big_rec2: _ => // i x2 x1 /leE12/andP[le0Ei leEi12] [x1ge0 le_x12].
by rewrite mulr_ge0 // ler_pM.
Qed.

Lemma ler_peMl x y : 0 <= y -> 1 <= x -> y <= x * y.
Proof. by move=> hy hx; rewrite -{1}[y]mul1r ler_wpM2r. Qed.

Lemma ler_neMl x y : y <= 0 -> 1 <= x -> x * y <= y.
Proof. by move=> hy hx; rewrite -{2}[y]mul1r ler_wnM2r. Qed.

Lemma ler_peMr x y : 0 <= y -> 1 <= x -> y <= y * x.
Proof. by move=> hy hx; rewrite -{1}[y]mulr1 ler_wpM2l. Qed.

Lemma ler_neMr x y : y <= 0 -> 1 <= x -> y * x <= y.
Proof. by move=> hy hx; rewrite -{2}[y]mulr1 ler_wnM2l. Qed.

Lemma ler_piMl x y : 0 <= y -> x <= 1 -> x * y <= y.
Proof. by move=> hy hx; rewrite -{2}[y]mul1r ler_wpM2r. Qed.

Lemma ler_niMl x y : y <= 0 -> x <= 1 -> y <= x * y.
Proof. by move=> hy hx; rewrite -{1}[y]mul1r ler_wnM2r. Qed.

Lemma ler_piMr x y : 0 <= y -> x <= 1 -> y * x <= y.
Proof. by move=> hy hx; rewrite -{2}[y]mulr1 ler_wpM2l. Qed.

Lemma ler_niMr x y : y <= 0 -> x <= 1 -> y <= y * x.
Proof. by move=> hx hy; rewrite -{1}[y]mulr1 ler_wnM2l. Qed.

Lemma mulr_ile1 x y : 0 <= x -> 0 <= y -> x <= 1 -> y <= 1 -> x * y <= 1.
Proof. by move=> *; rewrite (@le_trans _ _ y) ?ler_piMl. Qed.

Lemma prodr_ile1 {I : Type} (s : seq I) (P : pred I) (F : I -> R) :
  (forall i, P i -> 0 <= F i <= 1) -> \prod_(j <- s | P j) F j <= 1.
Proof.
elim: s => [_ | y s ih xs01]; rewrite ?big_nil// big_cons.
case: ifPn => Py; last by rewrite ih.
have /andP[y0 y1] : 0 <= F y <= 1 by rewrite xs01// mem_head.
rewrite mulr_ile1 ?andbT//; last first.
  by rewrite ih// => e xs; rewrite xs01// in_cons xs orbT.
by rewrite prodr_ge0// => x /xs01 /andP[].
Qed.

Lemma mulr_ilt1 x y : 0 <= x -> 0 <= y -> x < 1 -> y < 1 -> x * y < 1.
Proof. by move=> *; rewrite (@le_lt_trans _ _ y) ?ler_piMl // ltW. Qed.

Definition mulr_ilte1 := (mulr_ile1, mulr_ilt1).

Lemma mulr_ege1 x y : 1 <= x -> 1 <= y -> 1 <= x * y.
Proof.
by move=> le1x le1y; rewrite (@le_trans _ _ y) ?ler_peMl // (le_trans ler01).
Qed.

Lemma exprn_ge0 n x : 0 <= x -> 0 <= x ^+ n.
Proof. by move=> xge0; rewrite -nnegrE rpredX. Qed.

Lemma realX n : {in real, forall x, x ^+ n \is real}.
Proof. exact: rpredX. Qed.

Lemma exprn_ile1 n x : 0 <= x -> x <= 1 -> x ^+ n <= 1.
Proof.
move=> xge0 xle1; elim: n=> [|*]; rewrite ?expr0 // exprS.
by rewrite mulr_ile1 ?exprn_ge0.
Qed.

Lemma exprn_ege1 n x : 1 <= x -> 1 <= x ^+ n.
Proof.
by move=> x_ge1; elim: n=> [|n ihn]; rewrite ?expr0 // exprS mulr_ege1.
Qed.

Lemma ler_iXnr x n : (0 < n)%N -> 0 <= x -> x <= 1 -> x ^+ n <= x.
Proof. by case: n => n // *; rewrite exprS ler_piMr // exprn_ile1. Qed.

Lemma ler_eXnr x n : (0 < n)%N -> 1 <= x -> x <= x ^+ n.
Proof.
case: n => // n _ x_ge1.
by rewrite exprS ler_peMr ?(le_trans _ x_ge1) // exprn_ege1.
Qed.

Lemma ler_wiXn2l x :
  0 <= x -> x <= 1 -> {homo GRing.exp x : m n / (n <= m)%N >-> m <= n}.
Proof.
move=> xge0 xle1 m n /= hmn.
by rewrite -(subnK hmn) exprD ler_piMl ?(exprn_ge0, exprn_ile1).
Qed.

Lemma ler_weXn2l x : 1 <= x -> {homo GRing.exp x : m n / (m <= n)%N >-> m <= n}.
Proof.
move=> xge1 m n /= hmn; rewrite -(subnK hmn) exprD.
by rewrite ler_peMl ?(exprn_ge0, exprn_ege1) // (le_trans _ xge1) ?ler01.
Qed.

Lemma real_expr2_ge0 x : x \is real -> 0 <= x ^+ 2.
Proof.
by rewrite realE expr2 => /orP[] x0; [apply: mulr_ge0|apply: mulr_le0].
Qed.

Lemma real_exprn_even_ge0 n x : x \is real -> ~~ odd n -> 0 <= x ^+ n.
Proof.
by move=> xR /even_halfK <-; rewrite -muln2 exprM real_expr2_ge0 // rpredX.
Qed.

Lemma real_exprn_even_lt0 n x :
  x \is real -> ~~ odd n -> (x ^+ n < 0) = false.
Proof. by move=> xR n_even; rewrite le_gtF // real_exprn_even_ge0. Qed.

Lemma sgr_def x : sg x = (-1) ^+ (x < 0)%R *+ (x != 0).
Proof. by rewrite /sg; do 2!case: ifP => //. Qed.

Lemma neqr0_sign x : x != 0 -> (-1) ^+ (x < 0)%R = sgr x.
Proof. by rewrite sgr_def  => ->. Qed.

Lemma gtr0_sg x : 0 < x -> sg x = 1.
Proof. by move=> x_gt0; rewrite /sg gt_eqF // lt_gtF. Qed.

Lemma ltr0_sg x : x < 0 -> sg x = -1.
Proof. by move=> x_lt0; rewrite /sg x_lt0 lt_eqF. Qed.

Lemma sgr0 : sg 0 = 0 :> R. Proof. by rewrite /sgr eqxx. Qed.

Lemma sqr_sg x : sg x ^+ 2 = (x != 0)%:R.
Proof. by rewrite sgr_def exprMn_n sqrr_sign -mulnn mulnb andbb. Qed.

Lemma sgr_odd n x : x != 0 -> (sg x) ^+ n = (sg x) ^+ (odd n).
Proof. by rewrite /sg; do 2!case: ifP => // _; rewrite ?expr1n ?signr_odd. Qed.

Lemma leifBLR x y z C : (x - y <= z ?= iff C) = (x <= z + y ?= iff C).
Proof. by rewrite /leif !eq_le lerBlDr lerBrDr. Qed.

Lemma leifBRL x y z C : (x <= y - z ?= iff C) = (x + z <= y ?= iff C).
Proof. by rewrite -leifBLR opprK. Qed.

Lemma leifD x1 y1 C1 x2 y2 C2 :
    x1 <= y1 ?= iff C1 -> x2 <= y2 ?= iff C2 ->
  x1 + x2 <= y1 + y2 ?= iff C1 && C2.
Proof.
rewrite -(mono_leif (C := C1) (lerD2r x2)).
rewrite -(mono_leif (C := C2) (lerD2l y1)).
exact: leif_trans.
Qed.

Lemma leif_sum (I : finType) (P C : pred I) (E1 E2 : I -> R) :
    (forall i, P i -> E1 i <= E2 i ?= iff C i) ->
  \sum_(i | P i) E1 i <= \sum_(i | P i) E2 i ?= iff [forall (i | P i), C i].
Proof.
move=> leE12; rewrite -big_andE.
elim/big_rec3: _ => [|i Ci m2 m1 /leE12]; first by rewrite /leif lexx eqxx.
exact: leifD.
Qed.

Lemma leif_0_sum (I : finType) (P C : pred I) (E : I -> R) :
    (forall i, P i -> 0 <= E i ?= iff C i) ->
  0 <= \sum_(i | P i) E i ?= iff [forall (i | P i), C i].
Proof. by move/leif_sum; rewrite big1_eq. Qed.

(* lteif *)

Lemma subr_lteifr0 C x y : (y - x < 0 ?<= if C) = (y < x ?<= if C).
Proof. by case: C => /=; rewrite subr_lte0. Qed.

Lemma subr_lteif0r C x y : (0 < y - x ?<= if C) = (x < y ?<= if C).
Proof. by case: C => /=; rewrite subr_gte0. Qed.

Definition subr_lteif0 := (subr_lteifr0, subr_lteif0r).

Lemma mem0_itvcc_xNx x : (0 \in `[- x, x]) = (0 <= x).
Proof. by rewrite itv_boundlr [in LHS]/<=%O /= oppr_le0 andbb. Qed.

Lemma mem0_itvoo_xNx x : (0 \in `]- x, x[) = (0 < x).
Proof. by rewrite itv_boundlr [in LHS]/<=%O /= oppr_lt0 andbb. Qed.

Lemma oppr_itv ba bb (xa xb x : R) :
  (- x \in Interval (BSide ba xa) (BSide bb xb)) =
  (x \in Interval (BSide (~~ bb) (- xb)) (BSide (~~ ba) (- xa))).
Proof.
by rewrite !itv_boundlr /<=%O /= !implybF negbK andbC lteifNl lteifNr.
Qed.

Lemma oppr_itvoo (a b x : R) : (- x \in `]a, b[) = (x \in `]- b, - a[).
Proof. exact: oppr_itv. Qed.

Lemma oppr_itvco (a b x : R) : (- x \in `[a, b[) = (x \in `]- b, - a]).
Proof. exact: oppr_itv. Qed.

Lemma oppr_itvoc (a b x : R) : (- x \in `]a, b]) = (x \in `[- b, - a[).
Proof. exact: oppr_itv. Qed.

Lemma oppr_itvcc (a b x : R) : (- x \in `[a, b]) = (x \in `[- b, - a]).
Proof. exact: oppr_itv. Qed.

Lemma ler_wpMn2r n : {homo (@GRing.natmul R)^~ n : x y / x <= y}.
Proof.
by move=> x y xy;rewrite -mulr_natl -[y *+ n]mulr_natl ler_wpM2l.
Qed.

End pordered_theory.

Arguments ler01 {R}.

Lemma num_real (R : orderedRingType) (x : R) : x \is real. 
Proof. exact: le_total. Qed.
Hint Resolve num_real : core.

Arguments ler0n : clear implicits.
Hint Extern 0 (is_true (@Order.le ring_display _ _ _)) =>
  solve [apply: ler01 | apply: ler0n | apply: lerN10] : core.

Section nzpordered_theory.
Context (R : porderedNzRingType).
Implicit Types x y : R.

Lemma ltr01 : 0 < 1 :> R.
Proof. by rewrite lt_def oner_neq0 ler01. Qed.

Lemma ltr0Sn n : 0 < n.+1%:R :> R.
Proof.
apply: (lt_le_trans ltr01).
by rewrite mulrS lerDl ler0n.
Qed.

Lemma ltr0n n : (0 < n%:R :> R) = (0 < n)%N.
Proof. by case: n => // n; exact: ltr0Sn. Qed.

Definition lter01 := (@ler01 R, ltr01).
Local Hint Extern 0 (is_true (@Order.lt ring_display _ _ _)) =>
  solve [apply: ltr01 | apply: ltr0Sn] : core.

Lemma pnatr_eq0 n : (n%:R == 0 :> R) = (n == 0)%N.
Proof. by case: n => [|n]; rewrite ?eqxx // gt_eqF ?ltr0Sn. Qed.

Lemma pnatr_eq1 n : (n%:R == 1 :> R) = (n == 1)%N.
Proof.
case: n => [|n]; rewrite ?[0 == 1]eq_sym ?oner_eq0 //.
by rewrite mulrS [_ == 1]eq_sym addrC -subr_eq subrr eq_sym pnatr_eq0.
Qed.

Lemma lern0 n : (n%:R <= 0 :> R) = (n == 0).
Proof. by rewrite -pnatr_eq0 eq_le ler0n andbT. Qed.

Lemma ltrn0 n : (n%:R < 0 :> R) = false.
Proof. by rewrite lt_neqAle pnatr_eq0 lern0 andNb. Qed.

Lemma ler_nat m n : (m%:R <= n%:R :> R) = (m <= n)%N.
Proof.
elim: m n => [|m IH] n; rewrite ?ler0n //.
by case: n => [|n]; rewrite ?lern0 // !mulrS lerD2l IH ltnS.
Qed.

Lemma eqr_nat m n : (m%:R == n%:R :> R) = (m == n).
Proof. by rewrite eq_le !ler_nat eqn_leq. Qed.

Lemma ltr_nat m n : (m%:R < n%:R :> R) = (m < n)%N.
Proof. by rewrite lt_neqAle ler_nat eqr_nat ltn_neqAle. Qed.

Lemma ler1n n : (1 <= n%:R :> R) = (1 <= n)%N. Proof. by rewrite -ler_nat. Qed.
Lemma ltr1n n : (1 < n%:R :> R) = (1 < n)%N. Proof. by rewrite -ltr_nat. Qed.
Lemma lern1 n : (n%:R <= 1 :> R) = (n <= 1)%N. Proof. by rewrite -ler_nat. Qed.
Lemma ltrn1 n : (n%:R < 1 :> R) = (n < 1)%N. Proof. by rewrite -ltr_nat. Qed.
Lemma ltrN10 : -1 < 0 :> R. Proof. by rewrite oppr_lt0. Qed.
Lemma ltr10 : (1 < 0 :> R) = false. Proof. by rewrite le_gtF. Qed.
Lemma ler10 : (1 <= 0 :> R) = false. Proof. by rewrite lt_geF. Qed.
Lemma ltr0N1 : (0 < -1 :> R) = false. Proof. by rewrite le_gtF // lerN10. Qed.
Lemma ler0N1 : (0 <= -1 :> R) = false. Proof. by rewrite lt_geF // ltrN10. Qed.

Lemma pchar_num : [pchar R] =i pred0.
Proof. by case=> // p /=; rewrite !inE pnatr_eq0 andbF. Qed.

(* max and min *)

Lemma natr_min (m n : nat) : (Order.min m n)%:R = Order.min m%:R n%:R :> R.
Proof. by rewrite !minElt ltr_nat /Order.lt/= -fun_if. Qed.

Lemma natr_max (m n : nat) : (Order.max m n)%:R = Order.max m%:R n%:R :> R.
Proof. by rewrite !maxElt ltr_nat /Order.lt/= -fun_if. Qed.

(* Binary sign ((-1) ^+ s). *)

Lemma signr_gt0 (b : bool) : (0 < (-1) ^+ b :> R) = ~~ b.
Proof. by case: b; rewrite (ltr01, ltr0N1). Qed.

Lemma signr_lt0 (b : bool) : ((-1) ^+ b < 0 :> R) = b.
Proof. by case: b; rewrite // ?(ltrN10, ltr10). Qed.

Lemma signr_ge0 (b : bool) : (0 <= (-1) ^+ b :> R) = ~~ b.
Proof. by rewrite le0r signr_eq0 signr_gt0. Qed.

Lemma signr_le0 (b : bool) : ((-1) ^+ b <= 0 :> R) = b.
Proof. by rewrite le_eqVlt signr_eq0 signr_lt0. Qed.

(* This actually holds for char R != 2. *)
Lemma signr_inj : injective (fun b : bool => (-1) ^+ b : R).
Proof. exact: can_inj (fun x => 0 >= x) signr_le0. Qed.

Lemma sgr1 : sg 1 = 1 :> R. Proof. by rewrite gtr0_sg // ltr01. Qed.
Lemma sgrN1 : sg (-1) = -1 :> R. Proof. by rewrite ltr0_sg // ltrN10. Qed.
Definition sgrE := (@sgr0 R, sgr1, sgrN1).

Lemma mulr_sg_eq1 x y : (sg x * y == 1) = (x != 0) && (sg x == y).
Proof.
rewrite /sg eq_sym; case: ifP => _; first by rewrite mul0r oner_eq0.
by case: ifP => _; rewrite ?mul1r // mulN1r eqr_oppLR.
Qed.

Lemma mulr_sg_eqN1 x y : (sg x * sg y == -1) = (x != 0) && (sg x == - sg y).
Proof.
move/sg: y => y; rewrite /sg eq_sym eqr_oppLR.
case: ifP => _; first by rewrite mul0r oppr0 oner_eq0.
by case: ifP => _; rewrite ?mul1r // mulN1r eqr_oppLR.
Qed.

Lemma sgr_eq0 x : (sg x == 0) = (x == 0).
Proof.
rewrite /sg; case: ifP => _; first exact: eqxx.
by case: ifP => _; rewrite ?oppr_eq0 oner_eq0.
Qed.

Lemma sgr_nat n : sg n%:R = (n != 0)%:R :> R.
Proof. by rewrite /sg pnatr_eq0 ltrn0; case: ifP. Qed.

Lemma sgr_id x : sg (sg x) = sg x.
Proof. by rewrite !(fun_if sg) !sgrE. Qed.

Lemma sgr_lt0 x : (sg x < 0) = (x < 0).
Proof.
rewrite /sg; case: eqP => [-> // | _].
by case: ifP => _; rewrite ?ltrN10 // lt_gtF.
Qed.

Lemma sgr_le0 x : (sgr x <= 0) = (x <= 0).
Proof. by rewrite !le_eqVlt sgr_eq0 sgr_lt0. Qed.

(* leif *)

Lemma leif_nat_r m n C : (m%:R <= n%:R ?= iff C :> R) = (m <= n ?= iff C)%N.
Proof. by rewrite /leif !ler_nat eqr_nat. Qed.

Lemma lteif01 C : 0 < 1 ?<= if C :> R.
Proof. by case: C; rewrite /= lter01. Qed.

Section FinGroup.

Variables (gT : finGroupType).
Implicit Types G : {group gT}.

Local Open Scope group_scope.

Lemma natrG_gt0 G : #|G|%:R > 0 :> R.
Proof. by rewrite ltr0n cardG_gt0. Qed.

Lemma natrG_neq0 G : #|G|%:R != 0 :> R.
Proof. by rewrite gt_eqF // natrG_gt0. Qed.

Lemma natr_indexg_gt0 G B : #|G : B|%g%:R > 0 :> R.
Proof. by rewrite ltr0n indexg_gt0. Qed.

Lemma natr_indexg_neq0 G B : #|G : B|%g%:R != 0 :> R.
Proof. by rewrite gt_eqF // natr_indexg_gt0. Qed.

End FinGroup.

End nzpordered_theory.

Arguments ltr01 {R}.
Arguments signr_inj {R} [x1 x2].
#[global] Hint Extern 0 (is_true (@Order.lt ring_display _ _ _)) =>
  solve [apply: ltr01 | apply: ltr0Sn | apply: ltrN10] : core.
#[global] Hint Extern 0 (is_true (_%:R \is real)) => apply: realn : core.
#[global] Hint Extern 0 (is_true (1 \is real)) => apply: real1 : core.

Section strictpordered_theory.
Context {R : strictPOrderedRingType}.
Implicit Types x y : R.

Lemma mulr_gt0 x y : 0 < x -> 0 < y -> 0 < x * y.
Proof. exact: mulr_gt0. Qed.

Local Fact pos_mulr_closed : mulr_closed (@pos R).
Proof.
by split=> [|x y]; [ rewrite posrE ltr01 | exact: mulr_gt0 ].
Qed.
#[export]
HB.instance Definition _ := GRing.isMulClosed.Build R pos_num_pred
  pos_mulr_closed.

Lemma mulr_gt0_lt0 x y : 0 < x -> y < 0 -> x * y < 0.
Proof. by rewrite -!oppr_gt0 -mulrN; exact: mulr_gt0. Qed.

Lemma mulr_lt0_gt0 x y : x < 0 -> 0 < y -> x * y < 0.
Proof. by rewrite -!oppr_gt0 -mulNr; exact: mulr_gt0. Qed.

Lemma lt0_mulr_gt0 x y : x < 0 -> y < 0 -> 0 < x * y.
Proof. by rewrite -!oppr_gt0 -mulrNN; exact: mulr_gt0. Qed.

Lemma exprn_gt0 n x : 0 < x -> 0 < x ^+ n.
Proof.
move=> x0; elim: n => [|n IH]; first by rewrite expr0 ltr01.
by rewrite exprS mulr_gt0.
Qed.

Definition exprn_gte0 := (@exprn_ge0 R, exprn_gt0).

Lemma ltr_pM2lW x : 0 < x -> {homo *%R x : x y / x < y}.
Proof. by move=> x0 y z yz; rewrite -subr_gt0 -mulrBr mulr_gt0 // subr_gt0. Qed.

Lemma ltr_pM2rW x : 0 < x -> {homo *%R^~ x : x y / x < y}.
Proof. by move=> x0 y z yz; rewrite -subr_gt0 -mulrBl mulr_gt0 // subr_gt0. Qed.

Lemma ltr_nM2lW x : x < 0 -> {homo *%R x : x y /~ x < y}.
Proof.
by move=> x0 y z yz; rewrite -subr_gt0 -mulrBr lt0_mulr_gt0 // subr_lt0.
Qed.

Lemma ltr_nM2rW x : x < 0 -> {homo *%R^~ x : x y /~ x < y}.
Proof.
by move=> x0 y z yz; rewrite -subr_gt0 -mulrBl lt0_mulr_gt0 // subr_lt0.
Qed.

Lemma ltr_pM x1 y1 x2 y2 :
  0 <= x1 -> 0 <= x2 -> x1 < y1 -> x2 < y2 -> x1 * x2 < y1 * y2.
Proof.
move=> x1ge0 x2ge0 x1y1 x2y2.
apply: (@le_lt_trans _ _ (x1 * y2)).
- by apply: ler_wpM2l => //; exact: ltW.
- by apply: ltr_pM2rW => //; apply: le_lt_trans x2y2.
Qed.

Lemma prodr_gt0 I r (P : pred I) (E : I -> R) :
  (forall i, P i -> 0 < E i) -> 0 < \prod_(i <- r | P i) E i.
Proof. by move=> Ege0; rewrite -posrE rpred_prod. Qed.

Lemma ltr_prod I r (P : pred I) (E1 E2 : I -> R) :
    has P r -> (forall i, P i -> 0 <= E1 i < E2 i) ->
  \prod_(i <- r | P i) E1 i < \prod_(i <- r | P i) E2 i.
Proof.
elim: r => //= i r IHr; rewrite !big_cons; case: ifP => {IHr}// Pi _ ltE12.
have /andP[le0E1i ltE12i] := ltE12 i Pi; set E2r := \prod_(j <- r | P j) E2 j.
apply: le_lt_trans (_ : E1 i * E2r < E2 i * E2r).
  by rewrite ler_wpM2l ?ler_prod // => j /ltE12/andP[-> /ltW].
apply: ltr_pM2rW => //.
by rewrite prodr_gt0 // => j /ltE12/andP[? /le_lt_trans->].
Qed.

Lemma ltr_prod_nat (E1 E2 : nat -> R) (n m : nat) :
   (m < n)%N -> (forall i, (m <= i < n)%N -> 0 <= E1 i < E2 i) ->
  \prod_(m <= i < n) E1 i < \prod_(m <= i < n) E2 i.
Proof.
move=> lt_mn ltE12; rewrite !big_nat ltr_prod {ltE12}//.
by apply/hasP; exists m; rewrite ?mem_index_iota leqnn.
Qed.

Lemma gtr_pMlW x y : 0 < y -> x < 1 -> x * y < y.
Proof. by move=> hy hx; rewrite -{2}[y]mul1r ltr_pM2rW. Qed.

Lemma gtr_pMrW x y : 0 < y -> x < 1 -> y * x < y.
Proof. by move=> hy hx; rewrite -{2}[y]mulr1 ltr_pM2lW. Qed.

Lemma ltr_pMlW x y : 0 < y -> 1 < x -> y < x * y.
Proof. by move=> hy hx; rewrite -{1}[y]mul1r ltr_pM2rW. Qed.

Lemma ltr_pMrW x y : 0 < y -> 1 < x -> y < y * x.
Proof. by move=> hy hx; rewrite -{1}[y]mulr1 ltr_pM2lW. Qed.

Lemma gtr_nMlW x y : y < 0 -> 1 < x -> x * y < y.
Proof. by move=> hy hx; rewrite -{2}[y]mul1r ltr_nM2rW. Qed.

Lemma gtr_nMrW x y : y < 0 -> 1 < x -> y * x < y.
Proof. by move=> hy hx; rewrite -{2}[y]mulr1 ltr_nM2lW. Qed.

Lemma ltr_nMlW x y : y < 0 -> x < 1 -> y < x * y.
Proof. by move=> hy hx; rewrite -{1}[y]mul1r ltr_nM2rW. Qed.

Lemma ltr_nMrW x y : y < 0 -> x < 1 -> y < y * x.
Proof. by move=> hy hx; rewrite -{1}[y]mulr1 ltr_nM2lW. Qed.

Lemma mulr_egt1 x y : 1 < x -> 1 < y -> 1 < x * y.
Proof.
by move=> lt1x lt1y; rewrite (@lt_trans _ _ y) // ltr_pMlW // (lt_trans ltr01).
Qed.
Definition mulr_egte1 := (@mulr_ege1 R, mulr_egt1).
Definition mulr_cp1 := (@mulr_ilte1 R, mulr_egte1).

Lemma exprn_ilt1 n x : 0 <= x -> x < 1 -> (x ^+ n < 1) = (n != 0).
Proof.
move=> xge0 xlt1.
case: n; [by rewrite eqxx ltxx | elim=> [|n ihn]; first by rewrite expr1].
by rewrite exprS mulr_ilt1 // exprn_ge0.
Qed.

Definition exprn_ilte1 := (@exprn_ile1 R, exprn_ilt1).

Lemma exprn_egt1 n x : 1 < x -> (1 < x ^+ n) = (n != 0).
Proof.
move=> xgt1; case: n; first by rewrite eqxx ltxx.
by elim=> [|n ihn]; rewrite ?expr1// exprS mulr_egt1 // exprn_ge0.
Qed.

Definition exprn_egte1 := (@exprn_ege1 R, exprn_egt1).
Definition exprn_cp1 := (exprn_ilte1, exprn_egte1).

Lemma ltr_iXnrW x n : 0 < x -> x < 1 -> (1 < n)%N -> x ^+ n < x.
Proof.
by case: n => [|[|n]] // x0 x1 _; rewrite exprS gtr_pMrW // exprn_ilt1 // ltW.
Qed.

Lemma ltr_iXn2lW x :
  0 < x -> x < 1 -> {homo GRing.exp x : m n / (n < m)%N >-> m < n}.
Proof.
move=> x0 x1 m n /[dup] mn /ltnW /subnK <-.
rewrite exprD gtr_pMlW ?exprn_gt0 // exprn_ilt1 ?ltW //.
by rewrite subn_eq0 -ltnNge.
Qed.

End strictpordered_theory.

Arguments exprn_gt0 [R] n {x}.

Section numring_theory.
Context (R : numPOrderedRingType).
Implicit Types x y z : R.

Lemma realMr x y : x != 0 -> x \is real -> (x * y \is real) = (y \is real).
Proof. exact: realMr. Qed.
Lemma realrM x y : y != 0 -> y \is real -> (x * y \is real) = (x \is real).
Proof. exact: realrM. Qed.

Lemma ger1_real x : 1 <= x -> x \is real. Proof. by move=> /ger_real->. Qed.
Lemma ler1_real x : x <= 1 -> x \is real. Proof. by move=> /ler_real->. Qed.

(* real of mul *)

Lemma realM : {in real &, forall x y, x * y \is real}.
Proof. exact: rpredM. Qed.

Lemma realrMn x n : (n != 0)%N -> (x *+ n \is real) = (x \is real).
Proof. by move=> n_neq0; rewrite -mulr_natl realMr ?realn ?pnatr_eq0. Qed.

Lemma pmulr_rgt0 x y : 0 < x -> (0 < x * y) = (0 < y).
Proof.
move=> x0.
apply/idP/idP; last exact: mulr_gt0.
move=> xy0.
have yR : y \is real by rewrite -(@realMr x) ?gt_eqF ?gtr0_real.
apply: comparable_contra_lt xy0; first by rewrite comparable0r.
by rewrite -!oppr_ge0 -mulrN; apply/mulr_ge0/ltW.
Qed.

Lemma pmulr_lgt0 x y : 0 < y -> (0 < x * y) = (0 < x).
Proof.
move=> x0.
apply/idP/idP => [xy0|?]; last exact: mulr_gt0.
have yR : x \is real by rewrite -(@realrM x y) ?gt_eqF ?gtr0_real.
apply: comparable_contra_lt xy0; first by rewrite comparable0r.
by rewrite -!oppr_ge0 -mulNr => /mulr_ge0; apply; apply/ltW.
Qed.

Lemma nmulr_rgt0 x y : x < 0 -> (0 < x * y) = (y < 0).
Proof. by rewrite -!oppr_gt0 -mulrNN; exact: pmulr_rgt0. Qed.

Lemma nmulr_lgt0 x y : x < 0 -> (0 < y * x) = (y < 0).
Proof. by rewrite -!oppr_gt0 -mulrNN; exact: pmulr_lgt0. Qed.

Lemma ltr_pM2l x : 0 < x -> {mono *%R x : x y / x < y}.
Proof. by move=> x0 y z; rewrite -subr_gt0 -mulrBr pmulr_rgt0 // subr_gt0. Qed.

Lemma ltr_pM2r x : 0 < x -> {mono *%R^~ x : x y / x < y}.
Proof. by move=> x0 y z; rewrite -subr_gt0 -mulrBl pmulr_lgt0 // subr_gt0. Qed.

Lemma ltr_nM2l x : x < 0 -> {mono *%R x : x y /~ x < y}.
Proof. by move=> x0 y z; rewrite -subr_gt0 -mulrBr nmulr_rgt0 // subr_lt0. Qed.

Lemma ltr_nM2r x : x < 0 -> {mono *%R^~ x : x y /~ x < y}.
Proof. by move=> x0 y z; rewrite -subr_gt0 -mulrBl nmulr_lgt0 // subr_lt0. Qed.

Lemma ltr_pMn2r n : (0 < n)%N -> {mono (@GRing.natmul R)^~ n : x y / x < y}.
Proof.
by case: n => // n _ x y; rewrite -mulr_natl -[y *+ _]mulr_natl ltr_pM2l.
Qed.

Lemma pmulrn_lgt0 x n : (0 < n)%N -> (0 < x *+ n) = (0 < x).
Proof. by move=> n_gt0; rewrite -(mul0rn _ n) ltr_pMn2r // mul0rn. Qed.

Lemma pmulrn_llt0 x n : (0 < n)%N -> (x *+ n < 0) = (x < 0).
Proof. by move=> n_gt0; rewrite -(mul0rn _ n) ltr_pMn2r // mul0rn. Qed.

Lemma ltr_wMn2r x y n : x < y -> (x *+ n < y *+ n) = (0 < n)%N.
Proof. by move=> ltxy; case: n=> // n; rewrite ltr_pMn2r. Qed.

Lemma ltrMn2r n x y : (x *+ n < y *+ n) = ((0 < n)%N && (x < y)).
Proof. by case: n => [|n]; rewrite ?lexx ?eqxx // ltr_pMn2r. Qed.

Lemma mulrn_wgt0 x n : 0 < x -> (0 < x *+ n) = (0 < n)%N.
Proof. by case: n => // n hx; rewrite pmulrn_lgt0. Qed.

Lemma mulrn_wlt0 x n : x < 0 -> (x *+ n < 0) = (0 < n)%N.
Proof. by case: n => // n hx; rewrite pmulrn_llt0. Qed.

#[deprecated(since="mathcomp 2.4.0", use=mulrn_wgt0)]
Lemma pmulrn_rgt0 x n : 0 < x -> (0 < x *+ n) = (0 < n)%N.
Proof. exact: mulrn_wgt0. Qed.

Lemma pmulrn_rlt0 x n : 0 < x -> (x *+ n < 0) = false.
Proof. by move=> x_gt0; rewrite -(mulr0n x) ltr_pMn2l. Qed.

Lemma pmulrn_rge0 x n : 0 < x -> 0 <= x *+ n.
Proof. by move=> x_gt0; rewrite -(mulr0n x) ler_pMn2l. Qed.

Lemma pmulrn_rle0 x n : 0 < x -> (x *+ n <= 0) = (n == 0)%N.
Proof. by move=> x_gt0; rewrite -(mulr0n x) ler_pMn2l ?leqn0. Qed.

Lemma nmulrn_rgt0 x n : x < 0 -> (0 < x *+ n) = false.
Proof. by move=> x_lt0; rewrite -(mulr0n x) ltr_nMn2l. Qed.

Lemma nmulrn_rge0 x n : x < 0 -> (0 <= x *+ n) = (n == 0)%N.
Proof. by move=> x_lt0; rewrite -(mulr0n x) ler_nMn2l ?leqn0. Qed.

Lemma nmulrn_rle0 x n : x < 0 -> x *+ n <= 0.
Proof. by move=> x_lt0; rewrite -(mulr0n x) ler_nMn2l. Qed.

(* (x * y) compared to 0 *)
(* Remark : pmulr_rgt0 and pmulr_rge0 are defined above *)

(* x positive and y right *)
Lemma pmulr_rlt0 x y : 0 < x -> (x * y < 0) = (y < 0).
Proof. by rewrite -!oppr_gt0 -mulrN; exact: pmulr_rgt0. Qed.

(* x positive and y left *)
Lemma pmulr_llt0 x y : 0 < x -> (y * x < 0) = (y < 0).
Proof. by rewrite -!oppr_gt0 -mulNr; exact: pmulr_lgt0. Qed.

(* x negative and y right *)

Lemma nmulr_rlt0 x y : x < 0 -> (x * y < 0) = (0 < y).
Proof. by move=> x_lt0; rewrite -mulrNN pmulr_rlt0 lterNE. Qed.

(* x negative and y left *)

Lemma nmulr_llt0 x y : x < 0 -> (y * x < 0) = (0 < y).
Proof. by rewrite -!oppr_gt0 -mulrN; exact: pmulr_lgt0. Qed.

Lemma mulr_ge0_gt0 x y : 0 <= x -> 0 <= y -> (0 < x * y) = (0 < x) && (0 < y).
Proof.
rewrite le_eqVlt => /predU1P[<-|x0]; first by rewrite mul0r ltxx.
rewrite le_eqVlt => /predU1P[<-|y0]; first by rewrite mulr0 ltxx andbC.
by apply/idP/andP=> [|_]; rewrite pmulr_rgt0.
Qed.

Lemma gtr_pMl x y : 0 < y -> (x * y < y) = (x < 1).
Proof. by move=> hy; rewrite -{2}[y]mul1r ltr_pM2r. Qed.

Lemma gtr_pMr x y : 0 < y -> (y * x < y) = (x < 1).
Proof. by move=> hy; rewrite -{2}[y]mulr1 ltr_pM2l. Qed.

Lemma ltr_pMl x y : 0 < y -> (y < x * y) = (1 < x).
Proof. by move=> hy; rewrite -{1}[y]mul1r ltr_pM2r. Qed.

Lemma ltr_pMr x y : 0 < y -> (y < y * x) = (1 < x).
Proof. by move=> hy; rewrite -{1}[y]mulr1 ltr_pM2l. Qed.

Lemma gtr_nMl x y : y < 0 -> (x * y < y) = (1 < x).
Proof. by move=> hy; rewrite -{2}[y]mul1r ltr_nM2r. Qed.

Lemma gtr_nMr x y : y < 0 -> (y * x < y) = (1 < x).
Proof. by move=> hy; rewrite -{2}[y]mulr1 ltr_nM2l. Qed.

Lemma ltr_nMl x y : y < 0 -> (y < x * y) = (x < 1).
Proof. by move=> hy; rewrite -{1}[y]mul1r ltr_nM2r. Qed.

Lemma ltr_nMr x y : y < 0 -> (y < y * x) = (x < 1).
Proof. by move=> hy; rewrite -{1}[y]mulr1 ltr_nM2l. Qed.

Lemma ltr_iXnr x n : 0 < x -> x < 1 -> (x ^+ n < x) = (1 < n)%N.
Proof.
case: n=> [|[|n]] //; first by rewrite expr0 => _ /lt_gtF ->.
by move=> x0 x1; rewrite exprS gtr_pMr // ?exprn_ilt1 // ltW.
Qed.

Definition lter_iXnr := (ler_iXnr, ltr_iXnr).

Lemma ltr_eXnr x n : 1 < x -> (x < x ^+ n) = (1 < n)%N.
Proof.
move=> x_ge1; case: n=> [|[|n]] //; first by rewrite expr0 lt_gtF.
by rewrite exprS ltr_pMr ?(lt_trans _ x_ge1) ?exprn_egt1.
Qed.

Definition lter_eXnr := (ler_eXnr, ltr_eXnr).
Definition lter_Xnr := (lter_iXnr, lter_eXnr).

Lemma ieexprn_weq1 x n : 0 <= x -> (x ^+ n == 1) = ((n == 0) || (x == 1)).
Proof.
move=> xle0; case: n => [|n]; first by rewrite expr0 eqxx.
have : x >=< 1 by rewrite real_comparable ?ger0_real.
case/comparable_ltgtP; do ?by rewrite ?ger0_real.
+ by move=> x_lt1; rewrite 1?lt_eqF // exprn_ilt1.
+ by move=> x_lt1; rewrite 1?gt_eqF // exprn_egt1.
by move->; rewrite expr1n eqxx.
Qed.

Lemma ieexprIn x : 0 < x -> x != 1 -> injective (GRing.exp x).
Proof.
move=> x_gt0 x_neq1 m n; without loss /subnK <-: m n / (n <= m)%N.
  by move=> IH eq_xmn; case/orP: (leq_total m n) => /IH->.
case: {m}(m - n)%N => // m /eqP/idPn[]; rewrite -[x ^+ n]mul1r exprD.
have cx1 : x >=< 1.
  by apply: (@comparabler_trans _ 0); rewrite ?comparable0r // gt_comparable.
case/comparable_ltgtP : cx1 x_neq1 => // x1 _.
- by rewrite lt_eqF // ltr_pM2rW ?exprn_gt0 ?exprn_ilt1 // ltW.
- by rewrite gt_eqF // ltr_pM2rW ?exprn_gt0 ?exprn_egt1. 
Qed.

Lemma ler_iXn2l x :
  0 < x -> x < 1 -> {mono GRing.exp x : m n / (n <= m)%N >-> m <= n}.
Proof.
move=> xgt0 xlt1; apply: (le_nmono (inj_nhomo_lt _ _)); last first.
  by apply/ler_wiXn2l; exact/ltW.
by apply: ieexprIn; rewrite ?lt_eqF ?ltr_cpable.
Qed.

Lemma ltr_iXn2l x :
  0 < x -> x < 1 -> {mono GRing.exp x : m n / (n < m)%N >-> m < n}.
Proof. by move=> xgt0 xlt1; apply: (leW_nmono (ler_iXn2l _ _)). Qed.

Definition lter_iXn2l := (ler_iXn2l, ltr_iXn2l).

Lemma ler_eXn2l x :
  1 < x -> {mono GRing.exp x : m n / (m <= n)%N >-> m <= n}.
Proof.
move=> xgt1; apply: (le_mono (inj_homo_lt _ _)); last first.
  by apply: ler_weXn2l; rewrite ltW.
by apply: ieexprIn; rewrite ?gt_eqF ?gtr_cpable //; apply: lt_trans xgt1.
Qed.

Lemma ltr_eXn2l x :
  1 < x -> {mono (GRing.exp x) : m n / (m < n)%N >-> m < n}.
Proof. by move=> xgt1; apply: (leW_mono (ler_eXn2l _)). Qed.

Definition lter_eXn2l := (ler_eXn2l, ltr_eXn2l).

Lemma ltrXn2r n x y : 0 <= x -> x < y -> (x ^+ n < y ^+ n) = (n != 0).
Proof.
move=> xge0 xlty; case: n; first by rewrite ltxx.
elim=> [|n IHn]; rewrite ?[_ ^+ _.+2]exprS //.
rewrite (@le_lt_trans _ _ (x * y ^+ n.+1)) ?ler_wpM2l ?ltr_pM2r ?IHn //.
  by rewrite ltW.
by rewrite exprn_gt0 // (le_lt_trans xge0).
Qed.

Lemma lerXn2r n : {in nneg & , {homo (@GRing.exp R)^~ n : x y / x <= y}}.
Proof.
move=> x y /= x0 y0 xy; elim: n => [|n IHn]; rewrite !(expr0, exprS) //.
by rewrite (@le_trans _ _ (x * y ^+ n)) ?ler_wpM2l ?ler_wpM2r ?exprn_ge0.
Qed.

Definition lterXn2r := (lerXn2r, ltrXn2r).

Lemma ltr_wpXn2r n :
  (0 < n)%N -> {in nneg & , {homo (@GRing.exp R)^~ n : x y / x < y}}.
Proof. by move=> ngt0 x y /= x0 y0 hxy; rewrite ltrXn2r // -lt0n. Qed.

Lemma ler_pXn2r n :
  (0 < n)%N -> {in nneg & , {mono (@GRing.exp R)^~ n : x y / x <= y}}.
Proof.
case: n => // n _ x y; rewrite !qualifE /= => x_ge0 y_ge0.
have : x >=< y by apply/real_comparable; apply/ger0_real.
case/comparable_ltgtP => [xy|yx|->]; last exact: lexx.
- by rewrite ltW // ltr_wpXn2r.
- by rewrite lt_geF // ltr_wpXn2r.
Qed.

Lemma ltr_pXn2r n :
  (0 < n)%N -> {in nneg & , {mono (@GRing.exp R)^~ n : x y / x < y}}.
Proof.
by move=> n_gt0 x y x_ge0 y_ge0; rewrite !lt_neqAle !eq_le !ler_pXn2r.
Qed.

Definition lter_pXn2r := (ler_pXn2r, ltr_pXn2r).

Lemma pexpIrn n : (0 < n)%N -> {in nneg &, injective ((@GRing.exp R)^~ n)}.
Proof. by move=> n_gt0; apply: inc_inj_in (ler_pXn2r _). Qed.

(* expr and ler/ltr *)
Lemma expr_le1 n x : (0 < n)%N -> 0 <= x -> (x ^+ n <= 1) = (x <= 1).
Proof.
by move=> ngt0 xge0; rewrite -{1}[1](expr1n _ n) ler_pXn2r // [_ \in _]ler01.
Qed.

Lemma expr_lt1 n x : (0 < n)%N -> 0 <= x -> (x ^+ n < 1) = (x < 1).
Proof.
by move=> ngt0 xge0; rewrite -{1}[1](expr1n _ n) ltr_pXn2r // [_ \in _]ler01.
Qed.

Definition expr_lte1 := (expr_le1, expr_lt1).

Lemma expr_ge1 n x : (0 < n)%N -> 0 <= x -> (1 <= x ^+ n) = (1 <= x).
Proof.
by move=> ngt0 xge0; rewrite -{1}[1](expr1n _ n) ler_pXn2r // [_ \in _]ler01.
Qed.

Lemma expr_gt1 n x : (0 < n)%N -> 0 <= x -> (1 < x ^+ n) = (1 < x).
Proof.
by move=> ngt0 xge0; rewrite -{1}[1](expr1n _ n) ltr_pXn2r // [_ \in _]ler01.
Qed.

Definition expr_gte1 := (expr_ge1, expr_gt1).

Lemma pexpr_eq1 x n : (0 < n)%N -> 0 <= x -> (x ^+ n == 1) = (x == 1).
Proof. by move=> ngt0 xge0; rewrite !eq_le expr_le1 // expr_ge1. Qed.

Lemma pexprn_eq1 x n : 0 <= x -> (x ^+ n == 1) = (n == 0) || (x == 1).
Proof. by case: n => [|n] xge0; rewrite ?eqxx // pexpr_eq1 ?gtn_eqF. Qed.

Lemma eqrXn2 n x y :
  (0 < n)%N -> 0 <= x -> 0 <= y -> (x ^+ n == y ^+ n) = (x == y).
Proof. by move=> ngt0 xge0 yge0; rewrite (inj_in_eq (pexpIrn _)). Qed.

Lemma sqrp_eq1 x : 0 <= x -> (x ^+ 2 == 1) = (x == 1).
Proof. by move/pexpr_eq1->. Qed.

Lemma sqrn_eq1 x : x <= 0 -> (x ^+ 2 == 1) = (x == -1).
Proof. by rewrite -sqrrN -oppr_ge0 -eqr_oppLR => /sqrp_eq1. Qed.

Lemma ler_sqr : {in nneg &, {mono (fun x => x ^+ 2) : x y / x <= y}}.
Proof. exact: ler_pXn2r. Qed.

Lemma ltr_sqr : {in nneg &, {mono (fun x => x ^+ 2) : x y / x < y}}.
Proof. exact: ltr_pXn2r. Qed.

Lemma real_sqr x : x \is real -> 0 <= x ^+ 2.
Proof. by rewrite expr2; case/orP => x0; [apply: mulr_ge0|apply: mulr_le0]. Qed.

Lemma real_maxr_pMr x :
  0 <= x -> {in real &, {morph *%R x : y z / maxr y z}}.
Proof.
move=> x0 y z yr zr.
have xyr : x * y \is real by apply: realM => //; apply: ger0_real.
have xzr : x * z \is real by apply: realM => //; apply: ger0_real.
case/comparable_ltgtP : (real_comparable yr zr) => [yz|zy|->].
- by apply/esym/max_idPr/ler_wpM2l => //; apply: ltW.
- apply/esym/comparable_max_idPl; first by apply: real_comparable.
  by apply: ler_wpM2l => //; apply: ltW.
- by rewrite /maxr ltxx.
Qed.

Lemma real_minr_pMr x :
  0 <= x -> {in real &, {morph *%R x : y z / minr y z}}.
Proof.
move=> x0 y z yr zr; apply: oppr_inj.
rewrite -mulrN !real_oppr_min ?realM // ?ger0_real //.
by rewrite -!mulrN real_maxr_pMr ?realN.
Qed.

Lemma real_maxr_pMl x :
  0 <= x -> {in real &, {morph *%R^~ x : y z / maxr y z}}.
Proof.
move=> x0 y z yr zr.
have xyr : y * x \is real by apply: realM => //; apply: ger0_real.
have xzr : z * x \is real by apply: realM => //; apply: ger0_real.
case/comparable_ltgtP : (real_comparable yr zr) => [yz|zy|->].
- by apply/esym/max_idPr/ler_wpM2r => //; apply: ltW.
- apply/esym/comparable_max_idPl; first by apply: real_comparable.
  by apply: ler_wpM2r => //; apply: ltW.
- by rewrite /maxr ltxx.
Qed.

Lemma real_minr_pMl x :
  0 <= x -> {in real &, {morph *%R^~ x : y z / minr y z}}.
Proof.
move=> x0 y z yr zr; apply: oppr_inj.
rewrite -mulNr !real_oppr_min ?realM // ?ger0_real //.
by rewrite -!mulNr real_maxr_pMl ?realN.
Qed.

Lemma real_maxr_nMr x y z : x <= 0 -> y \is real -> z \is real ->
  x * max y z = min (x * y) (x * z).
Proof.
move=> x0 yr zr; rewrite -[_ * _]opprK -mulrN real_oppr_max// -mulNr.
by rewrite real_minr_pMr ?oppr_ge0 ?realN // !mulrNN.
Qed.

Lemma real_minr_nMr x y z :  x <= 0 -> y \is real -> z \is real ->
  x * min y z = max (x * y) (x * z).
Proof.
move=> x0 yr zr; rewrite -[_ * _]opprK -mulrN real_oppr_min// -mulNr.
by rewrite real_maxr_pMr ?oppr_ge0 ?realN // !mulrNN.
Qed.

Lemma real_maxr_nMl x y z : x <= 0 -> y \is real -> z \is real ->
  max y z * x = min (y * x) (z * x).
Proof.
move=> x0 yr zr; rewrite -[_ * _]opprK -mulNr real_oppr_max// -mulrN.
by rewrite real_minr_pMl ?oppr_ge0 ?realN // !mulrNN.
Qed.

Lemma real_minr_nMl x y z : x <= 0 -> y \is real -> z \is real ->
  min y z * x = max (y * x) (z * x).
Proof.
move=> x0 yr zr; rewrite -[_ * _]opprK -mulNr real_oppr_min// -mulrN.
by rewrite real_maxr_pMl ?oppr_ge0 ?realN // !mulrNN.
Qed.

Lemma real_expf_eq0 x n : x \is real -> (x ^+ n == 0) = (0 < n)%N && (x == 0).
Proof.
rewrite -comparabler0; case/comparable_ltgtP => [x0|x0|->]; last first.
- by rewrite expr0n; case: n => [|n]; rewrite ?eqxx //= oner_eq0.
- by rewrite andbF gt_eqF ?exprn_gt0.
rewrite andbF -[x]opprK exprNn mulrI_eq0; first exact: lreg_sign.
by rewrite gt_eqF ?exprn_gt0 ?oppr_gt0.
Qed.

Lemma real_exprn_even_gt0 n x :
  x \is real -> ~~ odd n -> (0 < x ^+ n) = (n == 0)%N || (x != 0).
Proof.
move=> xR n_even; rewrite lt0r real_exprn_even_ge0 ?real_expf_eq0 //.
by rewrite andbT negb_and lt0n negbK.
Qed.

Lemma real_exprn_even_le0 n x :
  x \is real -> ~~ odd n -> (x ^+ n <= 0) = (n != 0) && (x == 0).
Proof.
move=> xR n_even; rewrite !real_leNgt ?rpred0 ?rpredX //.
by rewrite real_exprn_even_gt0 // negb_or negbK.
Qed.

Lemma real_exprn_odd_ge0 n x :
  x \is real -> odd n -> (0 <= x ^+ n) = (0 <= x).
Proof.
case/comparable_leP => [x_ge0|x_lt0] n_odd; first by rewrite exprn_ge0.
apply: negbTE; rewrite lt_geF //.
case: n n_odd => // n /= n_even; rewrite exprS pmulr_llt0 //.
by rewrite real_exprn_even_gt0 ?ler0_real ?ltW // (lt_eqF x_lt0) ?orbT.
Qed.

Lemma real_exprn_odd_gt0 n x : x \is real -> odd n -> (0 < x ^+ n) = (0 < x).
Proof.
move=> xR n_odd; rewrite !lt0r real_expf_eq0 //.
by rewrite real_exprn_odd_ge0; case: n n_odd.
Qed.

Lemma real_exprn_odd_le0 n x : x \is real -> odd n -> (x ^+ n <= 0) = (x <= 0).
Proof.
by move=> xR n_odd; rewrite !real_leNgt ?rpred0 ?rpredX // real_exprn_odd_gt0.
Qed.

Lemma real_exprn_odd_lt0 n x : x \is real -> odd n -> (x ^+ n < 0) = (x < 0).
Proof.
by move=> xR n_odd; rewrite !real_ltNge ?rpred0 ?rpredX // real_exprn_odd_ge0.
Qed.

Lemma real_BSide_min b x y : x \in Num.real -> y \in Num.real ->
  BSide b (Order.min x y) = Order.min (BSide b x) (BSide b y).
Proof. by move=> xr yr; apply/comparable_BSide_min/real_comparable. Qed.

Lemma real_BSide_max b x y : x \in Num.real -> y \in Num.real ->
  BSide b (Order.max x y) = Order.max (BSide b x) (BSide b y).
Proof. by move=> xr yr; apply/comparable_BSide_max/real_comparable. Qed.

End numring_theory.

Arguments ler_sqr {R} [x y].
Arguments ltr_sqr {R} [x y].

Section strictorderedring_theory.
Context (R : strictOrderedRingType).
Implicit Types x y z t : R.

(* sign *)

Lemma mulr_lt0 x y :
  (x * y < 0) = [&& x != 0, y != 0 & (x < 0) (+) (y < 0)].
Proof.
case: (ltgtP 0 x) => [x_gt0|x_lt0|<-]; last by rewrite mul0r.
- by rewrite pmulr_rlt0 //; case: ltgtP.
- by rewrite nmulr_rlt0 //; case: ltgtP.
Qed.

Lemma neq0_mulr_lt0 x y :
  x != 0 -> y != 0 -> (x * y < 0) = (x < 0) (+) (y < 0).
Proof. by move=> x_neq0 y_neq0; rewrite mulr_lt0 x_neq0 y_neq0. Qed.

Lemma mulr_sign_lt0 (b : bool) x :
  ((-1) ^+ b * x < 0) = (x != 0) && (b (+) (x < 0)%R).
Proof. by rewrite mulr_lt0 signr_lt0 signr_eq0. Qed.

End strictorderedring_theory.

#[global] Hint Resolve num_real : core.

Section porderedidomain_theory.
Context (R : porderedIdomainType).
Implicit Types x y : R.

Lemma pmulrnI n : (0 < n)%N -> injective ((@GRing.natmul R)^~ n).
Proof.
case: n => // n _ x y /eqP.
rewrite -subr_eq0 -mulrnBl -mulr_natr mulf_eq0 pnatr_eq0 orbF.
by rewrite subr_eq0 => /eqP.
Qed.

Lemma eqr_pMn2r n : (0 < n)%N -> {mono (@GRing.natmul R)^~ n : x y / x == y}.
Proof. by move/pmulrnI/inj_eq. Qed.

Lemma eqrMn2r n x y : (x *+ n == y *+ n) = (n == 0)%N || (x == y).
Proof. by case: n => [|n]; rewrite ?mulr0n ?eqxx // eqr_pMn2r. Qed.

(* More characteristic zero properties. *)

Lemma mulrn_eq0 x n : (x *+ n == 0) = ((n == 0)%N || (x == 0)).
Proof. by rewrite -mulr_natl mulf_eq0 pnatr_eq0. Qed.

Lemma eqNr x : (- x == x) = (x == 0).
Proof. by rewrite eq_sym -addr_eq0 -mulr2n mulrn_eq0. Qed.

Lemma mulrIn x : x != 0 -> injective (GRing.natmul x).
Proof.
move=> x_neq0 m n; without loss /subnK <-: m n / (n <= m)%N.
  by move=> IH eq_xmn; case/orP: (leq_total m n) => /IH->.
by move/eqP; rewrite mulrnDr -subr_eq0 addrK mulrn_eq0 => /predU1P[-> | /idPn].
Qed.

Definition miditv (i : interval R) : R :=
  match i with
  | Interval (BSide _ a) (BSide _ b) => (a + b) / 2%:R
  | Interval -oo%O (BSide _ b) => b - 1
  | Interval (BSide _ a) +oo%O => a + 1
  | Interval -oo%O +oo%O => 0
  | _ => 0
  end.

End porderedidomain_theory.

Section numidomain_theory.
Context (R : numPOrderedIdomainType).
Implicit Types x y : R.

Local Fact real_semiring_closed : semiring_closed (@real R).
Proof. by split; [exact: rpred0D|exact: rpred1M]. Qed.
#[export]
HB.instance Definition _ :=
  GRing.isSemiringClosed.Build R real_num_pred real_semiring_closed.

Local Fact real_invr_closed : invr_closed (@real R).
Proof.
move=> /= x xR.
case: (boolP (x \is a GRing.unit)) => [xu|/invr_out -> //].
have x0 : x != 0 by apply: contraPneq xu => ->; rewrite unitr0.
by rewrite -(realMr x^-1 x0 xR) divrr // realE ler01.
Qed.
#[export]
HB.instance Definition _ :=
  GRing.isInvClosed.Build R real_num_pred real_invr_closed.

Lemma invr_gt0 (x : R) : (0 < x^-1) = (0 < x).
Proof.
case: (boolP (x \is a GRing.unit)) => [xu|/invr_out -> //].
wlog suff hinv : x xu / 0 < x -> 0 < x^-1.
  apply/idP/idP; last exact: hinv.
  by move/hinv; rewrite invrK unitrV; apply.
rewrite -(divrK xu x^-1) => x0.
apply: mulr_gt0 => //.
have : x^-1 \is real by apply/real_invr_closed/gtr0_real.
rewrite realE !le_eqVlt (eq_sym 0) invr_eq0 gt_eqF //=.
case/orP => i0. 
- exact: mulr_gt0.
- by rewrite -mulrNN mulr_gt0 ?oppr_gt0.
Qed.

Lemma invr_ge0 (x : R) : (0 <= x^-1) = (0 <= x).
Proof. by rewrite !le_eqVlt !(eq_sym 0) invr_eq0 invr_gt0. Qed.

Local Fact pos_invr_closed : invr_closed (@pos R).
Proof.
by move=> /= x; rewrite !posrE invr_gt0.
Qed.
#[export]
HB.instance Definition _ :=
  GRing.isInvClosed.Build R pos_num_pred pos_invr_closed.

Local Fact nneg_invr_closed : invr_closed (@nneg R).
Proof. by move=> /= x; rewrite !nnegrE invr_ge0. Qed.
#[export]
HB.instance Definition _ :=
  GRing.isInvClosed.Build R nneg_num_pred nneg_invr_closed.

Lemma pmulr_rge0 x y : 0 < x -> (0 <= x * y) = (0 <= y).
Proof.
rewrite !le_eqVlt => /[dup] x_gt0 /pmulr_rgt0 ->; congr orb.
by rewrite !(eq_sym 0) mulrI_eq0 //; apply/lregP/lt0r_neq0.
Qed.

(* mulr and ler/ltr *)

Lemma ler_pM2l x : 0 < x -> {mono *%R x : x y / x <= y}.
Proof.
by move=> x_gt0 y z; rewrite -subr_ge0 -mulrBr pmulr_rge0 // subr_ge0.
Qed.

Definition lter_pM2l := (ler_pM2l, ltr_pM2l).

Lemma ler_pM2r x : 0 < x -> {mono *%R^~ x : x y / x <= y}.
Proof. by move=> x_gt0 y z /=; rewrite ![_ * x]mulrC ler_pM2l. Qed.

Definition lter_pM2r := (ler_pM2r, ltr_pM2r).

Lemma ler_nM2l x : x < 0 -> {mono *%R x : x y /~ x <= y}.
Proof. by move=> x_lt0 y z /=; rewrite -lerN2 -!mulNr ler_pM2l ?oppr_gt0. Qed.

Definition lter_nM2l := (ler_nM2l, ltr_nM2l).

Lemma ler_nM2r x : x < 0 -> {mono *%R^~ x : x y /~ x <= y}.
Proof. by move=> x_lt0 y z /=; rewrite ![_ * x]mulrC ler_nM2l. Qed.

Definition lter_nM2r := (ler_nM2r, ltr_nM2r).

Lemma ler_pMn2r n : (0 < n)%N -> {mono (@GRing.natmul R)^~ n : x y / x <= y}.
Proof.
by case: n => // n _ x y /=; rewrite -mulr_natl -[y *+ _]mulr_natl ler_pM2l.
Qed.

Lemma pmulrn_lge0 x n : (0 < n)%N -> (0 <= x *+ n) = (0 <= x).
Proof. by move=> n_gt0; rewrite -(mul0rn _ n) ler_pMn2r // mul0rn. Qed.

Lemma pmulrn_lle0 x n : (0 < n)%N -> (x *+ n <= 0) = (x <= 0).
Proof. by move=> n_gt0; rewrite -(mul0rn _ n) ler_pMn2r // mul0rn. Qed.

(* (x * y) compared to 0 *)

(* x positive and y right *)

Lemma pmulr_rle0 x y : 0 < x -> (x * y <= 0) = (y <= 0).
Proof.
by move=> x_gt0; rewrite -[LHS]oppr_ge0 -mulrN pmulr_rge0 // oppr_ge0.
Qed.

(* x positive and y left *)

Lemma pmulr_lge0 x y : 0 < x -> (0 <= y * x) = (0 <= y).
Proof. by move=> x_gt0; rewrite mulrC pmulr_rge0. Qed.

Lemma pmulr_lle0 x y : 0 < x -> (y * x <= 0) = (y <= 0).
Proof. by move=> x_gt0; rewrite mulrC pmulr_rle0. Qed.

(* x negative and y right *)

Lemma nmulr_rge0 x y : x < 0 -> (0 <= x * y) = (y <= 0).
Proof. by move=> x_lt0; rewrite -mulrNN pmulr_rge0 lterNE. Qed.

Lemma nmulr_rle0 x y : x < 0 -> (x * y <= 0) = (0 <= y).
Proof. by move=> x_lt0; rewrite -mulrNN pmulr_rle0 lterNE. Qed.

(* x negative and y left *)

Lemma nmulr_lge0 x y : x < 0 -> (0 <= y * x) = (y <= 0).
Proof. by move=> x_lt0; rewrite mulrC nmulr_rge0. Qed.

Lemma nmulr_lle0 x y : x < 0 -> (y * x <= 0) = (0 <= y).
Proof. by move=> x_lt0; rewrite mulrC nmulr_rle0. Qed.

(* ler/ltr and multiplication between a positive/negative *)

Lemma ger_pMl x y : 0 < y -> (x * y <= y) = (x <= 1).
Proof. by move=> hy; rewrite -{2}[y]mul1r ler_pM2r. Qed.

Lemma ger_pMr x y : 0 < y -> (y * x <= y) = (x <= 1).
Proof. by move=> hy; rewrite -{2}[y]mulr1 ler_pM2l. Qed.

Lemma ler_pMl x y : 0 < y -> (y <= x * y) = (1 <= x).
Proof. by move=> hy; rewrite -{1}[y]mul1r ler_pM2r. Qed.

Lemma ler_pMr x y : 0 < y -> (y <= y * x) = (1 <= x).
Proof. by move=> hy; rewrite -{1}[y]mulr1 ler_pM2l. Qed.

Lemma ger_nMl x y : y < 0 -> (x * y <= y) = (1 <= x).
Proof. by move=> hy; rewrite -{2}[y]mul1r ler_nM2r. Qed.

Lemma ger_nMr x y : y < 0 -> (y * x <= y) = (1 <= x).
Proof. by move=> hy; rewrite -{2}[y]mulr1 ler_nM2l. Qed.

Lemma ler_nMl x y : y < 0 -> (y <= x * y) = (x <= 1).
Proof. by move=> hy; rewrite -{1}[y]mul1r ler_nM2r. Qed.

Lemma ler_nMr x y : y < 0 -> (y <= y * x) = (x <= 1).
Proof. by move=> hy; rewrite -{1}[y]mulr1 ler_nM2l. Qed.

Lemma lerMn2r n x y : (x *+ n <= y *+ n) = ((n == 0) || (x <= y)).
Proof. by case: n => [|n]; rewrite ?lexx ?eqxx // ler_pMn2r. Qed.

(* ler and ^-1 *)

Lemma invr_lt0 x : (x^-1 < 0) = (x < 0).
Proof. by rewrite -oppr_cp0 -invrN invr_gt0 oppr_cp0. Qed.

Lemma invr_le0 x : (x^-1 <= 0) = (x <= 0).
Proof. by rewrite -oppr_cp0 -invrN invr_ge0 oppr_cp0. Qed.

Definition invr_gte0 := (invr_ge0, invr_gt0).
Definition invr_lte0 := (invr_le0, invr_lt0).

Lemma divr_ge0 x y : 0 <= x -> 0 <= y -> 0 <= x / y.
Proof. by move=> x_ge0 y_ge0; rewrite mulr_ge0 ?invr_ge0. Qed.

Lemma divDl_ge0 x y : 0 <= x -> 0 <= y -> 0 <= x / (x + y).
Proof. by move=> *; rewrite divr_ge0// addr_ge0. Qed.

Lemma divr_gt0 x y : 0 < x -> 0 < y -> 0 < x / y.
Proof. by move=> x_gt0 y_gt0; rewrite pmulr_rgt0 ?invr_gt0. Qed.

Lemma realV : {mono (@GRing.inv R) : x / x \is real}.
Proof. exact: rpredV. Qed.

Lemma ler_pV2 :
  {in [pred x in GRing.unit | 0 < x] &, {mono (@GRing.inv R) : x y /~ x <= y}}.
Proof.
move=> x y /andP [ux hx] /andP [uy hy] /=.
by rewrite -(ler_pM2l hx) -(ler_pM2r hy) !(divrr, mulrVK) ?unitf_gt0 // mul1r.
Qed.

Lemma ler_nV2 :
  {in [pred x in GRing.unit | x < 0] &, {mono (@GRing.inv R) : x y /~ x <= y}}.
Proof.
move=> x y /andP [ux hx] /andP [uy hy] /=.
by rewrite -(ler_nM2l hx) -(ler_nM2r hy) !(divrr, mulrVK) ?unitf_lt0 // mul1r.
Qed.

Lemma ltr_pV2 :
  {in [pred x in GRing.unit | 0 < x] &, {mono (@GRing.inv R) : x y /~ x < y}}.
Proof. exact: leW_nmono_in ler_pV2. Qed.

Lemma ltr_nV2 :
  {in [pred x in GRing.unit | x < 0] &, {mono (@GRing.inv R) : x y /~ x < y}}.
Proof. exact: leW_nmono_in ler_nV2. Qed.

Lemma invr_gt1 x : x \is a GRing.unit -> 0 < x -> (1 < x^-1) = (x < 1).
Proof.
by move=> Ux xgt0; rewrite -{1}[1]invr1 ltr_pV2 ?inE ?unitr1 ?ltr01 ?Ux.
Qed.

Lemma invr_ge1 x : x \is a GRing.unit -> 0 < x -> (1 <= x^-1) = (x <= 1).
Proof.
by move=> Ux xgt0; rewrite -{1}[1]invr1 ler_pV2 ?inE ?unitr1 ?ltr01 // Ux.
Qed.

Definition invr_gte1 := (invr_ge1, invr_gt1).

Lemma invr_le1 x (ux : x \is a GRing.unit) (hx : 0 < x) :
  (x^-1 <= 1) = (1 <= x).
Proof. by rewrite -invr_ge1 ?invr_gt0 ?unitrV // invrK. Qed.

Lemma invr_lt1 x (ux : x \is a GRing.unit) (hx : 0 < x) : (x^-1 < 1) = (1 < x).
Proof. by rewrite -invr_gt1 ?invr_gt0 ?unitrV // invrK. Qed.

Definition invr_lte1 := (invr_le1, invr_lt1).
Definition invr_cp1 := (invr_gte1, invr_lte1).

(* max and min *)

Lemma minr_pMr x y z : 0 <= x -> x * min y z = min (x * y) (x * z).
Proof.
have [|x_gt0||->]// := comparableP x; last by rewrite !mul0r minxx.
by rewrite !(fun_if, if_arg) lter_pM2l//; case: (y < z).
Qed.

Lemma maxr_pMr x y z : 0 <= x -> x * max y z = max (x * y) (x * z).
Proof.
have [|x_gt0||->]// := comparableP x; last by rewrite !mul0r maxxx.
by rewrite !(fun_if, if_arg) lter_pM2l//; case: (y < z).
Qed.

Lemma minr_pMl x y z : 0 <= x -> min y z * x = min (y * x) (z * x).
Proof. by move=> *; rewrite mulrC minr_pMr // ![_ * x]mulrC. Qed.

Lemma maxr_pMl x y z : 0 <= x -> max y z * x = max (y * x) (z * x).
Proof. by move=> *; rewrite mulrC maxr_pMr // ![_ * x]mulrC. Qed.

Section RealDomainArgExtremum.

Context {I : finType} (i0 : I).
Context (P : pred I) (F : I -> R) (Pi0 : P i0).
Hypothesis F_real : {in P, forall i, F i \is real}.

Lemma real_arg_minP : extremum_spec <=%R P F [arg min_(i < i0 | P i) F i]%O.
Proof.
by apply: comparable_arg_minP => // i j iP jP; rewrite real_comparable ?F_real.
Qed.

Lemma real_arg_maxP : extremum_spec >=%R P F [arg max_(i > i0 | P i) F i]%O.
Proof.
by apply: comparable_arg_maxP => // i j iP jP; rewrite real_comparable ?F_real.
Qed.

End RealDomainArgExtremum.

(* Ternary sign (sg). *)

Lemma sgrMn x n : sg (x *+ n) = (n != 0)%:R * sg x.
Proof.
case: n => [|n]; first by rewrite mulr0n sgr0 mul0r.
by rewrite !sgr_def mulrn_eq0 mul1r pmulrn_llt0.
Qed.

(* leif *)

Lemma leif_pM x1 x2 y1 y2 C1 C2 :
    0 <= x1 -> 0 <= x2 -> x1 <= y1 ?= iff C1 -> x2 <= y2 ?= iff C2 ->
  x1 * x2 <= y1 * y2 ?= iff (y1 * y2 == 0) || C1 && C2.
Proof.
move=> x1_ge0 x2_ge0 le_xy1 le_xy2; have [y_0 | ] := eqVneq _ 0.
  apply/leifP; rewrite y_0 /= mulf_eq0 !eq_le x1_ge0 x2_ge0 !andbT.
  move/eqP: y_0; rewrite mulf_eq0.
  by case/pred2P=> <-; rewrite (le_xy1, le_xy2) ?orbT.
rewrite /= mulf_eq0 => /norP[y1nz y2nz].
have y1_gt0: 0 < y1 by rewrite lt_def y1nz (le_trans _ le_xy1).
have [x2_0 | x2nz] := eqVneq x2 0.
  apply/leifP; rewrite -le_xy2 x2_0 eq_sym (negPf y2nz) andbF mulr0.
  by rewrite mulr_gt0 // lt_def y2nz -x2_0 le_xy2.
have:= le_xy2; rewrite -[X in X -> _](mono_leif (ler_pM2l y1_gt0)).
by apply: leif_trans; rewrite (mono_leif (ler_pM2r _)) // lt_def x2nz.
Qed.

Lemma leif_nM x1 x2 y1 y2 C1 C2 :
    y1 <= 0 -> y2 <= 0 -> x1 <= y1 ?= iff C1 -> x2 <= y2 ?= iff C2 ->
  y1 * y2 <= x1 * x2 ?= iff (x1 * x2 == 0) || C1 && C2.
Proof.
rewrite -!oppr_ge0 -mulrNN -[x1 * x2]mulrNN => y1le0 y2le0 le_xy1 le_xy2.
by apply: leif_pM => //; rewrite (nmono_leif lerN2).
Qed.

Lemma leif_pprod (I : finType) (P C : pred I) (E1 E2 : I -> R) :
    (forall i, P i -> 0 <= E1 i) ->
    (forall i, P i -> E1 i <= E2 i ?= iff C i) ->
  let pi E := \prod_(i | P i) E i in
  pi E1 <= pi E2 ?= iff (pi E2 == 0) || [forall (i | P i), C i].
Proof.
move=> E1_ge0 leE12 /=; rewrite -big_andE; elim/(big_load (fun x => 0 <= x)): _.
elim/big_rec3: _ => [|i Ci m2 m1 Pi [m1ge0 le_m12]].
  by split=> //; apply/leifP; rewrite orbT.
have Ei_ge0 := E1_ge0 i Pi; split; first by rewrite mulr_ge0.
congr (leif _ _ _): (leif_pM Ei_ge0 m1ge0 (leE12 i Pi) le_m12).
by rewrite mulf_eq0 -!orbA; congr (_ || _); rewrite !orb_andr orbA orbb.
Qed.

(* lteif *)

Lemma lteif_pM2l C x : 0 < x -> {mono *%R x : y z / y < z ?<= if C}.
Proof. by case: C => ? ? ?; rewrite /= lter_pM2l. Qed.

Lemma lteif_pM2r C x : 0 < x -> {mono *%R^~ x : y z / y < z ?<= if C}.
Proof. by case: C => ? ? ?; rewrite /= lter_pM2r. Qed.

Lemma lteif_nM2l C x : x < 0 -> {mono *%R x : y z /~ y < z ?<= if C}.
Proof. by case: C => ? ? ?; rewrite /= lter_nM2l. Qed.

Lemma lteif_nM2r C x : x < 0 -> {mono *%R^~ x : y z /~ y < z ?<= if C}.
Proof. by case: C => ? ? ?; rewrite /= lter_nM2r. Qed.

Lemma real_lteifNE x y C : x \is Num.real -> y \is Num.real ->
  (x < y ?<= if ~~ C) = ~~ (y < x ?<= if C).
Proof. by move=> ? ?; rewrite comparable_lteifNE ?real_comparable. Qed.

(* Mean inequalities. *)

Lemma real_leif_mean_square_scaled x y :
  x \is real -> y \is real -> x * y *+ 2 <= x ^+ 2 + y ^+ 2 ?= iff (x == y).
Proof.
move=> Rx Ry; rewrite -[_ *+ 2]add0r -leifBRL addrAC -sqrrB -subr_eq0.
by rewrite -sqrf_eq0 eq_sym; apply/leif_eq/real_sqr/rpredB.
Qed.

Lemma real_leif_AGM2_scaled x y :
  x \is real -> y \is real -> x * y *+ 4 <= (x + y) ^+ 2 ?= iff (x == y).
Proof.
move=> Rx Ry; rewrite sqrrD addrAC (mulrnDr _ 2) -leifBLR addrK.
exact: real_leif_mean_square_scaled.
Qed.

Lemma leif_AGM_scaled (I : finType) (A : {pred I}) (E : I -> R) (n := #|A|) :
    {in A, forall i, 0 <= E i *+ n} ->
  \prod_(i in A) (E i *+ n) <= (\sum_(i in A) E i) ^+ n
                            ?= iff [forall i in A, forall j in A, E i == E j].
Proof.
have [m leAm] := ubnP #|A|; elim: m => // m IHm in A leAm E n * => Ege0.
apply/leifP; case: ifPn => [/forall_inP-Econstant | Enonconstant].
  have [i /= Ai | A0] := pickP [in A]; last by rewrite [n]eq_card0 ?big_pred0.
  have /eqfun_inP-E_i := Econstant i Ai; rewrite -(eq_bigr _ E_i) sumr_const.
  by rewrite exprMn_n prodrMn_const -(eq_bigr _ E_i) prodr_const.
set mu := \sum_(i in A) E i; pose En i := E i *+ n.
pose cmp_mu s := [pred i | s * mu < s * En i].
have{Enonconstant} has_cmp_mu e (s := (-1) ^+ e): {i | i \in A & cmp_mu s i}.
  apply/sig2W/exists_inP; apply: contraR Enonconstant => /exists_inPn-mu_s_A.
  have n_gt0 i: i \in A -> (0 < n)%N by rewrite [n](cardD1 i) => ->.
  have{} mu_s_A i: i \in A -> s * En i <= s * mu.
    move=> Ai; rewrite real_leNgt ?mu_s_A ?rpredMsign ?ger0_real ?Ege0 //.
    by rewrite -(pmulrn_lge0 _ (n_gt0 i Ai)) -sumrMnl sumr_ge0.
  have [_ /esym/eqfun_inP] := leif_sum (fun i Ai => leif_eq (mu_s_A i Ai)).
  rewrite sumr_const -/n -mulr_sumr sumrMnl -/mu mulrnAr eqxx => A_mu.
  apply/forall_inP=> i Ai; apply/eqfun_inP=> j Aj.
  by apply: (pmulrnI (n_gt0 i Ai)); apply: (can_inj (signrMK e)); rewrite !A_mu.
have [[i Ai Ei_lt_mu] [j Aj Ej_gt_mu]] := (has_cmp_mu 1, has_cmp_mu 0)%N.
rewrite {cmp_mu has_cmp_mu}/= !mul1r !mulN1r ltrN2 in Ei_lt_mu Ej_gt_mu.
pose A' := [predD1 A & i]; pose n' := #|A'|.
have [Dn n_gt0]: n = n'.+1 /\ (n > 0)%N  by rewrite [n](cardD1 i) Ai.
have i'j: j != i by apply: contraTneq Ej_gt_mu => ->; rewrite lt_gtF.
have{i'j} A'j: j \in A' by rewrite !inE Aj i'j.
have mu_gt0: 0 < mu := le_lt_trans (Ege0 i Ai) Ei_lt_mu.
rewrite (bigD1 i) // big_andbC (bigD1 j) //= mulrA; set pi := \prod_(k | _) _.
have [-> | nz_pi] := eqVneq pi 0; first by rewrite !mulr0 exprn_gt0.
have{nz_pi} pi_gt0: 0 < pi.
  by rewrite lt_def nz_pi prodr_ge0 // => k /andP[/andP[_ /Ege0]].
rewrite -/(En i) -/(En j); pose E' := [eta En with j |-> En i + En j - mu].
have E'ge0 k: k \in A' -> E' k *+ n' >= 0.
  case/andP=> /= _ Ak; apply: mulrn_wge0; case: ifP => _; last exact: Ege0.
  by rewrite subr_ge0 ler_wpDl ?Ege0 // ltW.
rewrite -/n Dn in leAm; have{leAm IHm E'ge0}: _ <= _ := IHm _ leAm _ E'ge0.
have ->: \sum_(k in A') E' k = mu *+ n'.
  apply: (addrI mu); rewrite -mulrS -Dn -sumrMnl (bigD1 i Ai) big_andbC /=.
  rewrite !(bigD1 j A'j) /= eqxx addrA subrKC addrA; congr (_ + _).
  by apply: eq_bigr => k /andP[_ /negPf->].
rewrite prodrMn_const exprMn_n -/n' ler_pMn2r ?expn_gt0; first by case: (n').
have ->: \prod_(k in A') E' k = E' j * pi.
  by rewrite (bigD1 j) //=; congr *%R; apply: eq_bigr => k /andP[_ /negPf->].
rewrite -(ler_pM2l mu_gt0) -exprS -Dn mulrA; apply: lt_le_trans.
rewrite ltr_pM2r //= eqxx -addrA mulrDr mulrC -ltrBlDl -mulrBl.
by rewrite mulrC ltr_pM2r ?subr_gt0.
Qed.

End numidomain_theory.

Arguments invr_ge0 [R].
Arguments invr_gt0 [R].
Arguments lerMn2r {R}.

Section orderedidomain_theory.
Context (R : orderedIdomainType).

Implicit Types x y z t : R.
Let numR_real := @num_real R.
Hint Resolve numR_real : core.

Lemma sgr_cp0 x :
  ((sg x == 1) = (0 < x)) *
  ((sg x == -1) = (x < 0)) *
  ((sg x == 0) = (x == 0)).
Proof.
rewrite -[1]/((-1) ^+ false) -signrN lt0r leNgt sgr_def.
case: (x =P 0) => [-> | _]; first by rewrite !(eq_sym 0) !signr_eq0 ltxx eqxx.
by rewrite !(inj_eq signr_inj) eqb_id eqbF_neg signr_eq0 //.
Qed.

Lemma sgrM x y : sg (x * y) = sg x * sg y.
Proof.
rewrite !sgr_def mulr_lt0 andbA mulrnAr mulrnAl -mulrnA mulnb -negb_or mulf_eq0.
by case: (~~ _) => //; rewrite signr_addb.
Qed.

Lemma sgrN x : sg (- x) = - sg x.
Proof. by rewrite -mulrN1 sgrM sgrN1 mulrN1. Qed.

Lemma sgrX n x : sg (x ^+ n) = (sg x) ^+ n.
Proof. by elim: n => [|n IHn]; rewrite ?sgr1 // !exprS sgrM IHn. Qed.

Lemma sgr_smul x y : sg (sg x * y) = sg x * sg y.
Proof. by rewrite sgrM sgr_id. Qed.

Lemma sgr_gt0 x : (sg x > 0) = (x > 0).
Proof. by rewrite -[LHS]sgr_cp0 sgr_id sgr_cp0. Qed.

Lemma sgr_ge0 x : (sgr x >= 0) = (x >= 0).
Proof. by rewrite !leNgt sgr_lt0. Qed.

Lemma exprn_even_ge0 n x : ~~ odd n -> 0 <= x ^+ n.
Proof. by move=> even_n; rewrite real_exprn_even_ge0 ?num_real. Qed.

Lemma exprn_even_gt0 n x : ~~ odd n -> (0 < x ^+ n) = (n == 0)%N || (x != 0).
Proof. by move=> even_n; rewrite real_exprn_even_gt0 ?num_real. Qed.

Lemma exprn_even_le0 n x : ~~ odd n -> (x ^+ n <= 0) = (n != 0) && (x == 0).
Proof. by move=> even_n; rewrite real_exprn_even_le0 ?num_real. Qed.

Lemma exprn_even_lt0 n x : ~~ odd n -> (x ^+ n < 0) = false.
Proof. by move=> even_n; rewrite real_exprn_even_lt0 ?num_real. Qed.

Lemma exprn_odd_ge0 n x : odd n -> (0 <= x ^+ n) = (0 <= x).
Proof. by move=> even_n; rewrite real_exprn_odd_ge0 ?num_real. Qed.

Lemma exprn_odd_gt0 n x : odd n -> (0 < x ^+ n) = (0 < x).
Proof. by move=> even_n; rewrite real_exprn_odd_gt0 ?num_real. Qed.

Lemma exprn_odd_le0 n x : odd n -> (x ^+ n <= 0) = (x <= 0).
Proof. by move=> even_n; rewrite real_exprn_odd_le0 ?num_real. Qed.

Lemma exprn_odd_lt0 n x : odd n -> (x ^+ n < 0) = (x < 0).
Proof. by move=> even_n; rewrite real_exprn_odd_lt0 ?num_real. Qed.

(* Special lemmas for squares. *)

Lemma sqr_ge0 x : 0 <= x ^+ 2. Proof. by rewrite exprn_even_ge0. Qed.

Lemma leif_mean_square_scaled x y :
  x * y *+ 2 <= x ^+ 2 + y ^+ 2 ?= iff (x == y).
Proof. exact: real_leif_mean_square_scaled. Qed.

Lemma leif_AGM2_scaled x y : x * y *+ 4 <= (x + y) ^+ 2 ?= iff (x == y).
Proof. exact: real_leif_AGM2_scaled. Qed.

Section MinMax.

Lemma oppr_max : {morph -%R : x y / max x y >-> min x y : R}.
Proof. by move=> x y; apply: real_oppr_max. Qed.

Lemma oppr_min : {morph -%R : x y / min x y >-> max x y : R}.
Proof. by move=> x y; apply: real_oppr_min. Qed.

Lemma addr_minl : @left_distributive R R +%R min.
Proof. by move=> x y z; apply: real_addr_minl. Qed.

Lemma addr_minr : @right_distributive R R +%R min.
Proof. by move=> x y z; apply: real_addr_minr. Qed.

Lemma addr_maxl : @left_distributive R R +%R max.
Proof. by move=> x y z; apply: real_addr_maxl. Qed.

Lemma addr_maxr : @right_distributive R R +%R max.
Proof. by move=> x y z; apply: real_addr_maxr. Qed.

Lemma minr_nMr x y z : x <= 0 -> x * min y z = max (x * y) (x * z).
Proof. by move=> x_le0; apply: real_minr_nMr. Qed.

Lemma maxr_nMr x y z : x <= 0 -> x * max y z = min (x * y) (x * z).
Proof. by move=> x_le0; apply: real_maxr_nMr. Qed.

Lemma minr_nMl x y z : x <= 0 -> min y z * x = max (y * x) (z * x).
Proof. by move=> x_le0; apply: real_minr_nMl. Qed.

Lemma maxr_nMl x y z : x <= 0 -> max y z * x = min (y * x) (z * x).
Proof. by move=> x_le0; apply: real_maxr_nMl. Qed.

End MinMax.

End orderedidomain_theory.

End Theory.

(*************)
(* FACTORIES *)
(*************)

HB.factory Record NzRing_isStrictPOrdered R 
    & Num.POrderZmodule R & GRing.NzRing R := {
  ler_wD2l : forall x : R, {homo +%R x : y z / (y <= z)%O};
  ler01 : 0 <= 1 :> R;
  mulr_gt0 : forall x y : R, 0 < x -> 0 < y -> 0 < x * y
}.
HB.builders Context R & NzRing_isStrictPOrdered R.

Let mulr_ge0 (x y : R) : 0 <= x -> 0 <= y -> 0 <= x * y.
Proof.
rewrite !le_eqVlt => /predU1P[<-|x0] /predU1P[<-|y0].
- by rewrite mulr0 eqxx.
- by rewrite mul0r eqxx.
- by rewrite mulr0 eqxx.
by apply/orP; right; apply: mulr_gt0.
Qed.

HB.instance Definition _ := Add_isHomo.Build R ler_wD2l.
HB.instance Definition _ := Ring_isPOrdered.Build R ler01 mulr_ge0.
HB.instance Definition _ := POrderRing_isStrictPOrdered.Build R mulr_gt0.

HB.end.

HB.factory Record NzRing_isStrictOrdered R 
    & Num.OrderZmodule R & GRing.NzRing R := {
  ler_wD2l : forall x : R, {homo +%R x : y z / (y <= z)%O};
  ler01 : 0 <= 1 :> R;
  mulr_gt0 : forall x y : R, 0 < x -> 0 < y -> 0 < x * y
}.
HB.builders Context R & NzRing_isStrictOrdered R.

HB.instance Definition _ :=
  NzRing_isStrictPOrdered.Build R ler_wD2l ler01 mulr_gt0.

Let trans_cmp : transitive (>=<%R : rel R).
Proof. by []. Qed.

Let mulr_ge0 (x y : R) : 0 <= x -> 0 <= y -> 0 <= x * y.
Proof.
rewrite !le_eqVlt => /predU1P[<-|x0] /predU1P[<-|y0].
- by rewrite mulr0 eqxx.
- by rewrite mul0r eqxx.
- by rewrite mulr0 eqxx.
by apply/orP; right; apply: mulr_gt0.
Qed.

Let num_real (x : R) : x \is real.
Proof. exact: le_total. Qed.

Let realrM (x y : R) :
  x != 0 -> x \is real -> (x * y \is real) = (y \is real).
Proof. by move=> _ _; rewrite !num_real. Qed.

Let realMr (x y : R) :
  y != 0 -> y \is real -> (x * y \is real) = (x \is real).
Proof. by move=> _ _; rewrite !num_real. Qed.

HB.instance Definition _ := POrderedZmodule_hasTransCmp.Build R trans_cmp.
HB.instance Definition _ := Ring_hasNumMul.Build R realrM realMr.

HB.end.

Module Exports. HB.reexport. End Exports.
End Num.
Export Num.Exports.