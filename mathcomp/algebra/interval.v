(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import div fintype bigop order ssralg finset fingroup.
From mathcomp Require Import ssrnum.

(******************************************************************************)
(* This file provide support for intervals in ordered types. The datatype     *)
(* (interval T) gives a formal characterization of an interval, as the pair   *)
(* of its right and left bounds.                                              *)
(*    interval T    == the type of formal intervals on T.                     *)
(*    x \in i       == when i is a formal interval on an ordered type,        *)
(*                     \in can be used to test membership.                    *)
(*    itvP x_in_i   == where x_in_i has type x \in i, if i is ground,         *)
(*                     gives a set of rewrite rules that x_in_i imply.        *)
(*                                                                            *)
(* Intervals of T form an partially ordered type (porderType) whose ordering  *)
(* is the subset relation. If T is a lattice, intervals also form a lattice   *)
(* (latticeType) whose meet and join are intersection and convex hull         *)
(* respectively. They are distributive if T is an orderType.                  *)
(*                                                                            *)
(* We provide a set of notations to write intervals (see below)               *)
(* `[a, b], `]a, b], ..., `]-oo, a], ..., `]-oo, +oo[                         *)
(* We also provide the lemma subitvP which computes the inequalities one      *)
(* needs to prove when trying to prove the inclusion of intervals.            *)
(*                                                                            *)
(* Remark that we cannot implement a boolean comparison test for intervals on *)
(* an arbitrary ordered types, for this problem might be undecidable. Note    *)
(* also that type (interval R) may contain several inhabitants coding for the *)
(* same interval. However, this pathological issues do nor arise when R is a  *)
(* real domain: we could provide a specific theory for this important case.   *)
(*                                                                            *)
(* See also ``Formal proofs in real algebraic geometry: from ordered fields   *)
(* to quantifier elimination'', LMCS journal, 2012                            *)
(* by Cyril Cohen and Assia Mahboubi                                          *)
(*                                                                            *)
(* And "Formalized algebraic numbers: construction and first-order theory"    *)
(* Cyril Cohen, PhD, 2012, section 4.3.                                       *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope order_scope.
Import Order.TTheory.

Variant itv_bound (T : Type) : Type := BSide of bool & T | BInfty of bool.
Notation BLeft := (BSide true).
Notation BRight := (BSide false).
Notation "'-oo'" := (BInfty _ true) (at level 0) : order_scope.
Notation "'+oo'" := (BInfty _ false) (at level 0) : order_scope.
Variant interval (T : Type) := Interval of itv_bound T & itv_bound T.

(* We provide the 9 following notations to help writing formal intervals *)
Notation "`[ a , b ]" := (Interval (BLeft a) (BRight b))
  (at level 0, a, b at level 9 , format "`[ a ,  b ]") : order_scope.
Notation "`] a , b ]" := (Interval (BRight a) (BRight b))
  (at level 0, a, b at level 9 , format "`] a ,  b ]") : order_scope.
Notation "`[ a , b [" := (Interval (BLeft a) (BLeft b))
  (at level 0, a, b at level 9 , format "`[ a ,  b [") : order_scope.
Notation "`] a , b [" := (Interval (BRight a) (BLeft b))
  (at level 0, a, b at level 9 , format "`] a ,  b [") : order_scope.
Notation "`] '-oo' , b ]" := (Interval -oo (BRight b))
  (at level 0, b at level 9 , format "`] '-oo' ,  b ]") : order_scope.
Notation "`] '-oo' , b [" := (Interval -oo (BLeft b))
  (at level 0, b at level 9 , format "`] '-oo' ,  b [") : order_scope.
Notation "`[ a , '+oo' [" := (Interval (BLeft a) +oo)
  (at level 0, a at level 9 , format "`[ a ,  '+oo' [") : order_scope.
Notation "`] a , '+oo' [" := (Interval (BRight a) +oo)
  (at level 0, a at level 9 , format "`] a ,  '+oo' [") : order_scope.
Notation "`] -oo , '+oo' [" := (Interval -oo +oo)
  (at level 0, format "`] -oo ,  '+oo' [") : order_scope.

Notation "`[ a , b ]" := (Interval (BLeft a) (BRight b))
  (at level 0, a, b at level 9 , format "`[ a ,  b ]") : ring_scope.
Notation "`] a , b ]" := (Interval (BRight a) (BRight b))
  (at level 0, a, b at level 9 , format "`] a ,  b ]") : ring_scope.
Notation "`[ a , b [" := (Interval (BLeft a) (BLeft b))
  (at level 0, a, b at level 9 , format "`[ a ,  b [") : ring_scope.
Notation "`] a , b [" := (Interval (BRight a) (BLeft b))
  (at level 0, a, b at level 9 , format "`] a ,  b [") : ring_scope.
Notation "`] '-oo' , b ]" := (Interval -oo (BRight b))
  (at level 0, b at level 9 , format "`] '-oo' ,  b ]") : ring_scope.
Notation "`] '-oo' , b [" := (Interval -oo (BLeft b))
  (at level 0, b at level 9 , format "`] '-oo' ,  b [") : ring_scope.
Notation "`[ a , '+oo' [" := (Interval (BLeft a) +oo)
  (at level 0, a at level 9 , format "`[ a ,  '+oo' [") : ring_scope.
Notation "`] a , '+oo' [" := (Interval (BRight a) +oo)
  (at level 0, a at level 9 , format "`] a ,  '+oo' [") : ring_scope.
Notation "`] -oo , '+oo' [" := (Interval -oo +oo)
  (at level 0, format "`] -oo ,  '+oo' [") : ring_scope.

Fact itv_bound_display (disp : unit) : unit. Proof. exact. Qed.
Fact interval_display (disp : unit) : unit. Proof. exact. Qed.

Section IntervalEq.

Variable T : eqType.

Definition eq_itv_bound (b1 b2 : itv_bound T) : bool :=
  match b1, b2 with
    | BSide a x, BSide b y => (a == b) && (x == y)
    | BInfty a, BInfty b => a == b
    | _, _ => false
  end.

Lemma eq_itv_boundP : Equality.axiom eq_itv_bound.
Proof.
move=> b1 b2; apply: (iffP idP).
- by move: b1 b2 => [a x|a][b y|b] => //= [/andP [/eqP -> /eqP ->]|/eqP ->].
- by move=> <-; case: b1 => //= a x; rewrite !eqxx.
Qed.

Canonical itv_bound_eqMixin := EqMixin eq_itv_boundP.
Canonical itv_bound_eqType := EqType (itv_bound T) itv_bound_eqMixin.

Definition eqitv (x y : interval T) : bool :=
  let: Interval x x' := x in
  let: Interval y y' := y in (x == y) && (x' == y').

Lemma eqitvP : Equality.axiom eqitv.
Proof.
move=> x y; apply: (iffP idP).
- by move: x y => [x x'][y y'] => //= /andP [] /eqP -> /eqP ->.
- by move=> <-; case: x => /= x x'; rewrite !eqxx.
Qed.

Canonical interval_eqMixin := EqMixin eqitvP.
Canonical interval_eqType := EqType (interval T) interval_eqMixin.

End IntervalEq.

Module IntervalChoice.
Section IntervalChoice.

Variable T : choiceType.

Lemma itv_bound_can :
  cancel (fun b : itv_bound T =>
            match b with BSide b x => (b, Some x) | BInfty b => (b, None) end)
         (fun b =>
            match b with (b, Some x) => BSide b x | (b, None) => BInfty _ b end).
Proof. by case. Qed.

Lemma interval_can :
  @cancel _ (interval T)
    (fun '(Interval b1 b2) => (b1, b2)) (fun '(b1, b2) => Interval b1 b2).
Proof. by case. Qed.

End IntervalChoice.

Module Exports.

Canonical itv_bound_choiceType (T : choiceType) :=
  ChoiceType (itv_bound T) (CanChoiceMixin (@itv_bound_can T)).
Canonical interval_choiceType (T : choiceType) :=
  ChoiceType (interval T) (CanChoiceMixin (@interval_can T)).

Canonical itv_bound_countType (T : countType) :=
  CountType (itv_bound T) (CanCountMixin (@itv_bound_can T)).
Canonical interval_countType (T : countType) :=
  CountType (interval T) (CanCountMixin (@interval_can T)).

Canonical itv_bound_finType (T : finType) :=
  FinType (itv_bound T) (CanFinMixin (@itv_bound_can T)).
Canonical interval_finType (T : finType) :=
  FinType (interval T) (CanFinMixin (@interval_can T)).

End Exports.

End IntervalChoice.
Export IntervalChoice.Exports.

Section IntervalPOrder.

Variable (disp : unit) (T : porderType disp).
Implicit Types (x y z : T) (b bl br : itv_bound T) (i : interval T).

Definition le_bound b1 b2 :=
  match b1, b2 with
    | -oo, _ | _, +oo => true
    | BSide b1 x1, BSide b2 x2 => x1 < x2 ?<= if b2 ==> b1
    | _, _ => false
  end.

Definition lt_bound b1 b2 :=
  match b1, b2 with
    | -oo, +oo | -oo, BSide _ _ | BSide _ _, +oo => true
    | BSide b1 x1, BSide b2 x2 => x1 < x2 ?<= if b1 && ~~ b2
    | _, _ => false
  end.

Lemma lt_bound_def b1 b2 : lt_bound b1 b2 = (b2 != b1) && le_bound b1 b2.
Proof. by case: b1 b2 => [[]?|[]][[]?|[]] //=; rewrite lt_def. Qed.

Lemma le_bound_refl : reflexive le_bound.
Proof. by move=> [[]?|[]] /=. Qed.

Lemma le_bound_anti : antisymmetric le_bound.
Proof. by case=> [[]?|[]] [[]?|[]] //=; case: comparableP => // ->. Qed.

Lemma le_bound_trans : transitive le_bound.
Proof.
by case=> [[]?|[]] [[]?|[]] [[]?|[]] lexy leyz //;
  apply: (lteif_imply _ (lteif_trans lexy leyz)).
Qed.

Definition itv_bound_porderMixin :=
  LePOrderMixin lt_bound_def le_bound_refl le_bound_anti le_bound_trans.
Canonical itv_bound_porderType :=
  POrderType (itv_bound_display disp) (itv_bound T) itv_bound_porderMixin.

Lemma bound_lexx c1 c2 x : (BSide c1 x <= BSide c2 x) = (c2 ==> c1).
Proof. by rewrite /<=%O /= lteifxx. Qed.

Lemma bound_ltxx c1 c2 x : (BSide c1 x < BSide c2 x) = (c1 && ~~ c2).
Proof. by rewrite /<%O /= lteifxx. Qed.

Definition subitv i1 i2 :=
  let: Interval b1l b1r := i1 in
  let: Interval b2l b2r := i2 in (b2l <= b1l) && (b1r <= b2r).

Lemma subitv_refl : reflexive subitv.
Proof. by case=> /= ? ?; rewrite !lexx. Qed.

Lemma subitv_anti : antisymmetric subitv.
Proof.
by case=> [? ?][? ?]; rewrite andbACA => /andP[] /le_anti -> /le_anti ->.
Qed.

Lemma subitv_trans : transitive subitv.
Proof.
case=> [yl yr][xl xr][zl zr] /andP [Hl Hr] /andP [Hl' Hr'] /=.
by rewrite (le_trans Hl' Hl) (le_trans Hr Hr').
Qed.

Definition interval_porderMixin :=
  LePOrderMixin (fun _ _ => erefl) subitv_refl subitv_anti subitv_trans.
Canonical interval_porderType :=
  POrderType (interval_display disp) (interval T) interval_porderMixin.

Definition pred_of_itv i : pred T := [pred x | `[x, x] <= i].

Canonical Structure itvPredType := PredType pred_of_itv.

Lemma subitvE b1l b1r b2l b2r :
  (Interval b1l b1r <= Interval b2l b2r) = (b2l <= b1l) && (b1r <= b2r).
Proof. by []. Qed.

Lemma in_itv x i :
  x \in i =
  let: Interval l u := i in
  match l with
    | BSide b lb => lb < x ?<= if b
    | BInfty b => b
  end &&
  match u with
    | BSide b ub => x < ub ?<= if ~~ b
    | BInfty b => ~~ b
  end.
Proof. by case: i => [[? ?|[]][|[]]]. Qed.

Lemma itv_boundlr bl br x :
  (x \in Interval bl br) = (bl <= BLeft x) && (BRight x <= br).
Proof. by []. Qed.

Lemma itv_splitI bl br x :
  x \in Interval bl br = (x \in Interval bl +oo) && (x \in Interval -oo br).
Proof. by rewrite !itv_boundlr andbT. Qed.

Lemma subitvP i1 i2 : i1 <= i2 -> {subset i1 <= i2}.
Proof. by move=> ? ? /le_trans; exact. Qed.

Lemma subitvPl b1l b2l br :
  b2l <= b1l -> {subset Interval b1l br <= Interval b2l br}.
Proof. by move=> ?; apply: subitvP; rewrite subitvE lexx andbT. Qed.

Lemma subitvPr bl b1r b2r :
  b1r <= b2r -> {subset Interval bl b1r <= Interval bl b2r}.
Proof. by move=> ?; apply: subitvP; rewrite subitvE lexx. Qed.

Lemma itv_xx x cl cr y :
  y \in Interval (BSide cl x) (BSide cr x) = cl && ~~ cr && (y == x).
Proof. by case: cl cr => [] []; rewrite [LHS]lteif_anti // eq_sym. Qed.

Lemma boundl_in_itv c x b : x \in Interval (BSide c x) b = c && (BRight x <= b).
Proof. by rewrite itv_boundlr bound_lexx. Qed.

Lemma boundr_in_itv c x b :
  x \in Interval b (BSide c x) = ~~ c && (b <= BLeft x).
Proof. by rewrite itv_boundlr bound_lexx implybF andbC. Qed.

Definition bound_in_itv := (boundl_in_itv, boundr_in_itv).

Lemma lt_in_itv bl br x : x \in Interval bl br -> bl < br.
Proof. by case/andP; apply/le_lt_trans. Qed.

Lemma lteif_in_itv cl cr yl yr x :
  x \in Interval (BSide cl yl) (BSide cr yr) -> yl < yr ?<= if cl && ~~ cr.
Proof. exact: lt_in_itv. Qed.

Lemma itv_ge b1 b2 : ~~ (b1 < b2) -> Interval b1 b2 =i pred0.
Proof. by move=> ltb12 y; apply/contraNF: ltb12; apply/lt_in_itv. Qed.

Definition itv_decompose i x : Prop :=
  let: Interval l u := i in
  (match l return Prop with
     | BSide b lb => lb < x ?<= if b
     | BInfty b => b
   end *
   match u return Prop with
     | BSide b ub => x < ub ?<= if ~~ b
     | BInfty b => ~~ b
   end)%type.

Lemma itv_dec : forall x i, reflect (itv_decompose i x) (x \in i).
Proof. by move=> ? [[? ?|[]][? ?|[]]]; apply: (iffP andP); case. Qed.

Arguments itv_dec {x i}.

(* we compute a set of rewrite rules associated to an interval *)
Definition itv_rewrite i x : Type :=
  let: Interval l u := i in
    (match l with
       | BLeft a => (a <= x) * (x < a = false)
       | BRight a => (a <= x) * (a < x) * (x <= a = false) * (x < a = false)
       | -oo => forall x : T, x == x
       | +oo => forall b : bool, unkeyed b = false
     end *
     match u with
       | BRight b => (x <= b) * (b < x = false)
       | BLeft b => (x <= b) * (x < b) * (b <= x = false) * (b < x = false)
       | +oo => forall x : T, x == x
       | -oo => forall b : bool, unkeyed b = false
     end *
     match l, u with
       | BLeft a, BRight b =>
         (a <= b) * (b < a = false) * (a \in `[a, b]) * (b \in `[a, b])
       | BLeft a, BLeft b =>
         (a <= b) * (a < b) * (b <= a = false) * (b < a = false)
         * (a \in `[a, b]) * (a \in `[a, b[) * (b \in `[a, b]) * (b \in `]a, b])
       | BRight a, BRight b =>
         (a <= b) * (a < b) * (b <= a = false) * (b < a = false)
         * (a \in `[a, b]) * (a \in `[a, b[) * (b \in `[a, b]) * (b \in `]a, b])
       | BRight a, BLeft b =>
         (a <= b) * (a < b) * (b <= a = false) * (b < a = false)
         * (a \in `[a, b]) * (a \in `[a, b[) * (b \in `[a, b]) * (b \in `]a, b])
       | _, _ => forall x : T, x == x
     end)%type.

Lemma itvP x i : x \in i -> itv_rewrite i x.
Proof.
case: i => [[[]a|[]][[]b|[]]] /andP [] ha hb; rewrite /= ?bound_in_itv;
  do ![split | apply/negbTE; rewrite (le_gtF, lt_geF)];
  by [|apply: ltW | move: (lteif_trans ha hb) => //=; exact: ltW].
Qed.

Arguments itvP [x i].

End IntervalPOrder.

Section IntervalLattice.

Variable (disp : unit) (T : latticeType disp).
Implicit Types (x y z : T) (b bl br : itv_bound T) (i : interval T).

Definition bound_meet bl br : itv_bound T :=
  match bl, br with
    | -oo, _ | _, -oo => -oo
    | +oo, b | b, +oo => b
    | BSide xb x, BSide yb y =>
      BSide (((x <= y) && xb) || ((y <= x) && yb)) (x `&` y)
  end.

Definition bound_join bl br : itv_bound T :=
  match bl, br with
    | -oo, b | b, -oo => b
    | +oo, _ | _, +oo => +oo
    | BSide xb x, BSide yb y =>
      BSide ((~~ (x <= y) || yb) && (~~ (y <= x) || xb)) (x `|` y)
  end.

Lemma bound_meetC : commutative bound_meet.
Proof.
case=> [? ?|[]][? ?|[]] //=; rewrite meetC; congr BSide.
by case: lcomparableP; rewrite ?orbF // orbC.
Qed.

Lemma bound_joinC : commutative bound_join.
Proof.
case=> [? ?|[]][? ?|[]] //=; rewrite joinC; congr BSide.
by case: lcomparableP; rewrite ?andbT // andbC.
Qed.

Lemma bound_meetA : associative bound_meet.
Proof.
case=> [? x|[]][? y|[]][? z|[]] //=; rewrite !lexI meetA; congr BSide.
by case: (lcomparableP x y) => [|||->]; case: (lcomparableP y z) => [|||->];
  case: (lcomparableP x z) => [|||//<-]; case: (lcomparableP x y);
  rewrite //= ?andbF ?orbF ?lexx ?orbA //; case: (lcomparableP y z).
Qed.

Lemma bound_joinA : associative bound_join.
Proof.
case=> [? x|[]][? y|[]][? z|[]] //=; rewrite !leUx joinA; congr BSide.
by case: (lcomparableP x y) => [|||->]; case: (lcomparableP y z) => [|||->];
  case: (lcomparableP x z) => [|||//<-]; case: (lcomparableP x y);
  rewrite //= ?orbT ?andbT ?lexx ?andbA //; case: (lcomparableP y z).
Qed.

Lemma bound_meetKU b2 b1 : bound_join b1 (bound_meet b1 b2) = b1.
Proof.
case: b1 b2 => [? ?|[]][? ?|[]] //=;
  rewrite ?meetKU ?joinxx ?leIl ?lexI ?lexx ?andbb //=; congr BSide.
by case: lcomparableP; rewrite ?orbF /= ?andbb ?orbK.
Qed.

Lemma bound_joinKI b2 b1 : bound_meet b1 (bound_join b1 b2) = b1.
Proof.
case: b1 b2 => [? ?|[]][? ?|[]] //=;
  rewrite ?joinKI ?meetxx ?leUl ?leUx ?lexx ?orbb //=; congr BSide.
by case: lcomparableP; rewrite ?orbF ?orbb ?andKb.
Qed.

Lemma bound_leEmeet b1 b2 : (b1 <= b2) = (bound_meet b1 b2 == b1).
Proof.
by case: b1 b2 => [[]?|[]][[]?|[]] //=;
  rewrite [LHS]/<=%O /eq_op /= ?eqxx //= -leEmeet; case: lcomparableP.
Qed.

Definition itv_bound_latticeMixin :=
  LatticeMixin bound_meetC bound_joinC bound_meetA bound_joinA
               bound_joinKI bound_meetKU bound_leEmeet.
Canonical itv_bound_latticeType :=
  LatticeType (itv_bound T) itv_bound_latticeMixin.

Lemma bound_le0x b : -oo <= b. Proof. by []. Qed.

Lemma bound_lex1 b : b <= +oo. Proof. by case: b => [|[]]. Qed.

Canonical itv_bound_bLatticeType :=
  BLatticeType (itv_bound T) (BottomMixin bound_le0x).

Canonical itv_bound_tbLatticeType :=
  TBLatticeType (itv_bound T) (TopMixin bound_lex1).

Definition itv_meet i1 i2 : interval T :=
  let: Interval b1l b1r := i1 in
  let: Interval b2l b2r := i2 in Interval (b1l `|` b2l) (b1r `&` b2r).

Definition itv_join i1 i2 : interval T :=
  let: Interval b1l b1r := i1 in
  let: Interval b2l b2r := i2 in Interval (b1l `&` b2l) (b1r `|` b2r).

Lemma itv_meetC : commutative itv_meet.
Proof. by case=> [? ?][? ?] /=; rewrite meetC joinC. Qed.

Lemma itv_joinC : commutative itv_join.
Proof. by case=> [? ?][? ?] /=; rewrite meetC joinC. Qed.

Lemma itv_meetA : associative itv_meet.
Proof. by case=> [? ?][? ?][? ?] /=; rewrite meetA joinA. Qed.

Lemma itv_joinA : associative itv_join.
Proof. by case=> [? ?][? ?][? ?] /=; rewrite meetA joinA. Qed.

Lemma itv_meetKU i2 i1 : itv_join i1 (itv_meet i1 i2) = i1.
Proof. by case: i1 i2 => [? ?][? ?] /=; rewrite meetKU joinKI. Qed.

Lemma itv_joinKI i2 i1 : itv_meet i1 (itv_join i1 i2) = i1.
Proof. by case: i1 i2 => [? ?][? ?] /=; rewrite meetKU joinKI. Qed.

Lemma itv_leEmeet i1 i2 : (i1 <= i2) = (itv_meet i1 i2 == i1).
Proof. by case: i1 i2 => [? ?][? ?]; rewrite /eq_op /= eq_meetl eq_joinl. Qed.

Definition interval_latticeMixin :=
  LatticeMixin itv_meetC itv_joinC itv_meetA itv_joinA
               itv_joinKI itv_meetKU itv_leEmeet.
Canonical interval_latticeType :=
  LatticeType (interval T) interval_latticeMixin.

Lemma itv_le0x i : Interval +oo -oo <= i. Proof. by case: i => [[|[]]]. Qed.

Lemma itv_lex1 i : i <= `]-oo, +oo[. Proof. by case: i => [?[|[]]]. Qed.

Canonical interval_bLatticeType :=
  BLatticeType (interval T) (BottomMixin itv_le0x).

Canonical interval_tbLatticeType :=
  TBLatticeType (interval T) (TopMixin itv_lex1).

Lemma in_itvI x i1 i2 : x \in i1 `&` i2 = (x \in i1) && (x \in i2).
Proof. exact: lexI. Qed.

End IntervalLattice.

Section IntervalTotal.

Variable (disp : unit) (T : orderType disp).
Implicit Types (x y z : T) (i : interval T).

Lemma itv_bound_totalMixin : totalLatticeMixin [latticeType of itv_bound T].
Proof. by move=> [[]?|[]][[]?|[]]; rewrite /<=%O //=; case: ltgtP. Qed.

Canonical itv_bound_distrLatticeType :=
  DistrLatticeType (itv_bound T) itv_bound_totalMixin.
Canonical itv_bound_bDistrLatticeType := [bDistrLatticeType of itv_bound T].
Canonical itv_bound_tbDistrLatticeType := [tbDistrLatticeType of itv_bound T].
Canonical itv_bound_orderType := OrderType (itv_bound T) itv_bound_totalMixin.

Lemma itv_meetUl : @left_distributive (interval T) _ Order.meet Order.join.
Proof.
by move=> [? ?][? ?][? ?]; rewrite /Order.meet /Order.join /= -meetUl -joinIl.
Qed.

Canonical interval_distrLatticeType :=
  DistrLatticeType (interval T) (DistrLatticeMixin itv_meetUl).
Canonical interval_bDistrLatticeType := [bDistrLatticeType of interval T].
Canonical interval_tbDistrLatticeType := [tbDistrLatticeType of interval T].

Lemma itv_splitU c a b : a <= c <= b ->
  forall y, y \in Interval a b = (y \in Interval a c) || (y \in Interval c b).
Proof.
case/andP => leac lecb y.
rewrite !itv_boundlr !(ltNge (BLeft y) _ : (BRight y <= _) = _).
case: (leP a) (leP b) (leP c) => leay [] leby [] lecy //=.
- by case: leP lecy (le_trans lecb leby).
- by case: leP leay (le_trans leac lecy).
Qed.

Lemma itv_splitUeq x a b : x \in Interval a b ->
  forall y, y \in Interval a b =
    [|| y \in Interval a (BLeft x), y == x | y \in Interval (BRight x) b].
Proof.
case/andP => ax xb y; rewrite (@itv_splitU (BLeft x)) ?ax ?ltW //.
by congr orb; rewrite (@itv_splitU (BRight x)) ?bound_lexx // itv_xx.
Qed.

Lemma itv_total_meet3E i1 i2 i3 :
  i1 `&` i2 `&` i3 \in [:: i1 `&` i2; i1 `&` i3; i2 `&` i3].
Proof.
case: i1 i2 i3 => [b1l b1r] [b2l b2r] [b3l b3r]; rewrite !inE /eq_op /=.
case: (leP b1l b2l); case: (leP b1l b3l); case: (leP b2l b3l);
  case: (leP b1r b2r); case: (leP b1r b3r); case: (leP b2r b3r);
  rewrite ?eqxx ?orbT //= => b23r b13r b12r b23l b13l b12l.
- by case: leP b13r (le_trans b12r b23r).
- by case: leP b13l (le_trans b12l b23l).
- by case: leP b13l (le_trans b12l b23l).
- by case: leP b13r (le_trans b12r b23r).
- by case: leP b13r (le_trans b12r b23r).
- by case: leP b13l (lt_trans b23l b12l).
- by case: leP b13r (lt_trans b23r b12r).
- by case: leP b13l (lt_trans b23l b12l).
- by case: leP b13r (lt_trans b23r b12r).
- by case: leP b13r (lt_trans b23r b12r).
Qed.

Lemma itv_total_join3E i1 i2 i3 :
  i1 `|` i2 `|` i3 \in [:: i1 `|` i2; i1 `|` i3; i2 `|` i3].
Proof.
case: i1 i2 i3 => [b1l b1r] [b2l b2r] [b3l b3r]; rewrite !inE /eq_op /=.
case: (leP b1l b2l); case: (leP b1l b3l); case: (leP b2l b3l);
  case: (leP b1r b2r); case: (leP b1r b3r); case: (leP b2r b3r);
  rewrite ?eqxx ?orbT //= => b23r b13r b12r b23l b13l b12l.
- by case: leP b13r (le_trans b12r b23r).
- by case: leP b13r (le_trans b12r b23r).
- by case: leP b13l (le_trans b12l b23l).
- by case: leP b13l (le_trans b12l b23l).
- by case: leP b13l (le_trans b12l b23l).
- by case: leP b13r (lt_trans b23r b12r).
- by case: leP b13l (lt_trans b23l b12l).
- by case: leP b13l (lt_trans b23l b12l).
- by case: leP b13l (lt_trans b23l b12l).
- by case: leP b13r (lt_trans b23r b12r).
Qed.

End IntervalTotal.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Section IntervalNumDomain.

Variable R : numFieldType.
Implicit Types x : R.

Lemma mem0_itvcc_xNx x : (0 \in `[- x, x]) = (0 <= x).
Proof. by rewrite itv_boundlr [in LHS]/<=%O /= oppr_le0 andbb. Qed.

Lemma mem0_itvoo_xNx x : 0 \in `](- x), x[ = (0 < x).
Proof. by rewrite itv_boundlr [in LHS]/<=%O /= oppr_lt0 andbb. Qed.

Lemma oppr_itv ba bb (xa xb x : R) :
  (- x \in Interval (BSide ba xa) (BSide bb xb)) =
  (x \in Interval (BSide (~~ bb) (- xb)) (BSide (~~ ba) (- xa))).
Proof.
by rewrite !itv_boundlr /<=%O /= !implybF negbK andbC lteif_oppl lteif_oppr.
Qed.

Lemma oppr_itvoo (a b x : R) : (- x \in `]a, b[) = (x \in `](- b), (- a)[).
Proof. exact: oppr_itv. Qed.

Lemma oppr_itvco (a b x : R) : (- x \in `[a, b[) = (x \in `](- b), (- a)]).
Proof. exact: oppr_itv. Qed.

Lemma oppr_itvoc (a b x : R) : (- x \in `]a, b]) = (x \in `[(- b), (- a)[).
Proof. exact: oppr_itv. Qed.

Lemma oppr_itvcc (a b x : R) : (- x \in `[a, b]) = (x \in `[(- b), (- a)]).
Proof. exact: oppr_itv. Qed.

End IntervalNumDomain.

Section IntervalField.

Variable R : realFieldType.

Local Notation mid x y := ((x + y) / 2%:R).

Lemma mid_in_itv : forall ba bb (xa xb : R), xa < xb ?<= if ba && ~~ bb ->
  mid xa xb \in Interval (BSide ba xa) (BSide bb xb).
Proof.
by move=> [] [] xa xb /= ?; apply/itv_dec; rewrite /= ?midf_lte // ?ltW.
Qed.

Lemma mid_in_itvoo : forall (xa xb : R), xa < xb -> mid xa xb \in `]xa, xb[.
Proof. by move=> xa xb ?; apply: mid_in_itv. Qed.

Lemma mid_in_itvcc : forall (xa xb : R), xa <= xb -> mid xa xb \in `[xa, xb].
Proof. by move=> xa xb ?; apply: mid_in_itv. Qed.

End IntervalField.

(******************************************************************************)
(* Compatibility layer                                                        *)
(******************************************************************************)

Module mc_1_11.

Local Notation lersif x y b := (Order.lteif x y (~~ b)) (only parsing).

Local Notation "x <= y ?< 'if' b" := (x < y ?<= if ~~ b)
  (at level 70, y at next level, only parsing) : ring_scope.

Section LersifPo.

Variable R : numDomainType.
Implicit Types (b : bool) (x y z : R).

Lemma subr_lersifr0 b (x y : R) : (y - x <= 0 ?< if b) = (y <= x ?< if b).
Proof. exact: subr_lteifr0. Qed.

Lemma subr_lersif0r b (x y : R) : (0 <= y - x ?< if b) = (x <= y ?< if b).
Proof. exact: subr_lteif0r. Qed.

Definition subr_lersif0 := (subr_lersifr0, subr_lersif0r).

Lemma lersif_trans x y z b1 b2 :
  x <= y ?< if b1 -> y <= z ?< if b2 -> x <= z ?< if b1 || b2.
Proof. by rewrite negb_or; exact: lteif_trans. Qed.

Lemma lersif01 b : (0 : R) <= 1 ?< if b. Proof. exact: lteif01. Qed.

Lemma lersif_anti b1 b2 x y :
  (x <= y ?< if b1) && (y <= x ?< if b2) =
  if b1 || b2 then false else x == y.
Proof. by rewrite lteif_anti -negb_or; case: orb. Qed.

Lemma lersifxx x b : (x <= x ?< if b) = ~~ b. Proof. exact: lteifxx. Qed.

Lemma lersifNF x y b : y <= x ?< if ~~ b -> x <= y ?< if b = false.
Proof. exact: lteifNF. Qed.

Lemma lersifS x y b : x < y -> x <= y ?< if b.
Proof. exact: lteifS. Qed.

Lemma lersifT x y : x <= y ?< if true = (x < y). Proof. by []. Qed.

Lemma lersifF x y : x <= y ?< if false = (x <= y). Proof. by []. Qed.

Lemma lersif_oppl b x y : - x <= y ?< if b = (- y <= x ?< if b).
Proof. exact: lteif_oppl. Qed.

Lemma lersif_oppr b x y : x <= - y ?< if b = (y <= - x ?< if b).
Proof. exact: lteif_oppr. Qed.

Lemma lersif_0oppr b x : 0 <= - x ?< if b = (x <= 0 ?< if b).
Proof. exact: lteif_0oppr. Qed.

Lemma lersif_oppr0 b x : - x <= 0 ?< if b = (0 <= x ?< if b).
Proof. exact: lteif_oppr0. Qed.

Lemma lersif_opp2 b : {mono (-%R : R -> R) : x y /~ x <= y ?< if b}.
Proof. exact: lteif_opp2. Qed.

Definition lersif_oppE := (lersif_0oppr, lersif_oppr0, lersif_opp2).

Lemma lersif_add2l b x : {mono +%R x : y z / y <= z ?< if b}.
Proof. exact: lteif_add2l. Qed.

Lemma lersif_add2r b x : {mono +%R^~ x : y z / y <= z ?< if b}.
Proof. exact: lteif_add2r. Qed.

Definition lersif_add2 := (lersif_add2l, lersif_add2r).

Lemma lersif_subl_addr b x y z : (x - y <= z ?< if b) = (x <= z + y ?< if b).
Proof. exact: lteif_subl_addr. Qed.

Lemma lersif_subr_addr b x y z : (x <= y - z ?< if b) = (x + z <= y ?< if b).
Proof. exact: lteif_subr_addr. Qed.

Definition lersif_sub_addr := (lersif_subl_addr, lersif_subr_addr).

Lemma lersif_subl_addl b x y z : (x - y <= z ?< if b) = (x <= y + z ?< if b).
Proof. exact: lteif_subl_addl. Qed.

Lemma lersif_subr_addl b x y z : (x <= y - z ?< if b) = (z + x <= y ?< if b).
Proof. exact: lteif_subr_addl. Qed.

Definition lersif_sub_addl := (lersif_subl_addl, lersif_subr_addl).

Lemma lersif_andb x y :
  {morph (fun b => lersif x y b) : p q / p || q >-> p && q}.
Proof. by move=> ? ?; rewrite negb_or lteif_andb. Qed.

Lemma lersif_orb x y :
  {morph (fun b => lersif x y b) : p q / p && q >-> p || q}.
Proof. by move=> ? ?; rewrite negb_and lteif_orb. Qed.

Lemma lersif_imply b1 b2 (r1 r2 : R) :
  b2 ==> b1 -> r1 <= r2 ?< if b1 -> r1 <= r2 ?< if b2.
Proof. by move=> ?; apply: lteif_imply; rewrite implybNN. Qed.

Lemma lersifW b x y : x <= y ?< if b -> x <= y.
Proof. exact: lteifW. Qed.

Lemma ltrW_lersif b x y : x < y -> x <= y ?< if b.
Proof. exact: ltrW_lteif. Qed.

Lemma lersif_pmul2l b x : 0 < x -> {mono *%R x : y z / y <= z ?< if b}.
Proof. exact: lteif_pmul2l. Qed.

Lemma lersif_pmul2r b x : 0 < x -> {mono *%R^~ x : y z / y <= z ?< if b}.
Proof. exact: lteif_pmul2r. Qed.

Lemma lersif_nmul2l b x : x < 0 -> {mono *%R x : y z /~ y <= z ?< if b}.
Proof. exact: lteif_nmul2l. Qed.

Lemma lersif_nmul2r b x : x < 0 -> {mono *%R^~ x : y z /~ y <= z ?< if b}.
Proof. exact: lteif_nmul2r. Qed.

Lemma real_lersifN x y b : x \is Num.real -> y \is Num.real ->
  x <= y ?< if ~~b = ~~ (y <= x ?< if b).
Proof. exact: real_lteifNE. Qed.

Lemma real_lersif_norml b x y :
  x \is Num.real ->
  (`|x| <= y ?< if b) = ((- y <= x ?< if b) && (x <= y ?< if b)).
Proof. exact: real_lteif_norml. Qed.

Lemma real_lersif_normr b x y :
  y \is Num.real ->
  (x <= `|y| ?< if b) = ((x <= y ?< if b) || (x <= - y ?< if b)).
Proof. exact: real_lteif_normr. Qed.

Lemma lersif_nnormr b x y : y <= 0 ?< if ~~ b -> (`|x| <= y ?< if b) = false.
Proof. exact: lteif_nnormr. Qed.

End LersifPo.

Section LersifOrdered.

Variable (R : realDomainType) (b : bool) (x y z e : R).

Lemma lersifN : (x <= y ?< if ~~ b) = ~~ (y <= x ?< if b).
Proof. exact: lteifNE. Qed.

Lemma lersif_norml :
  (`|x| <= y ?< if b) = (- y <= x ?< if b) && (x <= y ?< if b).
Proof. exact: lteif_norml. Qed.

Lemma lersif_normr :
  (x <= `|y| ?< if b) = (x <= y ?< if b) || (x <= - y ?< if b).
Proof. exact: lteif_normr. Qed.

Lemma lersif_distl :
  (`|x - y| <= e ?< if b) = (y - e <= x ?< if b) && (x <= y + e ?< if b).
Proof. exact: lteif_distl. Qed.

Lemma lersif_minr :
  (x <= Num.min y z ?< if b) = (x <= y ?< if b) && (x <= z ?< if b).
Proof. exact: lteif_minr. Qed.

Lemma lersif_minl :
  (Num.min y z <= x ?< if b) = (y <= x ?< if b) || (z <= x ?< if b).
Proof. exact: lteif_minl. Qed.

Lemma lersif_maxr :
  (x <= Num.max y z ?< if b) = (x <= y ?< if b) || (x <= z ?< if b).
Proof. exact: lteif_maxr. Qed.

Lemma lersif_maxl :
  (Num.max y z <= x ?< if b) = (y <= x ?< if b) && (z <= x ?< if b).
Proof. exact: lteif_maxl. Qed.

End LersifOrdered.

Section LersifField.

Variable (F : numFieldType) (b : bool) (z x y : F).

Lemma lersif_pdivl_mulr : 0 < z -> x <= y / z ?< if b = (x * z <= y ?< if b).
Proof. exact: lteif_pdivl_mulr. Qed.

Lemma lersif_pdivr_mulr : 0 < z -> y / z <= x ?< if b = (y <= x * z ?< if b).
Proof. exact: lteif_pdivr_mulr. Qed.

Lemma lersif_pdivl_mull : 0 < z -> x <= z^-1 * y ?< if b = (z * x <= y ?< if b).
Proof. exact: lteif_pdivl_mull. Qed.

Lemma lersif_pdivr_mull : 0 < z -> z^-1 * y <= x ?< if b = (y <= z * x ?< if b).
Proof. exact: lteif_pdivr_mull. Qed.

Lemma lersif_ndivl_mulr : z < 0 -> x <= y / z ?< if b = (y <= x * z ?< if b).
Proof. exact: lteif_ndivl_mulr. Qed.

Lemma lersif_ndivr_mulr : z < 0 -> y / z <= x ?< if b = (x * z <= y ?< if b).
Proof. exact: lteif_ndivr_mulr. Qed.

Lemma lersif_ndivl_mull : z < 0 -> x <= z^-1 * y ?< if b = (y <=z * x ?< if b).
Proof. exact: lteif_ndivl_mull. Qed.

Lemma lersif_ndivr_mull : z < 0 -> z^-1 * y <= x ?< if b = (z * x <= y ?< if b).
Proof. exact: lteif_ndivr_mull. Qed.

End LersifField.

Section IntervalPo.

Variable R : numDomainType.

Implicit Types (x xa xb : R).

Lemma lersif_in_itv ba bb xa xb x :
  x \in Interval (BSide ba xa) (BSide bb xb) -> xa <= xb ?< if ~~ ba || bb.
Proof. by move/lt_in_itv; rewrite negb_or negbK. Qed.

Lemma itv_gte ba xa bb xb :
  xb <= xa ?< if ba && ~~ bb -> Interval (BSide ba xa) (BSide bb xb) =i pred0.
Proof. by move=> ?; apply: itv_ge; rewrite /<%O /= lteifNF. Qed.

Lemma ltr_in_itv ba bb xa xb x :
  ~~ ba || bb -> x \in Interval (BSide ba xa) (BSide bb xb) -> xa < xb.
Proof. by move=> bab /lersif_in_itv; rewrite bab. Qed.

Lemma ler_in_itv ba bb xa xb x :
  x \in Interval (BSide ba xa) (BSide bb xb) -> xa <= xb.
Proof. by move/lt_in_itv/lteifW. Qed.

End IntervalPo.

Lemma itv_splitU2 (R : realDomainType) (x : R) a b :
  x \in Interval a b ->
  forall y, y \in Interval a b =
    [|| y \in Interval a (BLeft x), y == x | y \in Interval (BRight x) b].
Proof. exact: itv_splitUeq. Qed.

End mc_1_11.

(* Use `Order.lteif` instead of `lteif`. (`deprecate` does not accept a       *)
(* qualified name.)                                                           *)
Local Notation lteif := Order.lteif (only parsing).

Notation "@ 'lersif'" :=
  ((fun _ (R : numDomainType) x y b => @Order.lteif _ R x y (~~ b))
     (deprecate lersif lteif))
    (at level 10, only parsing).

Notation lersif := (@lersif _) (only parsing).

Notation "x <= y ?< 'if' b" :=
  ((fun _ => x < y ?<= if ~~ b) (deprecate lersif lteif))
    (at level 70, y at next level, only parsing) : ring_scope.

(* LersifPo *)

Notation "@ 'subr_lersifr0'" :=
  ((fun _ => @mc_1_11.subr_lersifr0) (deprecate subr_lersifr0 subr_lteifr0))
    (at level 10, only parsing).

Notation subr_lersifr0 := (@subr_lersifr0 _) (only parsing).

Notation "@ 'subr_lersif0r'" :=
  ((fun _ => @mc_1_11.subr_lersif0r) (deprecate subr_lersif0r subr_lteif0r))
    (at level 10, only parsing).

Notation subr_lersif0r := (@subr_lersif0r _) (only parsing).

Notation subr_lersif0 :=
  ((fun _ => @mc_1_11.subr_lersif0) (deprecate subr_lersif0 subr_lteif0))
    (only parsing).

Notation "@ 'lersif_trans'" :=
  ((fun _ => @mc_1_11.lersif_trans) (deprecate lersif_trans lteif_trans))
    (at level 10, only parsing).

Notation lersif_trans := (@lersif_trans _ _ _ _ _ _) (only parsing).

Notation lersif01 :=
  ((fun _ => @mc_1_11.lersif01) (deprecate lersif01 lteif01)) (only parsing).

Notation "@ 'lersif_anti'" :=
  ((fun _ => @mc_1_11.lersif_anti) (deprecate lersif_anti lteif_anti))
    (at level 10, only parsing).

Notation lersif_anti := (@lersif_anti _) (only parsing).

Notation "@ 'lersifxx'" :=
  ((fun _ => @mc_1_11.lersifxx) (deprecate lersifxx lteifxx))
    (at level 10, only parsing).

Notation lersifxx := (@lersifxx _) (only parsing).

Notation "@ 'lersifNF'" :=
  ((fun _ => @mc_1_11.lersifNF) (deprecate lersifNF lteifNF))
    (at level 10, only parsing).

Notation lersifNF := (@lersifNF _ _ _ _) (only parsing).

Notation "@ 'lersifS'" :=
  ((fun _ => @mc_1_11.lersifS) (deprecate lersifS lteifS))
    (at level 10, only parsing).

Notation lersifS := (@lersifS _ _ _) (only parsing).

Notation "@ 'lersifT'" :=
  ((fun _ => @mc_1_11.lersifT) (deprecate lersifT lteifT))
    (at level 10, only parsing).

Notation lersifT := (@lersifT _) (only parsing).

Notation "@ 'lersifF'" :=
  ((fun _ => @mc_1_11.lersifF) (deprecate lersifF lteifF))
    (at level 10, only parsing).

Notation lersifF := (@lersifF _) (only parsing).

Notation "@ 'lersif_oppl'" :=
  ((fun _ => @mc_1_11.lersif_oppl) (deprecate lersif_oppl lteif_oppl))
    (at level 10, only parsing).

Notation lersif_oppl := (@lersif_oppl _) (only parsing).

Notation "@ 'lersif_oppr'" :=
  ((fun _ => @mc_1_11.lersif_oppr) (deprecate lersif_oppr lteif_oppr))
    (at level 10, only parsing).

Notation lersif_oppr := (@lersif_oppr _) (only parsing).

Notation "@ 'lersif_0oppr'" :=
  ((fun _ => @mc_1_11.lersif_0oppr) (deprecate lersif_0oppr lteif_0oppr))
    (at level 10, only parsing).

Notation lersif_0oppr := (@lersif_0oppr _) (only parsing).

Notation "@ 'lersif_oppr0'" :=
  ((fun _ => @mc_1_11.lersif_oppr0) (deprecate lersif_oppr0 lteif_oppr0))
    (at level 10, only parsing).

Notation lersif_oppr0 := (@lersif_oppr0 _) (only parsing).

Notation "@ 'lersif_opp2'" :=
  ((fun _ => @mc_1_11.lersif_opp2) (deprecate lersif_opp2 lteif_opp2))
    (at level 10, only parsing).

Notation lersif_opp2 := (@lersif_opp2 _) (only parsing).

Notation lersif_oppE :=
  ((fun _ => @mc_1_11.lersif_oppE) (deprecate lersif_oppE lteif_oppE))
    (only parsing).

Notation "@ 'lersif_add2l'" :=
  ((fun _ => @mc_1_11.lersif_add2l) (deprecate lersif_add2l lteif_add2l))
    (at level 10, only parsing).

Notation lersif_add2l := (@lersif_add2l _) (only parsing).

Notation "@ 'lersif_add2r'" :=
  ((fun _ => @mc_1_11.lersif_add2r) (deprecate lersif_add2r lteif_add2r))
    (at level 10, only parsing).

Notation lersif_add2r := (@lersif_add2r _) (only parsing).

Notation lersif_add2 :=
  ((fun _ => @mc_1_11.lersif_add2) (deprecate lersif_add2 lteif_add2))
    (only parsing).

Notation "@ 'lersif_subl_addr'" :=
  ((fun _ => @mc_1_11.lersif_subl_addr)
     (deprecate lersif_subl_addr lteif_subl_addr))
    (at level 10, only parsing).

Notation lersif_subl_addr := (@lersif_subl_addr _) (only parsing).

Notation "@ 'lersif_subr_addr'" :=
  ((fun _ => @mc_1_11.lersif_subr_addr)
     (deprecate lersif_subr_addr lteif_subr_addr))
    (at level 10, only parsing).

Notation lersif_subr_addr := (@lersif_subr_addr _) (only parsing).

Notation lersif_sub_addr :=
  ((fun _ => @mc_1_11.lersif_sub_addr)
     (deprecate lersif_sub_addr lteif_sub_addr))
    (only parsing).

Notation "@ 'lersif_subl_addl'" :=
  ((fun _ => @mc_1_11.lersif_subl_addl)
     (deprecate lersif_subl_addl lteif_subl_addl))
    (at level 10, only parsing).

Notation lersif_subl_addl := (@lersif_subl_addl _) (only parsing).

Notation "@ 'lersif_subr_addl'" :=
  ((fun _ => @mc_1_11.lersif_subr_addl)
     (deprecate lersif_subr_addl lteif_subr_addl))
    (at level 10, only parsing).

Notation lersif_subr_addl := (@lersif_subr_addl _) (only parsing).

Notation lersif_sub_addl :=
  ((fun _ => @mc_1_11.lersif_sub_addl)
     (deprecate lersif_sub_addl lteif_sub_addl))
    (only parsing).

Notation "@ 'lersif_andb'" :=
  ((fun _ => @mc_1_11.lersif_andb) (deprecate lersif_andb lteif_andb))
    (at level 10, only parsing).

Notation lersif_andb := (@lersif_andb _) (only parsing).

Notation "@ 'lersif_orb'" :=
  ((fun _ => @mc_1_11.lersif_orb) (deprecate lersif_orb lteif_orb))
    (at level 10, only parsing).

Notation lersif_orb := (@lersif_orb _) (only parsing).

Notation "@ 'lersif_imply'" :=
  ((fun _ => @mc_1_11.lersif_imply) (deprecate lersif_imply lteif_imply))
    (at level 10, only parsing).

Notation lersif_imply := (@lersif_imply _ _ _ _ _) (only parsing).

Notation "@ 'lersifW'" :=
  ((fun _ => @mc_1_11.lersifW) (deprecate lersifW lteifW))
    (at level 10, only parsing).

Notation lersifW := (@lersifW _ _ _ _) (only parsing).

Notation "@ 'ltrW_lersif'" :=
  ((fun _ => @mc_1_11.ltrW_lersif) (deprecate ltrW_lersif ltrW_lteif))
    (at level 10, only parsing).

Notation ltrW_lersif := (@ltrW_lersif _) (only parsing).

Notation "@ 'lersif_pmul2l'" :=
  ((fun _ => @mc_1_11.lersif_pmul2l) (deprecate lersif_pmul2l lteif_pmul2l))
    (at level 10, only parsing).

Notation lersif_pmul2l := (fun b => @lersif_pmul2l _ b _) (only parsing).

Notation "@ 'lersif_pmul2r'" :=
  ((fun _ => @mc_1_11.lersif_pmul2r) (deprecate lersif_pmul2r lteif_pmul2r))
    (at level 10, only parsing).

Notation lersif_pmul2r := (fun b => @lersif_pmul2r _ b _) (only parsing).

Notation "@ 'lersif_nmul2l'" :=
  ((fun _ => @mc_1_11.lersif_nmul2l) (deprecate lersif_nmul2l lteif_nmul2l))
    (at level 10, only parsing).

Notation lersif_nmul2l := (fun b => @lersif_nmul2l _ b _) (only parsing).

Notation "@ 'lersif_nmul2r'" :=
  ((fun _ => @mc_1_11.lersif_nmul2r) (deprecate lersif_nmul2r lteif_nmul2r))
    (at level 10, only parsing).

Notation lersif_nmul2r := (fun b => @lersif_nmul2r _ b _) (only parsing).

Notation "@ 'real_lersifN'" :=
  ((fun _ => @mc_1_11.real_lersifN) (deprecate real_lersifN real_lteifNE))
    (at level 10, only parsing).

Notation real_lersifN := (@real_lersifN _ _ _) (only parsing).

Notation "@ 'real_lersif_norml'" :=
  ((fun _ => @mc_1_11.real_lersif_norml)
     (deprecate real_lersif_norml real_lteif_norml))
    (at level 10, only parsing).

Notation real_lersif_norml :=
  (fun b => @real_lersif_norml _ b _) (only parsing).

Notation "@ 'real_lersif_normr'" :=
  ((fun _ => @mc_1_11.real_lersif_normr)
     (deprecate real_lersif_normr real_lteif_normr))
    (at level 10, only parsing).

Notation real_lersif_normr :=
  (fun b x => @real_lersif_normr _ b x _) (only parsing).

Notation "@ 'lersif_nnormr'" :=
  ((fun _ => @mc_1_11.lersif_nnormr) (deprecate lersif_nnormr lteif_nnormr))
    (at level 10, only parsing).

Notation lersif_nnormr := (fun x => @lersif_nnormr _ _ x _) (only parsing).

(* LersifOrdered *)

Notation "@ 'lersifN'" :=
  ((fun _ => @mc_1_11.lersifN) (deprecate lersifN lteifNE))
    (at level 10, only parsing).

Notation lersifN := (@lersifN _) (only parsing).

Notation "@ 'lersif_norml'" :=
  ((fun _ => @mc_1_11.lersif_norml) (deprecate lersif_norml lteif_norml))
    (at level 10, only parsing).

Notation lersif_norml := (@lersif_norml _) (only parsing).

Notation "@ 'lersif_normr'" :=
  ((fun _ => @mc_1_11.lersif_normr) (deprecate lersif_normr lteif_normr))
    (at level 10, only parsing).

Notation lersif_normr := (@lersif_normr _) (only parsing).

Notation "@ 'lersif_distl'" :=
  ((fun _ => @mc_1_11.lersif_distl) (deprecate lersif_distl lteif_distl))
    (at level 10, only parsing).

Notation lersif_distl := (@lersif_distl _) (only parsing).

Notation "@ 'lersif_minr'" :=
  ((fun _ => @mc_1_11.lersif_minr) (deprecate lersif_minr lteif_minr))
    (at level 10, only parsing).

Notation lersif_minr := (@lersif_minr _) (only parsing).

Notation "@ 'lersif_minl'" :=
  ((fun _ => @mc_1_11.lersif_minl) (deprecate lersif_minl lteif_minl))
    (at level 10, only parsing).

Notation lersif_minl := (@lersif_minl _) (only parsing).

Notation "@ 'lersif_maxr'" :=
  ((fun _ => @mc_1_11.lersif_maxr) (deprecate lersif_maxr lteif_maxr))
    (at level 10, only parsing).

Notation lersif_maxr := (@lersif_maxr _) (only parsing).

Notation "@ 'lersif_maxl'" :=
  ((fun _ => @mc_1_11.lersif_maxl) (deprecate lersif_maxl lteif_maxl))
    (at level 10, only parsing).

Notation lersif_maxl := (@lersif_maxl _) (only parsing).

(* LersifField *)

Notation "@ 'lersif_pdivl_mulr'" :=
  ((fun _ => @mc_1_11.lersif_pdivl_mulr)
     (deprecate lersif_pdivl_mulr lteif_pdivl_mulr))
    (at level 10, only parsing).

Notation lersif_pdivl_mulr :=
  (fun b => @lersif_pdivl_mulr _ b _) (only parsing).

Notation "@ 'lersif_pdivr_mulr'" :=
  ((fun _ => @mc_1_11.lersif_pdivr_mulr)
     (deprecate lersif_pdivr_mulr lteif_pdivr_mulr))
    (at level 10, only parsing).

Notation lersif_pdivr_mulr :=
  (fun b => @lersif_pdivr_mulr _ b _) (only parsing).

Notation "@ 'lersif_pdivl_mull'" :=
  ((fun _ => @mc_1_11.lersif_pdivl_mull)
     (deprecate lersif_pdivl_mull lteif_pdivl_mull))
    (at level 10, only parsing).

Notation lersif_pdivl_mull :=
  (fun b => @lersif_pdivl_mull _ b _) (only parsing).

Notation "@ 'lersif_pdivr_mull'" :=
  ((fun _ => @mc_1_11.lersif_pdivr_mull)
     (deprecate lersif_pdivr_mull lteif_pdivr_mull))
    (at level 10, only parsing).

Notation lersif_pdivr_mull :=
  (fun b => @lersif_pdivr_mull _ b _) (only parsing).

Notation "@ 'lersif_ndivl_mulr'" :=
  ((fun _ => @mc_1_11.lersif_ndivl_mulr)
     (deprecate lersif_ndivl_mulr lteif_ndivl_mulr))
    (at level 10, only parsing).

Notation lersif_ndivl_mulr :=
  (fun b => @lersif_ndivl_mulr _ b _) (only parsing).

Notation "@ 'lersif_ndivr_mulr'" :=
  ((fun _ => @mc_1_11.lersif_ndivr_mulr)
     (deprecate lersif_ndivr_mulr lteif_ndivr_mulr))
    (at level 10, only parsing).

Notation lersif_ndivr_mulr :=
  (fun b => @lersif_ndivr_mulr _ b _) (only parsing).

Notation "@ 'lersif_ndivl_mull'" :=
  ((fun _ => @mc_1_11.lersif_ndivl_mull)
     (deprecate lersif_ndivl_mull lteif_ndivl_mull))
    (at level 10, only parsing).

Notation lersif_ndivl_mull :=
  (fun b => @lersif_ndivl_mull _ b _) (only parsing).

Notation "@ 'lersif_ndivr_mull'" :=
  ((fun _ => @mc_1_11.lersif_ndivr_mull)
     (deprecate lersif_ndivr_mull lteif_ndivr_mull))
    (at level 10, only parsing).

Notation lersif_ndivr_mull :=
  (fun b => @lersif_ndivr_mull _ b _) (only parsing).

(* IntervalPo *)

Notation "@ 'lersif_in_itv'" :=
  ((fun _ => @mc_1_11.lersif_in_itv) (deprecate lersif_in_itv lteif_in_itv))
    (at level 10, only parsing).

Notation lersif_in_itv := (@lersif_in_itv _ _ _ _ _ _) (only parsing).

Notation "@ 'itv_gte'" :=
  ((fun _ => @mc_1_11.itv_gte) (deprecate itv_gte itv_ge))
    (at level 10, only parsing).

Notation itv_gte := (@itv_gte _ _ _ _ _) (only parsing).

Notation "@ 'ltr_in_itv'" :=
  ((fun _ => @mc_1_11.ltr_in_itv) (deprecate ltr_in_itv lt_in_itv))
    (at level 10, only parsing).

Notation ltr_in_itv := (@ltr_in_itv _ _ _ _ _ _) (only parsing).

Notation "@ 'ler_in_itv'" :=
  ((fun _ => @mc_1_11.ler_in_itv) (deprecate ler_in_itv lt_in_itv))
    (at level 10, only parsing).

Notation ler_in_itv := (@ler_in_itv _ _ _ _ _ _) (only parsing).

Notation "@ 'itv_splitU2'" :=
  ((fun _ => @mc_1_11.itv_splitU2) (deprecate itv_splitU2 itv_splitUeq))
    (at level 10, only parsing).

Notation itv_splitU2 := (@itv_splitU2 _ _ _ _) (only parsing).

(* `itv_intersection` accepts any `numDomainType` but `Order.meet` accepts    *)
(* only `realDomainType`. Use `Order.meet` instead of `itv_meet`.             *)
Notation "@ 'itv_intersection'" :=
  ((fun _ (R : realDomainType) => @Order.meet _ [latticeType of interval R])
     (deprecate itv_intersection itv_meet))
    (at level 10, only parsing) : fun_scope.

Notation itv_intersection := (@itv_intersection _) (only parsing).

Notation "@ 'itv_intersection1i'" :=
  ((fun _ (R : realDomainType) => @meet1x _ [tbLatticeType of interval R])
     (deprecate itv_intersection1i meet1x))
    (at level 10, only parsing) : fun_scope.

Notation itv_intersection1i := (@itv_intersection1i _) (only parsing).

Notation "@ 'itv_intersectioni1'" :=
  ((fun _ (R : realDomainType) => @meetx1 _ [tbLatticeType of interval R])
     (deprecate itv_intersectioni1 meetx1))
    (at level 10, only parsing) : fun_scope.

Notation itv_intersectioni1 := (@itv_intersectioni1 _) (only parsing).

Notation "@ 'itv_intersectionii'" :=
  ((fun _ (R : realDomainType) => @meetxx _ [latticeType of interval R])
     (deprecate itv_intersectionii meetxx))
    (at level 10, only parsing) : fun_scope.

Notation itv_intersectionii := (@itv_intersectionii _) (only parsing).

(* IntervalOrdered *)

Notation "@ 'itv_intersectionC'" :=
  ((fun _ (R : realDomainType) => @meetC _ [latticeType of interval R])
     (deprecate itv_intersectionC meetC))
    (at level 10, only parsing) : fun_scope.

Notation itv_intersectionC := (@itv_intersectionC _) (only parsing).

Notation "@ 'itv_intersectionA'" :=
  ((fun _ (R : realDomainType) => @meetA _ [latticeType of interval R])
     (deprecate itv_intersectionA meetA))
    (at level 10, only parsing) : fun_scope.

Notation itv_intersectionA := (@itv_intersectionA _) (only parsing).
