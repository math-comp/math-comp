(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import div fintype bigop order ssralg finset fingroup.
From mathcomp Require Import orderedzmod numdomain numfield.

(******************************************************************************)
(*                         Intervals in ordered types                         *)
(*                                                                            *)
(* This file provides support for intervals in ordered types. The datatype    *)
(* (interval T) gives a formal characterization of an interval, as the pair   *)
(* of its right and left bounds.                                              *)
(*    interval T    == the type of formal intervals on T.                     *)
(*    x \in i       == when i is a formal interval on an ordered type,        *)
(*                     \in can be used to test membership.                    *)
(*    itvP x_in_i   == where x_in_i has type x \in i, if i is ground,         *)
(*                     gives a set of rewrite rules that x_in_i implies       *)
(* lteBSide, bnd_simp == multirules to simplify inequalities between interval *)
(*                     bounds                                                 *)
(*    miditv i      == middle point of interval i                             *)
(*                                                                            *)
(* When using interval.v, the lemma `in_itv` is in practice very useful. For  *)
(* example, the execution of the tactic `rewrite in_itv` w.r.t. an hypothesis *)
(* of the form x \in `]a, b[ into a < x < b.                                  *)
(*                                                                            *)
(* Intervals of T form an partially ordered type (porderType) whose ordering  *)
(* is the subset relation. If T is a lattice, intervals also form a lattice   *)
(* (latticeType) whose meet and join are intersection and convex hull         *)
(* respectively. They are distributive if T is an orderType.                  *)
(*                                                                            *)
(* We provide a set of notations to write intervals (see below)               *)
(* `[a, b], `]a, b], ..., `]-oo, a], ..., `]-oo, +oo[                         *)
(* The substrings "oo", "oc", "co", "cc" in the names of lemmas respectively  *)
(* stand for the intervals of the shape `]a, b[, `]a, b], `[a, b[, `[a, b].   *)
(* The substrings "pinfty" and "ninfty" in the names of lemmas stand for      *)
(* +oo and -oo.                                                               *)
(* We also provide the lemma subitvP which computes the inequalities one      *)
(* needs to prove when trying to prove the inclusion of intervals.            *)
(*                                                                            *)
(* Remark that we cannot implement a boolean comparison test for intervals on *)
(* an arbitrary ordered types, for this problem might be undecidable. Note    *)
(* also that type (interval R) may contain several inhabitants coding for the *)
(* same interval. However, these pathological issues do not arise when R is a *)
(* real domain: we could provide a specific theory for this important case.   *)
(*                                                                            *)
(* References:                                                                *)
(* - Cyril Cohen, Assia Mahboubi, Formal proofs in real algebraic geometry:   *)
(* from ordered fields quantifier elimination, LMCS, 2012                     *)
(* - Cyril Cohen, Formalized algebraic numbers: construction and first-order  *)
(* theory, PhD thesis, 2012, section 4.3                                      *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope order_scope.
Import Order.TTheory.
Import orderedzmod.Num.Theory numdomain.Num.Theory numfield.Num.Theory.

Variant itv_bound (T : Type) : Type := BSide of bool & T | BInfty of bool.
Notation BLeft := (BSide true).
Notation BRight := (BSide false).
Notation "'-oo'" := (BInfty _ true) (at level 0) : order_scope.
Notation "'+oo'" := (BInfty _ false) (at level 0) : order_scope.
Variant interval (T : Type) := Interval of itv_bound T & itv_bound T.

Coercion pair_of_interval T (I : interval T) : itv_bound T * itv_bound T :=
  let: Interval b1 b2 := I in (b1, b2).

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

Fact itv_bound_display (disp : Order.disp_t) : Order.disp_t. Proof. exact. Qed.
Fact interval_display (disp : Order.disp_t) : Order.disp_t. Proof. exact. Qed.

Module IntervalCan.
Section IntervalCan.

Variable T : Type.

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

End IntervalCan.

#[export, hnf]
HB.instance Definition _ (T : eqType)  := Equality.copy (itv_bound T)
  (can_type (@itv_bound_can T)).
#[export, hnf]
HB.instance Definition _ (T : eqType)  := Equality.copy (interval T)
  (can_type (@interval_can T)).
#[export, hnf]
HB.instance Definition _ (T : choiceType)  := Choice.copy (itv_bound T)
  (can_type (@itv_bound_can T)).
#[export, hnf]
HB.instance Definition _ (T : choiceType)  := Choice.copy (interval T)
  (can_type (@interval_can T)).
#[export, hnf]
HB.instance Definition _ (T : countType)  := Countable.copy (itv_bound T)
  (can_type (@itv_bound_can T)).
#[export, hnf]
HB.instance Definition _ (T : countType)  := Countable.copy (interval T)
  (can_type (@interval_can T)).
#[export, hnf]
HB.instance Definition _ (T : finType)  := Finite.copy (itv_bound T)
  (can_type (@itv_bound_can T)).
#[export, hnf]
HB.instance Definition _ (T : finType)  := Finite.copy (interval T)
  (can_type (@interval_can T)).

Module Exports. HB.reexport. End Exports.

End IntervalCan.

Export IntervalCan.Exports.

Section IntervalPOrder.

Variable (disp : Order.disp_t) (T : porderType disp).
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

HB.instance Definition _ :=
  Order.isPOrder.Build (itv_bound_display disp) (itv_bound T)
    lt_bound_def le_bound_refl le_bound_anti le_bound_trans.

Lemma bound_lexx c1 c2 x : (BSide c1 x <= BSide c2 x) = (c2 ==> c1).
Proof. by rewrite /<=%O /= lteifxx. Qed.

Lemma bound_ltxx c1 c2 x : (BSide c1 x < BSide c2 x) = (c1 && ~~ c2).
Proof. by rewrite /<%O /= lteifxx. Qed.

Lemma ge_pinfty b : (+oo <= b) = (b == +oo). Proof. by case: b => [|] []. Qed.

Lemma le_ninfty b : (b <= -oo) = (b == -oo). Proof. by case: b => // - []. Qed.

Lemma gt_pinfty b : (+oo < b) = false. Proof. by []. Qed.

Lemma lt_ninfty b : (b < -oo) = false. Proof. by case: b => // -[]. Qed.

Lemma ltBSide x y (b b' : bool) :
  BSide b x < BSide b' y = (x < y ?<= if b && ~~ b').
Proof. by []. Qed.

Lemma leBSide x y (b b' : bool) :
  BSide b x <= BSide b' y = (x < y ?<= if b' ==> b).
Proof. by []. Qed.

Definition lteBSide := (ltBSide, leBSide).

Lemma ltBRight_leBLeft b x : b < BRight x = (b <= BLeft x).
Proof. by move: b => [[] b|[]]. Qed.
Lemma leBRight_ltBLeft b x : BRight x <= b = (BLeft x < b).
Proof. by move: b => [[] b|[]]. Qed.

Let BLeft_ltE x y (b : bool) : BSide b x < BLeft y = (x < y).
Proof. by case: b. Qed.
Let BRight_leE x y (b : bool) : BSide b x <= BRight y = (x <= y).
Proof. by case: b. Qed.
Let BRight_BLeft_leE x y : BRight x <= BLeft y = (x < y).
Proof. by []. Qed.
Let BLeft_BRight_ltE x y : BLeft x < BRight y = (x <= y).
Proof. by []. Qed.
Let BRight_BSide_ltE x y (b : bool) : BRight x < BSide b y = (x < y).
Proof. by case: b. Qed.
Let BLeft_BSide_leE x y (b : bool) : BLeft x <= BSide b y = (x <= y).
Proof. by case: b. Qed.
Let BSide_ltE x y (b : bool) : BSide b x < BSide b y = (x < y).
Proof. by case: b. Qed.
Let BSide_leE x y (b : bool) : BSide b x <= BSide b y = (x <= y).
Proof. by case: b. Qed.
Let BInfty_leE a : a <= BInfty T false. Proof. by case: a => [[] a|[]]. Qed.
Let BInfty_geE a : BInfty T true <= a. Proof. by case: a => [[] a|[]]. Qed.
Let BInfty_le_eqE a : BInfty T false <= a = (a == BInfty T false).
Proof. by case: a => [[] a|[]]. Qed.
Let BInfty_ge_eqE a : a <= BInfty T true = (a == BInfty T true).
Proof. by case: a => [[] a|[]]. Qed.
Let BInfty_ltE a : a < BInfty T false = (a != BInfty T false).
Proof. by case: a => [[] a|[]]. Qed.
Let BInfty_gtE a : BInfty T true < a = (a != BInfty T true).
Proof. by case: a => [[] a|[]]. Qed.
Let BInfty_ltF a : BInfty T false < a = false.
Proof. by case: a => [[] a|[]]. Qed.
Let BInfty_gtF a : a < BInfty T true = false.
Proof. by case: a => [[] a|[]]. Qed.
Let BInfty_BInfty_ltE : BInfty T true < BInfty T false. Proof. by []. Qed.

Definition bnd_simp := (BLeft_ltE, BRight_leE,
  BRight_BLeft_leE, BLeft_BRight_ltE,
  BRight_BSide_ltE, BLeft_BSide_leE, BSide_ltE, BSide_leE,
  BInfty_leE, BInfty_geE, BInfty_BInfty_ltE,
  BInfty_le_eqE, BInfty_ge_eqE, BInfty_ltE, BInfty_gtE, BInfty_ltF, BInfty_gtF,
  @lexx _ T, @ltxx _ T, @eqxx T).

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

HB.instance Definition _ :=
  Order.isPOrder.Build  (interval_display disp) (interval T)
  (fun _ _ => erefl) subitv_refl subitv_anti subitv_trans.

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

Lemma subset_itv (r s u v : bool) x y : r <= u -> v <= s ->
  {subset Interval (BSide r x) (BSide s y) <= Interval (BSide u x) (BSide v y)}.
Proof.
by move: r s u v=> [] [] [] []// *; apply: subitvP; rewrite subitvE !bound_lexx.
Qed.

Lemma subset_itv_oo_cc x y : {subset `]x, y[ <= `[x, y]}.
Proof. exact: subset_itv. Qed.

Lemma subset_itv_oo_oc x y : {subset `]x, y[ <= `]x, y]}.
Proof. exact: subset_itv. Qed.

Lemma subset_itv_oo_co x y : {subset `]x, y[ <= `[x, y[}.
Proof. exact: subset_itv. Qed.

Lemma subset_itv_oc_cc x y : {subset `]x, y] <= `[x, y]}.
Proof. exact: subset_itv. Qed.

Lemma subset_itv_co_cc x y : {subset `[x, y[ <= `[x, y]}.
Proof. exact: subset_itv. Qed.

Lemma itvxx x : `[x, x] =i pred1 x.
Proof. by move=> y; rewrite in_itv/= -eq_le eq_sym. Qed.

Lemma itvxxP y x : reflect (y = x) (y \in `[x, x]).
Proof. by rewrite itvxx; apply/eqP. Qed.

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

Lemma itv_splitU1 b x : b <= BLeft x ->
  Interval b (BRight x) =i [predU1 x & Interval b (BLeft x)].
Proof.
move=> bx z; rewrite !inE/= !subitvE ?bnd_simp//= lt_neqAle.
by case: (eqVneq z x) => [->|]//=; rewrite lexx bx.
Qed.

Lemma itv_split1U b x : BRight x <= b ->
  Interval (BLeft x) b =i [predU1 x & Interval (BRight x) b].
Proof.
move=> bx z; rewrite !inE/= !subitvE ?bnd_simp//= lt_neqAle.
by case: (eqVneq z x) => [->|]//=; rewrite lexx bx.
Qed.

End IntervalPOrder.

Section IntervalLattice.

Variable (disp : Order.disp_t) (T : latticeType disp).
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
case: b1 b2 => [[]t[][]|[][][]] //=; rewrite ?eqxx// => t';
  rewrite [LHS]/<=%O /eq_op ?andbT ?andbF ?orbF/= /eq_op/= /eq_op/=;
  case: lcomparableP => //=; rewrite ?eqxx//=; [| | |].
- by move/lt_eqF.
- move=> ic; apply: esym; apply: contraNF ic.
  by move=> /eqP/meet_idPl; apply: le_comparable.
- by move/lt_eqF.
- move=> ic; apply: esym; apply: contraNF ic.
  by move=> /eqP/meet_idPl; apply: le_comparable.
Qed.

HB.instance Definition _ :=
  Order.POrder_isLattice.Build (itv_bound_display disp) (itv_bound T)
    bound_meetC bound_joinC bound_meetA bound_joinA
    bound_joinKI bound_meetKU bound_leEmeet.

Lemma bound_le0x b : -oo <= b. Proof. by []. Qed.

Lemma bound_lex1 b : b <= +oo. Proof. by case: b => [|[]]. Qed.

HB.instance Definition _ :=
  Order.hasBottom.Build (itv_bound_display disp) (itv_bound T) bound_le0x.
HB.instance Definition _ :=
  Order.hasTop.Build (itv_bound_display disp) (itv_bound T) bound_lex1.

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
Proof.
by case: i1 i2 => [? ?] [? ?]; rewrite /eq_op/=/eq_op/= eq_meetl eq_joinl.
Qed.

HB.instance Definition _ :=
  Order.POrder_isLattice.Build (interval_display disp) (interval T)
    itv_meetC itv_joinC itv_meetA itv_joinA
    itv_joinKI itv_meetKU itv_leEmeet.

Lemma itv_le0x i : Interval +oo -oo <= i. Proof. by case: i => [[|[]]]. Qed.

Lemma itv_lex1 i : i <= `]-oo, +oo[. Proof. by case: i => [?[|[]]]. Qed.

HB.instance Definition _ :=
  Order.hasBottom.Build (interval_display disp) (interval T) itv_le0x.
HB.instance Definition _ :=
  Order.hasTop.Build (interval_display disp) (interval T) itv_lex1.

Lemma in_itvI x i1 i2 : x \in i1 `&` i2 = (x \in i1) && (x \in i2).
Proof. exact: lexI. Qed.

End IntervalLattice.

Section IntervalTotal.

Variable (disp : Order.disp_t) (T : orderType disp).
Implicit Types (a b c : itv_bound T) (x y z : T) (i : interval T).

Lemma itv_bound_total : total (<=%O : rel (itv_bound T)).
Proof. by move=> [[]?|[]][[]?|[]]; rewrite /<=%O //=; case: ltgtP. Qed.

HB.instance Definition _ :=
  Order.Lattice_isTotal.Build
    (itv_bound_display disp) (itv_bound T) itv_bound_total.

Lemma itv_meetUl : @left_distributive (interval T) _ Order.meet Order.join.
Proof.
by move=> [? ?][? ?][? ?]; rewrite /Order.meet /Order.join /= -meetUl -joinIl.
Qed.

HB.instance Definition _ :=
  Order.Lattice_Meet_isDistrLattice.Build
    (interval_display disp) (interval T) itv_meetUl.

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

Lemma predC_itvl a : [predC Interval -oo a] =i Interval a +oo.
Proof.
case: a => [b x|[]//] y.
by rewrite !inE !subitvE/= bnd_simp andbT !lteBSide/= lteifNE negbK.
Qed.

Lemma predC_itvr a : [predC Interval a +oo] =i Interval -oo a.
Proof. by move=> y; rewrite inE/= -predC_itvl negbK. Qed.

Lemma predC_itv i : [predC i] =i [predU Interval -oo i.1 & Interval i.2 +oo].
Proof.
case: i => [a a']; move=> x; rewrite inE/= itv_splitI negb_and.
by symmetry; rewrite inE/= -predC_itvl -predC_itvr.
Qed.

End IntervalTotal.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Section IntervalNumDomain.

Variable R : numDomainType.
Implicit Types x : R.

Lemma mem0_itvcc_xNx x : (0 \in `[- x, x]) = (0 <= x).
Proof. by rewrite itv_boundlr [in LHS]/<=%O /= oppr_le0 andbb. Qed.

Lemma mem0_itvoo_xNx x : 0 \in `](- x), x[ = (0 < x).
Proof. by rewrite itv_boundlr [in LHS]/<=%O /= oppr_lt0 andbb. Qed.

Lemma oppr_itv ba bb (xa xb x : R) :
  (- x \in Interval (BSide ba xa) (BSide bb xb)) =
  (x \in Interval (BSide (~~ bb) (- xb)) (BSide (~~ ba) (- xa))).
Proof.
by rewrite !itv_boundlr /<=%O /= !implybF negbK andbC lteifNl lteifNr.
Qed.

Lemma oppr_itvoo (a b x : R) : (- x \in `]a, b[) = (x \in `](- b), (- a)[).
Proof. exact: oppr_itv. Qed.

Lemma oppr_itvco (a b x : R) : (- x \in `[a, b[) = (x \in `](- b), (- a)]).
Proof. exact: oppr_itv. Qed.

Lemma oppr_itvoc (a b x : R) : (- x \in `]a, b]) = (x \in `[(- b), (- a)[).
Proof. exact: oppr_itv. Qed.

Lemma oppr_itvcc (a b x : R) : (- x \in `[a, b]) = (x \in `[(- b), (- a)]).
Proof. exact: oppr_itv. Qed.

Definition miditv (R : numDomainType) (i : interval R) : R :=
  match i with
  | Interval (BSide _ a) (BSide _ b) => (a + b) / 2%:R
  | Interval -oo%O (BSide _ b) => b - 1
  | Interval (BSide _ a) +oo%O => a + 1
  | Interval -oo%O +oo%O => 0
  | _ => 0
  end.

End IntervalNumDomain.

Section IntervalField.

Variable R : numFieldType.
Implicit Types (x y z : R) (i : interval R).

Local Notation mid x y := ((x + y) / 2).

Lemma mid_in_itv : forall ba bb (xa xb : R), xa < xb ?<= if ba && ~~ bb ->
  mid xa xb \in Interval (BSide ba xa) (BSide bb xb).
Proof.
by move=> [] [] xa xb /= ?; apply/itv_dec; rewrite /= ?midf_lte // ?ltW.
Qed.

Lemma mid_in_itvoo : forall (xa xb : R), xa < xb -> mid xa xb \in `]xa, xb[.
Proof. by move=> xa xb ?; apply: mid_in_itv. Qed.

Lemma mid_in_itvcc : forall (xa xb : R), xa <= xb -> mid xa xb \in `[xa, xb].
Proof. by move=> xa xb ?; apply: mid_in_itv. Qed.

Lemma mem_miditv i : (i.1 < i.2)%O -> miditv i \in i.
Proof.
move: i => [[ba a|[]] [bb b|[]]] //= ab; first exact: mid_in_itv.
by rewrite !in_itv -lteifBlDl subrr lteif01.
by rewrite !in_itv lteifBlDr -lteifBlDl subrr lteif01.
Qed.

Lemma miditv_le_left i b : (i.1 < i.2)%O -> (BSide b (miditv i) <= i.2)%O.
Proof.
case: i => [x y] lti; have := mem_miditv lti; rewrite inE => /andP[_ ].
by apply: le_trans; rewrite !bnd_simp.
Qed.

Lemma miditv_ge_right i b : (i.1 < i.2)%O -> (i.1 <= BSide b (miditv i))%O.
Proof.
case: i => [x y] lti; have := mem_miditv lti; rewrite inE => /andP[+ _].
by move=> /le_trans; apply; rewrite !bnd_simp.
Qed.

Lemma in_segmentDgt0Pr x y z :
  reflect (forall e, e > 0 -> y \in `[x - e, z + e]) (y \in `[x, z]).
Proof.
apply/(iffP idP)=> [xyz e /[dup] e_gt0 /ltW e_ge0 | xyz_e].
  by rewrite in_itv /= lerBDr !ler_wpDr// (itvP xyz).
by rewrite in_itv /= ; apply/andP; split; apply/ler_addgt0Pr => ? /xyz_e;
  rewrite in_itv /= lerBDr => /andP [].
Qed.

Lemma in_segmentDgt0Pl x y z :
  reflect (forall e, e > 0 -> y \in `[(- e + x), (e + z)]) (y \in `[x, z]).
Proof.
apply/(equivP (in_segmentDgt0Pr x y z)).
by split=> zxy e /zxy; rewrite [z + _]addrC [_ + x]addrC.
Qed.

End IntervalField.
