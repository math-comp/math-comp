(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import div fintype bigop order ssralg finset fingroup.
From mathcomp Require Import ssrnum.

(******************************************************************************)
(* This file provide support for intervals in ordered types. The datatype     *)
(* (interval T) gives a formal characterization of an interval, as the pair   *)
(* of its right and left bounds.                                              *)
(*    interval R    == the type of formal intervals on R.                     *)
(*    x \in i       == when i is a formal interval on an ordered type,        *)
(*                     \in can be used to test membership.                    *)
(*    itvP x_in_i   == where x_in_i has type x \in i, if i is ground,         *)
(*                     gives a set of rewrite rules that x_in_i imply.        *)
(* x < y ?<= if c   == x is smaller than y, and strictly if c is false        *)
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

Section LteifPOrder.

Variable (disp : unit) (T : porderType disp).
Implicit Types (b : bool) (x y z : T).

Definition lteif x y b := if b then x <= y else x < y.

Local Notation "x < y ?<= 'if' b" := (lteif x y b)
  (at level 70, y at next level,
  format "x '[hv'  <  y '/'  ?<=  'if'  b ']'") : order_scope.

Lemma lteif_trans x y z b1 b2 :
  x < y ?<= if b1 -> y < z ?<= if b2 -> x < z ?<= if b1 && b2.
Proof.
case: b1 b2 => [][];
  [exact: le_trans | exact: le_lt_trans | exact: lt_le_trans | exact: lt_trans].
Qed.

Lemma lteif_anti b1 b2 x y :
  (x < y ?<= if b1) && (y < x ?<= if b2) = b1 && b2 && (x == y).
Proof. by case: b1 b2 => [][]; rewrite lte_anti. Qed.

Lemma lteifxx x b : (x < x ?<= if b) = b.
Proof. by case: b; rewrite /= ltexx. Qed.

Lemma lteifNF x y b : y < x ?<= if ~~ b -> x < y ?<= if b = false.
Proof. by case: b => [/lt_geF|/le_gtF]. Qed.

Lemma lteifS x y b : x < y -> x < y ?<= if b.
Proof. by case: b => //= /ltW. Qed.

Lemma lteifT x y : x < y ?<= if true = (x <= y). Proof. by []. Qed.

Lemma lteifF x y : x < y ?<= if false = (x < y). Proof. by []. Qed.

Lemma lteif_orb x y : {morph lteif x y : p q / p || q}.
Proof. by case=> [][] /=; case: comparableP. Qed.

Lemma lteif_andb x y : {morph lteif x y : p q / p && q}.
Proof. by case=> [][] /=; case: comparableP. Qed.

Lemma lteif_imply b1 b2 x y : b1 ==> b2 -> x < y ?<= if b1 -> x < y ?<= if b2.
Proof. by case: b1 b2 => [][] //= _ /ltW. Qed.

Lemma lteifW b x y : x < y ?<= if b -> x <= y.
Proof. by case: b => // /ltW. Qed.

Lemma ltrW_lteif b x y : x < y -> x < y ?<= if b.
Proof. by case: b => // /ltW. Qed.

Lemma comparable_lteifN x y b :
  x >=< y -> x < y ?<= if ~~b = ~~ (y < x ?<= if b).
Proof. by case: b => /=; case: comparableP. Qed.

End LteifPOrder.

Notation "x < y ?<= 'if' b" := (lteif x y b)
  (at level 70, y at next level,
  format "x '[hv'  <  y '/'  ?<=  'if'  b ']'") : order_scope.

Notation "x < y ?<= 'if' b" := (@lteif ring_display _ x y b)
  (at level 70, y at next level,
  format "x '[hv'  <  y '/'  ?<=  'if'  b ']'") : ring_scope.

Section LteifTotal.

Variable (disp : unit) (T : orderType disp) (b : bool) (x y z e : T).

Lemma lteif_minr :
  (x < Order.min y z ?<= if b) = (x < y ?<= if b) && (x < z ?<= if b).
Proof. by case: b; rewrite /= (le_minr, lt_minr). Qed.

Lemma lteif_minl :
  (Order.min y z < x ?<= if b) = (y < x ?<= if b) || (z < x ?<= if b).
Proof. by case: b; rewrite /= (le_minl, lt_minl). Qed.

Lemma lteif_maxr :
  (x < Order.max y z ?<= if b) = (x < y ?<= if b) || (x < z ?<= if b).
Proof. by case: b; rewrite /= (le_maxr, lt_maxr). Qed.

Lemma lteif_maxl :
  (Order.max y z < x ?<= if b) = (y < x ?<= if b) && (z < x ?<= if b).
Proof. by case: b; rewrite /= (le_maxl, lt_maxl). Qed.

Lemma lteifN : (x < y ?<= if ~~ b) = ~~ (y < x ?<= if b).
Proof. by rewrite comparable_lteifN ?comparableT. Qed.

End LteifTotal.

Variant itv_bound (T : Type) : Type := BClose_if of bool & T | BInfty.
Definition itv_boundl := itv_bound.
Definition itv_boundr := itv_bound.
Notation BOpen := (BClose_if false).
Notation BClose := (BClose_if true).
Variant interval (T : Type) := Interval of itv_boundl T & itv_boundr T.

(* We provide the 9 following notations to help writing formal intervals *)
Notation "`[ a , b ]" := (Interval (BClose a) (BClose b))
  (at level 0, a, b at level 9 , format "`[ a ,  b ]") : order_scope.
Notation "`] a , b ]" := (Interval (BOpen a) (BClose b))
  (at level 0, a, b at level 9 , format "`] a ,  b ]") : order_scope.
Notation "`[ a , b [" := (Interval (BClose a) (BOpen b))
  (at level 0, a, b at level 9 , format "`[ a ,  b [") : order_scope.
Notation "`] a , b [" := (Interval (BOpen a) (BOpen b))
  (at level 0, a, b at level 9 , format "`] a ,  b [") : order_scope.
Notation "`] '-oo' , b ]" := (Interval (BInfty _) (BClose b))
  (at level 0, b at level 9 , format "`] '-oo' ,  b ]") : order_scope.
Notation "`] '-oo' , b [" := (Interval (BInfty _) (BOpen b))
  (at level 0, b at level 9 , format "`] '-oo' ,  b [") : order_scope.
Notation "`[ a , '+oo' [" := (Interval (BClose a) (BInfty _))
  (at level 0, a at level 9 , format "`[ a ,  '+oo' [") : order_scope.
Notation "`] a , '+oo' [" := (Interval (BOpen a) (BInfty _))
  (at level 0, a at level 9 , format "`] a ,  '+oo' [") : order_scope.
Notation "`] -oo , '+oo' [" := (Interval (BInfty _) (BInfty _))
  (at level 0, format "`] -oo ,  '+oo' [") : order_scope.

Notation "`[ a , b ]" := (Interval (BClose a) (BClose b))
  (at level 0, a, b at level 9 , format "`[ a ,  b ]") : ring_scope.
Notation "`] a , b ]" := (Interval (BOpen a) (BClose b))
  (at level 0, a, b at level 9 , format "`] a ,  b ]") : ring_scope.
Notation "`[ a , b [" := (Interval (BClose a) (BOpen b))
  (at level 0, a, b at level 9 , format "`[ a ,  b [") : ring_scope.
Notation "`] a , b [" := (Interval (BOpen a) (BOpen b))
  (at level 0, a, b at level 9 , format "`] a ,  b [") : ring_scope.
Notation "`] '-oo' , b ]" := (Interval (BInfty _) (BClose b))
  (at level 0, b at level 9 , format "`] '-oo' ,  b ]") : ring_scope.
Notation "`] '-oo' , b [" := (Interval (BInfty _) (BOpen b))
  (at level 0, b at level 9 , format "`] '-oo' ,  b [") : ring_scope.
Notation "`[ a , '+oo' [" := (Interval (BClose a) (BInfty _))
  (at level 0, a at level 9 , format "`[ a ,  '+oo' [") : ring_scope.
Notation "`] a , '+oo' [" := (Interval (BOpen a) (BInfty _))
  (at level 0, a at level 9 , format "`] a ,  '+oo' [") : ring_scope.
Notation "`] -oo , '+oo' [" := (Interval (BInfty _) (BInfty _))
  (at level 0, format "`] -oo ,  '+oo' [") : ring_scope.

Fact itv_boundl_display (disp : unit) : unit. Proof. exact. Qed.
Fact itv_boundr_display (disp : unit) : unit. Proof. exact. Qed.
Fact interval_display (disp : unit) : unit. Proof. exact. Qed.

Section IntervalEq.

Variable T : eqType.

Definition eq_itv_bound (b1 b2 : itv_bound T) : bool :=
  match b1, b2 with
    | BClose_if a x, BClose_if b y => (a == b) && (x == y)
    | BInfty, BInfty => true
    | _, _ => false
  end.

Lemma eq_itv_boundP : Equality.axiom eq_itv_bound.
Proof.
move=> b1 b2; apply: (iffP idP).
- by move: b1 b2 => [a x|][b y|] => //= /andP [] /eqP -> /eqP ->.
- by move=> <-; case: b1 => //= a x; rewrite !eqxx.
Qed.

Canonical itv_bound_eqMixin := EqMixin eq_itv_boundP.
Canonical itv_bound_eqType := EqType (itv_bound T) itv_bound_eqMixin.
Canonical itv_boundl_eqType := [eqType of itv_boundl T].
Canonical itv_boundr_eqType := [eqType of itv_boundr T].

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
            match b with BInfty => None | BClose_if b x => Some (b, x) end)
         (fun b =>
            match b with None => BInfty _ | Some (b, x) => BClose_if b x end).
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
Canonical itv_boundl_choiceType (T : choiceType) :=
  [choiceType of itv_boundl T].
Canonical itv_boundr_choiceType (T : choiceType) :=
  [choiceType of itv_boundr T].

Canonical itv_bound_countType (T : countType) :=
  CountType (itv_bound T) (CanCountMixin (@itv_bound_can T)).
Canonical interval_countType (T : countType) :=
  CountType (interval T) (CanCountMixin (@interval_can T)).
Canonical itv_boundl_countType (T : countType) := [countType of itv_boundl T].
Canonical itv_boundr_countType (T : countType) := [countType of itv_boundr T].

Canonical itv_bound_finType (T : finType) :=
  FinType (itv_bound T) (CanFinMixin (@itv_bound_can T)).
Canonical interval_finType (T : finType) :=
  FinType (interval T) (CanFinMixin (@interval_can T)).
Canonical itv_boundl_finType (T : finType) := [finType of itv_boundl T].
Canonical itv_boundr_finType (T : finType) := [finType of itv_boundr T].

End Exports.

End IntervalChoice.
Export IntervalChoice.Exports.

Section IntervalPOrder.

Variable (disp : unit) (T : porderType disp).
Implicit Types (x y z : T) (i : interval T).

Definition pred_of_itv i : pred T :=
  [pred x | let: Interval l u := i in
      match l with
        | BClose_if b lb => lb < x ?<= if b
        | BInfty => true
      end &&
      match u with
        | BClose_if b ub => x < ub ?<= if b
        | BInfty => true
      end].

Canonical Structure itvPredType := PredType pred_of_itv.

(* we compute a set of rewrite rules associated to an interval *)
Definition itv_rewrite i x : Type :=
  let: Interval l u := i in
    (match l with
       | BClose a => (a <= x) * (x < a = false)
       | BOpen a => (a <= x) * (a < x) * (x <= a = false) * (x < a = false)
       | BInfty => forall x : T, x == x
     end *
     match u with
       | BClose b => (x <= b) * (b < x = false)
       | BOpen b => (x <= b) * (x < b) * (b <= x = false) * (b < x = false)
       | BInfty => forall x : T, x == x
     end *
     match l, u with
       | BClose a, BClose b =>
         (a <= b) * (b < a = false) * (a \in `[a, b]) * (b \in `[a, b])
       | BClose a, BOpen b =>
         (a <= b) * (a < b) * (b <= a = false) * (b < a = false)
         * (a \in `[a, b]) * (a \in `[a, b[) * (b \in `[a, b]) * (b \in `]a, b])
       | BOpen a, BClose b =>
         (a <= b) * (a < b) * (b <= a = false) * (b < a = false)
         * (a \in `[a, b]) * (a \in `[a, b[) * (b \in `[a, b]) * (b \in `]a, b])
       | BOpen a, BOpen b =>
         (a <= b) * (a < b) * (b <= a = false) * (b < a = false)
         * (a \in `[a, b]) * (a \in `[a, b[) * (b \in `[a, b]) * (b \in `]a, b])
       | _, _ => forall x : T, x == x
     end)%type.

Definition itv_decompose i x : Prop :=
  let: Interval l u := i in
  ((match l with
    | BClose_if b lb => (lb < x ?<= if b) : Prop
    | BInfty => True
  end : Prop) *
  (match u with
    | BClose_if b ub => (x < ub ?<= if b) : Prop
    | BInfty => True
  end : Prop))%type.

Lemma itv_dec : forall x i, reflect (itv_decompose i x) (x \in i).
Proof. by move=> ? [[? ?|][? ?|]]; apply: (iffP andP); case. Qed.

Arguments itv_dec {x i}.

Definition le_boundl (b1 b2 : itv_boundl T) :=
  match b1, b2 with
    | BClose_if b1 x1, BClose_if b2 x2 => x1 < x2 ?<= if b2 ==> b1
    | BClose_if _ _, BInfty => false
    | _, _ => true
  end.

Definition le_boundr (b1 b2 : itv_boundr T) :=
  match b1, b2 with
    | BClose_if b1 x1, BClose_if b2 x2 => x1 < x2 ?<= if b1 ==> b2
    | BInfty, BClose_if _ _ => false
    | _, _ => true
  end.

Lemma itv_boundlr bl br x :
  (x \in Interval bl br) =
  (le_boundl bl (BClose x)) && (le_boundr (BClose x) br).
Proof. by case: bl br => [? ?|][]. Qed.

Lemma le_boundl_refl : reflexive le_boundl.
Proof. by move=> [[] b|]; rewrite /le_boundl /= ?lerr. Qed.

Lemma le_boundr_refl : reflexive le_boundr.
Proof. by move=> [[] b|]; rewrite /le_boundr /= ?lerr. Qed.

Hint Resolve le_boundl_refl le_boundr_refl : core.

Lemma le_boundl_anti : antisymmetric le_boundl.
Proof. by case=> [[]?|][[]?|] //=; case: comparableP => // ->. Qed.

Lemma le_boundl_converse_anti : antisymmetric (fun b => le_boundl ^~ b).
Proof. by move=> ? ? /le_boundl_anti. Qed.

Lemma le_boundr_anti : antisymmetric le_boundr.
Proof. by case=> [[]?|][[]?|] //=; case: comparableP => // ->. Qed.

Lemma le_boundl_trans : transitive le_boundl.
Proof.
by move=> [[] x|][[] y|][[] z|] lexy leyz //;
  apply: (lteif_imply _ (lteif_trans lexy leyz)).
Qed.

Lemma le_boundl_converse_trans : transitive (fun b => le_boundl ^~ b).
Proof. move=> ? ? ? ? /le_boundl_trans; exact. Qed.

Lemma le_boundr_trans : transitive le_boundr.
Proof.
by move=> [[] x|][[] y|][[] z|] lexy leyz //;
  apply: (lteif_imply _ (lteif_trans lexy leyz)).
Qed.

Lemma le_boundl_bb x b1 b2 :
  le_boundl (BClose_if b1 x) (BClose_if b2 x) = (b2 ==> b1).
Proof. by rewrite /le_boundl lteifxx. Qed.

Lemma le_boundr_bb x b1 b2 :
  le_boundr (BClose_if b1 x) (BClose_if b2 x) = (b1 ==> b2).
Proof. by rewrite /le_boundr lteifxx. Qed.

Lemma itv_xx x bl br :
  Interval (BClose_if bl x) (BClose_if br x) =i
  if bl && br then pred1 x else pred0.
Proof. by move: bl br => [][] y /=; rewrite !inE lteif_anti /=. Qed.

Lemma itv_gte ba xa bb xb :
  xb < xa ?<= if ~~ (ba && bb) ->
  Interval (BClose_if ba xa) (BClose_if bb xb) =i pred0.
Proof.
move=> ? y; rewrite itv_boundlr inE /=.
by apply/negP => /andP [] lexay /(lteif_trans lexay); rewrite lteifNF.
Qed.

Lemma boundl_in_itv : forall ba xa b,
  xa \in Interval (BClose_if ba xa) b =
  if ba then le_boundr (BClose xa) b else false.
Proof. by move=> [] xa [b xb|]; rewrite inE lteifxx. Qed.

Lemma boundr_in_itv : forall bb xb a,
  xb \in Interval a (BClose_if bb xb) =
  if bb then le_boundl a (BClose xb) else false.
Proof. by move=> [] xb [b xa|]; rewrite inE lteifxx /= ?andbT ?andbF. Qed.

Definition bound_in_itv := (boundl_in_itv, boundr_in_itv).

Lemma itvP : forall x i, x \in i -> itv_rewrite i x.
Proof.
move=> x [[[] a|][[] b|]] /itv_dec [ha hb]; do !split;
  rewrite ?bound_in_itv //=; do 1?[apply/negbTE; rewrite (le_gtF, lt_geF)];
  by [| apply: ltW | move: (lteif_trans ha hb) => //=; exact: ltW].
Qed.

Arguments itvP [x i].

Definition itv_boundl_porderMixin :=
  @LePOrderMixin
    (itv_boundl_eqType T) (fun b => le_boundl^~ b) _ (fun _ _ => erefl)
    le_boundl_refl le_boundl_converse_anti le_boundl_converse_trans.
Canonical itv_boundl_porderType :=
  POrderType (itv_boundl_display disp) (itv_boundl T) itv_boundl_porderMixin.

Definition itv_boundr_porderMixin :=
  LePOrderMixin (fun _ _ => erefl)
                le_boundr_refl le_boundr_anti le_boundr_trans.
Canonical itv_boundr_porderType :=
  POrderType (itv_boundr_display disp) (itv_boundr T) itv_boundr_porderMixin.

Definition subitv i1 i2 :=
  match i1, i2 with
    | Interval a1 b1, Interval a2 b2 => (a1 <= a2) && (b1 <= b2)
  end.

Lemma subitv_refl : reflexive subitv.
Proof. by case=> /= ? ?; rewrite !lexx. Qed.

Lemma subitv_anti : antisymmetric subitv.
Proof.
by case=> [? ?][? ?]; rewrite andbACA => /andP[] /le_anti -> /le_anti ->.
Qed.

Lemma subitv_trans : transitive subitv.
Proof.
case=> [yl yr][xl xr][zl zr] /andP [Hl Hr] /andP [Hl' Hr'] /=.
by rewrite (le_trans Hl Hl') (le_trans Hr Hr').
Qed.

Definition interval_porderMixin :=
  LePOrderMixin (fun _ _ => erefl) subitv_refl subitv_anti subitv_trans.
Canonical interval_porderType :=
  POrderType (interval_display disp) (interval T) interval_porderMixin.

Lemma subitvP i1 i2 : i1 <= i2 -> {subset i1 <= i2}.
Proof.
by case: i1 i2 => [[b2 l2|][b2' u2|]][[b1 l1|][b1' u1|]]
          /andP [] /= ha hb x /andP [ha' hb']; apply/andP; split => //;
  (apply/lteif_imply: (lteif_trans ha ha'); case: b1 b2 ha ha' => [][]) ||
  (apply/lteif_imply: (lteif_trans hb' hb); case: b1' b2' hb hb' => [][]).
Qed.

Lemma subitvPr (a : itv_boundl T) (b1 b2 : itv_boundr T) :
  le_boundr b1 b2 -> {subset (Interval a b1) <= (Interval a b2)}.
Proof. by move=> leb; apply: subitvP; rewrite /<=%O /= lexx. Qed.

Lemma subitvPl (a1 a2 : itv_boundl T) (b : itv_boundr T) :
  le_boundl a2 a1 -> {subset (Interval a1 b) <= (Interval a2 b)}.
Proof. by move=> lea; apply: subitvP; rewrite /<=%O /= lexx andbT. Qed.

Lemma inEsubitv x i : (x \in i) = (`[x, x] <= i).
Proof. by rewrite inE /=; case: i => [[[]?|][[]?|]]. Qed.

Lemma lteif_in_itv ba bb xa xb x :
  x \in Interval (BClose_if ba xa) (BClose_if bb xb) ->
        xa < xb ?<= if ba && bb.
Proof. by case: ba bb => [][] /itvP /= ->. Qed.

Lemma ltr_in_itv ba bb xa xb x :
  ~~ (ba && bb) -> x \in Interval (BClose_if ba xa) (BClose_if bb xb) ->
  xa < xb.
Proof. by move=> /negbTE bab /lteif_in_itv; rewrite bab. Qed.

Lemma ler_in_itv ba bb xa xb x :
  x \in Interval (BClose_if ba xa) (BClose_if bb xb) -> xa <= xb.
Proof. by move/lteif_in_itv/lteifW. Qed.

End IntervalPOrder.

Section IntervalLattice.

Variable (disp : unit) (T : latticeType disp).
Implicit Types (x y z : T) (i : interval T).

Definition itv_boundl_meet (bl br : itv_boundl T) : itv_boundl T :=
  match bl, br with
    | BInfty, _ => br | _, BInfty => bl
    | BClose_if xb x, BClose_if yb y =>
      BClose_if ((~~ (x <= y) || yb) && (~~ (y <= x) || xb)) (x `|` y)
  end.

Definition itv_boundr_meet (bl br : itv_boundr T) : itv_boundr T :=
  match bl, br with
    | BInfty, _ => br | _, BInfty => bl
    | BClose_if xb x, BClose_if yb y =>
      BClose_if ((~~ (x <= y) || xb) && (~~ (y <= x) || yb)) (x `&` y)
  end.

Definition itv_boundl_join (bl br : itv_boundl T) : itv_bound T :=
  match bl, br with
    | BInfty, _ | _, BInfty => BInfty _
    | BClose_if xb x, BClose_if yb y =>
      BClose_if ((x <= y) && xb || (y <= x) && yb) (x `&` y)
  end.

Definition itv_boundr_join (bl br : itv_boundr T) : itv_bound T :=
  match bl, br with
    | BInfty, _ | _, BInfty => BInfty _
    | BClose_if xb x, BClose_if yb y =>
      BClose_if ((x <= y) && yb || (y <= x) && xb) (x `|` y)
  end.

Lemma itv_boundl_meetC : commutative itv_boundl_meet.
Proof.
by case=> [? ?|][? ?|] //=; rewrite joinC; congr BClose_if;
  case: lcomparableP; rewrite ?andbT // 1?andbC.
Qed.

Lemma itv_boundr_meetC : commutative itv_boundr_meet.
Proof.
by case=> [? ?|][? ?|] //=; rewrite meetC; congr BClose_if;
  case: lcomparableP; rewrite ?andbT // 1?andbC.
Qed.

Lemma itv_boundl_joinC : commutative itv_boundl_join.
Proof.
by case=> [? ?|][? ?|] //=; rewrite meetC; congr BClose_if;
  case: lcomparableP; rewrite ?orbF // 1?orbC.
Qed.

Lemma itv_boundr_joinC : commutative itv_boundr_join.
Proof.
by case=> [? ?|][? ?|] //=; rewrite joinC; congr BClose_if;
  case: lcomparableP; rewrite ?orbF // 1?orbC.
Qed.

Lemma itv_boundl_meetA : associative itv_boundl_meet.
Proof.
case=> [? x|][? y|][? z|]//; congr BClose_if; rewrite ?leUx ?joinA //.
by case: (lcomparableP x y) => [|||->]; case: (lcomparableP y z) => [|||->];
  case: (lcomparableP x z) => [|||//<-] //=;
  case: (lcomparableP x y) => //=; case: (lcomparableP y z) => //=;
  rewrite ?orbT ?andbT ?lexx ?andbA.
Qed.

Lemma itv_boundr_meetA : associative itv_boundr_meet.
Proof.
case=> [? x|][? y|][? z|]//; congr BClose_if; rewrite ?lexI ?meetA //.
by case: (lcomparableP x y) => [|||->]; case: (lcomparableP y z) => [|||->];
  case: (lcomparableP x z) => [|||//<-] //=;
  case: (lcomparableP x y) => //=; case: (lcomparableP y z) => //=;
  rewrite ?orbT ?andbT ?lexx ?andbA.
Qed.

Lemma itv_boundl_joinA : associative itv_boundl_join.
Proof.
case=> [? x|][? y|][? z|]//; congr BClose_if; rewrite ?lexI ?meetA //.
by case: (lcomparableP x y) => [|||->]; case: (lcomparableP y z) => [|||->];
  case: (lcomparableP x z) => [|||//<-] //=;
  case: (lcomparableP x y) => //=; case: (lcomparableP y z) => //=;
  rewrite ?andbF ?orbF ?lexx ?orbA.
Qed.

Lemma itv_boundr_joinA : associative itv_boundr_join.
Proof.
case=> [? x|][? y|][? z|]//; congr BClose_if; rewrite ?leUx ?joinA //.
by case: (lcomparableP x y) => [|||->]; case: (lcomparableP y z) => [|||->];
  case: (lcomparableP x z) => [|||//<-] //=;
  case: (lcomparableP x y) => //=; case: (lcomparableP y z) => //=;
  rewrite ?andbF ?orbF ?lexx ?orbA.
Qed.

Lemma itv_boundl_meetKU b2 b1 : itv_boundl_join b1 (itv_boundl_meet b1 b2) = b1.
Proof.
case: b1 b2 => [? ?|][? ?|] //=; congr BClose_if;
  rewrite ?joinKI ?meetxx ?leUl ?leUx ?lexx ?orbb //=.
by case: lcomparableP; rewrite ?orbb ?orbF ?andKb.
Qed.

Lemma itv_boundr_meetKU b2 b1 : itv_boundr_join b1 (itv_boundr_meet b1 b2) = b1.
Proof.
case: b1 b2 => [? ?|][? ?|] //=; congr BClose_if;
  rewrite ?meetKU ?joinxx ?leIl ?lexI ?lexx ?orbb //.
by case: lcomparableP; rewrite ?andbT /= ?orbb ?andbK.
Qed.

Lemma itv_boundl_joinKI b2 b1 : itv_boundl_meet b1 (itv_boundl_join b1 b2) = b1.
Proof.
case: b1 b2 => [? ?|][? ?|] //=; congr BClose_if;
  rewrite ?meetKU // leIl lexI lexx.
by case: lcomparableP; rewrite ?orbF ?andbb /= ?orbK.
Qed.

Lemma itv_boundr_joinKI b2 b1 : itv_boundr_meet b1 (itv_boundr_join b1 b2) = b1.
Proof.
case: b1 b2 => [? ?|][? ?|] //=; congr BClose_if;
  rewrite ?joinKI // leUl leUx lexx.
by case: lcomparableP; rewrite ?andbT ?andbb ?orKb.
Qed.

Lemma itv_boundl_leEmeet b1 b2 :
  le_boundl b2 b1 = (itv_boundl_meet b1 b2 == b1).
Proof.
by case: b1 b2 => [[]?|][[]?|] //=;
  rewrite /eq_op /= ?eqxx // eq_joinl; case: lcomparableP.
Qed.

Lemma itv_boundr_leEmeet b1 b2 :
  le_boundr b1 b2 = (itv_boundr_meet b1 b2 == b1).
Proof.
by case: b1 b2 => [[]?|][[]?|] //=;
  rewrite /eq_op /= ?eqxx //= -leEmeet; case: lcomparableP.
Qed.

Definition itv_boundl_latticeMixin :=
  LatticeMixin itv_boundl_meetC itv_boundl_joinC
               itv_boundl_meetA itv_boundl_joinA
               itv_boundl_joinKI itv_boundl_meetKU itv_boundl_leEmeet.
Canonical itv_boundl_latticeType :=
  LatticeType (itv_boundl T) itv_boundl_latticeMixin.

Definition itv_boundr_latticeMixin :=
  LatticeMixin itv_boundr_meetC itv_boundr_joinC
               itv_boundr_meetA itv_boundr_joinA
               itv_boundr_joinKI itv_boundr_meetKU itv_boundr_leEmeet.
Canonical itv_boundr_latticeType :=
  LatticeType (itv_boundr T) itv_boundr_latticeMixin.

Definition itv_meet i1 i2 : interval T :=
  let: Interval b1l b1r := i1 in
  let: Interval b2l b2r := i2 in Interval (b1l `&` b2l) (b1r `&` b2r).

Definition itv_join i1 i2 : interval T :=
  let: Interval b1l b1r := i1 in
  let: Interval b2l b2r := i2 in Interval (b1l `|` b2l) (b1r `|` b2r).

Lemma itv_meetC : commutative itv_meet.
Proof. by case=> [? ?][? ?]; congr Interval; rewrite meetC. Qed.

Lemma itv_joinC : commutative itv_join.
Proof. by case=> [? ?][? ?]; congr Interval; rewrite joinC. Qed.

Lemma itv_meetA : associative itv_meet.
Proof. by case=> [? ?][? ?][? ?]; rewrite /= !meetA. Qed.

Lemma itv_joinA : associative itv_join.
Proof. by case=> [? ?][? ?][? ?]; rewrite /= !joinA. Qed.

Lemma itv_meetKU i2 i1 : itv_join i1 (itv_meet i1 i2) = i1.
Proof. by case: i1 i2 => [? ?][? ?]; rewrite /= !meetKU. Qed.

Lemma itv_joinKI i2 i1 : itv_meet i1 (itv_join i1 i2) = i1.
Proof. by case: i1 i2 => [? ?][? ?]; rewrite /= !joinKI. Qed.

Lemma itv_leEmeet i1 i2 : (i1 <= i2) = (itv_meet i1 i2 == i1).
Proof. by case: i1 i2 => [? ?][? ?]; rewrite /<=%O /eq_op /= !leEmeet. Qed.

Definition interval_latticeMixin :=
  LatticeMixin itv_meetC itv_joinC itv_meetA itv_joinA
               itv_joinKI itv_meetKU itv_leEmeet.
Canonical interval_latticeType :=
  LatticeType (interval T) interval_latticeMixin.

Definition itv_meet1i : left_id `]-oo, +oo[ Order.meet.
Proof. by case=> i []. Qed.

Definition itv_meeti1 : right_id `]-oo, +oo[ Order.meet.
Proof. by case=> [[? ?|][? ?|]]. Qed.

Canonical itv_intersection_monoid := Monoid.Law itv_meetA itv_meet1i itv_meeti1.
Canonical itv_intersection_comoid := Monoid.ComLaw itv_meetC.

Lemma in_itv_meet x i1 i2 : x \in i1 `&` i2 = (x \in i1) && (x \in i2).
Proof. by rewrite !inEsubitv lexI. Qed.

End IntervalLattice.

Section IntervalTotal.

Variable (disp : unit) (T : orderType disp).
Implicit Types (x y z : T) (i : interval T).

Lemma le_boundl_total : total (@le_boundl _ T).
Proof. by move=> [[]l|] [[]r|] //=; case: (ltgtP l r). Qed.

Lemma le_boundr_total : total (@le_boundr _ T).
Proof. by move=> [[]l|] [[]r|] //=; case: (ltgtP l r). Qed.

Definition itv_boundl_totalMixin : totalLatticeMixin _ :=
  fun b1 b2 => le_boundl_total b2 b1.

Canonical itv_boundl_distrLatticeType :=
  DistrLatticeType (itv_boundl T) itv_boundl_totalMixin.
Canonical itv_boundl_orderType :=
  OrderType (itv_boundl T) itv_boundl_totalMixin.

Canonical itv_boundr_distrLatticeType :=
  DistrLatticeType (itv_boundr T) (le_boundr_total : totalLatticeMixin _).
Canonical itv_boundr_orderType := OrderType (itv_boundr T) le_boundr_total.

Lemma itv_meetUl : @left_distributive (interval T) _ Order.meet Order.join.
Proof.
by move=> [? ?][? ?][? ?]; rewrite /Order.meet /Order.join /= !meetUl.
Qed.

Canonical interval_distrLatticeType :=
  DistrLatticeType (interval T) (DistrLatticeMixin itv_meetUl).

Lemma itv_splitU (xc : T) bc a b : xc \in Interval a b ->
  forall y, y \in Interval a b =
    (y \in Interval a (BClose_if (~~ bc) xc))
    || (y \in Interval (BClose_if bc xc) b).
Proof.
move=> xc_in y; move: xc_in.
rewrite !itv_boundlr [le_boundr (BClose _) (BClose_if _ _)]/=
        [le_boundr]lock /= lteifN -lock.
case/andP => leaxc lexcb;
  case: (boolP (le_boundl a _)) => leay; case: (boolP (le_boundr _ b)) => leyb;
  rewrite /= (andbT, andbF) ?orbF ?orNb //=;
  [apply/esym/negbF | apply/esym/negbTE].
- by case: b lexcb leyb => //= bb b; rewrite -lteifN => lexcb leyb;
    apply/lteif_imply: (lteif_trans lexcb leyb); rewrite andbN.
- case: a leaxc leay => //= ab a leaxc;
    apply/contra => /(lteif_trans leaxc); apply/lteif_imply.
  by rewrite implybE negb_and orbC orbA orbN.
Qed.

Lemma itv_splitU2 x a b : x \in Interval a b ->
  forall y, y \in Interval a b =
    [|| (y \in Interval a (BOpen x)), (y == x)
      | (y \in Interval (BOpen x) b)].
Proof.
move=> xab y; rewrite (itv_splitU true xab y); congr (_ || _).
rewrite (@itv_splitU x false _ _ _ y); first by rewrite itv_xx inE.
by move: xab; rewrite boundl_in_itv itv_boundlr => /andP [].
Qed.

Lemma itv_total_meet3E i1 i2 i3 :
  i1 `&` i2 `&` i3 \in [:: i1 `&` i2; i1 `&` i3; i2 `&` i3].
Proof.
rewrite !inE /eq_op; case: i1 i2 i3 => [b1l b1r] [b2l b2r] [b3l b3r] /=.
case: (leP b2l b1l); case: (leP b3l b2l); case: (leP b3l b1l);
  case: (leP b1r b2r); case: (leP b2r b3r); case: (leP b1r b3r);
  rewrite ?eqxx ?andbT ?orbT //= => b13r b23r b12r b31l b32l b21l.
- by case: leP b31l (le_trans b32l b21l).
- by case: leP b31l (le_trans b32l b21l).
- by case: leP b31l (le_trans b32l b21l).
- by case: leP b13r (le_trans b12r b23r).
- by case: leP b13r (le_trans b12r b23r).
- by case: leP b13r (lt_trans b23r b12r).
- by case: leP b31l (lt_trans b21l b32l).
- by case: leP b31l (lt_trans b21l b32l).
- by case: leP b31l (lt_trans b21l b32l).
- by case: leP b13r (lt_trans b23r b12r).
Qed.

Lemma itv_total_join3E i1 i2 i3 :
  i1 `|` i2 `|` i3 \in [:: i1 `|` i2; i1 `|` i3; i2 `|` i3].
Proof.
rewrite !inE /eq_op; case: i1 i2 i3 => [b1l b1r] [b2l b2r] [b3l b3r] /=.
case: (leP b2l b1l); case: (leP b3l b2l); case: (leP b3l b1l);
  case: (leP b1r b2r); case: (leP b2r b3r); case: (leP b1r b3r);
  rewrite ?eqxx ?andbT ?orbT //= => b13r b23r b12r b31l b32l b21l.
- by case: leP b13r (le_trans b12r b23r).
- by case: leP b31l (le_trans b32l b21l).
- by case: leP b31l (le_trans b32l b21l).
- by case: leP b31l (le_trans b32l b21l).
- by case: leP b13r (le_trans b12r b23r).
- by case: leP b13r (lt_trans b23r b12r).
- by case: leP b13r (lt_trans b23r b12r).
- by case: leP b31l (lt_trans b21l b32l).
- by case: leP b31l (lt_trans b21l b32l).
- by case: leP b31l (lt_trans b21l b32l).
Qed.

End IntervalTotal.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Section LteifNumDomain.

Variable R : numDomainType.
Implicit Types (b : bool) (x y z : R).

Local Notation "x < y ?<= 'if' b" := (@lteif _ R x y b)
  (at level 70, y at next level,
  format "x '[hv'  <  y '/'  ?<=  'if'  b ']'") : ring_scope.

Lemma subr_lteifr0 b (x y : R) : (y - x < 0 ?<= if b) = (y < x ?<= if b).
Proof. by case: b => /=; rewrite subr_lte0. Qed.

Lemma subr_lteif0r b (x y : R) : (0 < y - x ?<= if b) = (x < y ?<= if b).
Proof. by case: b => /=; rewrite subr_gte0. Qed.

Definition subr_lteif0 := (subr_lteifr0, subr_lteif0r).

Lemma lteif01 b : 0 < 1 ?<= if b.
Proof. by case: b; rewrite /= lter01. Qed.

Lemma lteif_oppl b x y : - x < y ?<= if b = (- y < x ?<= if b).
Proof. by case: b; rewrite /= lter_oppl. Qed.

Lemma lteif_oppr b x y : x < - y ?<= if b = (y < - x ?<= if b).
Proof. by case: b; rewrite /= lter_oppr. Qed.

Lemma lteif_0oppr b x : 0 < - x ?<= if b = (x < 0 ?<= if b).
Proof. by case: b; rewrite /= (oppr_ge0, oppr_gt0). Qed.

Lemma lteif_oppr0 b x : - x < 0 ?<= if b = (0 < x ?<= if b).
Proof. by case: b; rewrite /= (oppr_le0, oppr_lt0). Qed.

Lemma lteif_opp2 b : {mono -%R : x y /~ x < y ?<= if b}.
Proof. by case: b => ? ?; rewrite /= lter_opp2. Qed.

Definition lteif_oppE := (lteif_0oppr, lteif_oppr0, lteif_opp2).

Lemma lteif_add2l b x : {mono +%R x : y z / y < z ?<= if b}.
Proof. by case: b => ? ?; rewrite /= lter_add2. Qed.

Lemma lteif_add2r b x : {mono +%R^~ x : y z / y < z ?<= if b}.
Proof. by case: b => ? ?; rewrite /= lter_add2. Qed.

Definition lteif_add2 := (lteif_add2l, lteif_add2r).

Lemma lteif_subl_addr b x y z : (x - y < z ?<= if b) = (x < z + y ?<= if b).
Proof. by case: b; rewrite /= lter_sub_addr. Qed.

Lemma lteif_subr_addr b x y z : (x < y - z ?<= if b) = (x + z < y ?<= if b).
Proof. by case: b; rewrite /= lter_sub_addr. Qed.

Definition lteif_sub_addr := (lteif_subl_addr, lteif_subr_addr).

Lemma lteif_subl_addl b x y z : (x - y < z ?<= if b) = (x < y + z ?<= if b).
Proof. by case: b; rewrite /= lter_sub_addl. Qed.

Lemma lteif_subr_addl b x y z : (x < y - z ?<= if b) = (z + x < y ?<= if b).
Proof. by case: b; rewrite /= lter_sub_addl. Qed.

Definition lteif_sub_addl := (lteif_subl_addl, lteif_subr_addl).

Lemma lteif_pmul2l b x : 0 < x -> {mono *%R x : y z / y < z ?<= if b}.
Proof. by case: b => ? ? ?; rewrite /= lter_pmul2l. Qed.

Lemma lteif_pmul2r b x : 0 < x -> {mono *%R^~ x : y z / y < z ?<= if b}.
Proof. by case: b => ? ? ?; rewrite /= lter_pmul2r. Qed.

Lemma lteif_nmul2l b x : x < 0 -> {mono *%R x : y z /~ y < z ?<= if b}.
Proof. by case: b => ? ? ?; rewrite /= lter_nmul2l. Qed.

Lemma lteif_nmul2r b x : x < 0 -> {mono *%R^~ x : y z /~ y < z ?<= if b}.
Proof. by case: b => ? ? ?; rewrite /= lter_nmul2r. Qed.

Lemma real_lteifN x y b : x \is Num.real -> y \is Num.real ->
  x < y ?<= if ~~b = ~~ (y < x ?<= if b).
Proof. by move=> ? ?; rewrite comparable_lteifN ?real_comparable. Qed.

Lemma real_lteif_norml b x y :
  x \is Num.real ->
  (`|x| < y ?<= if b) = ((- y < x ?<= if b) && (x < y ?<= if b)).
Proof. by case: b => ?; rewrite /= real_lter_norml. Qed.

Lemma real_lteif_normr b x y :
  y \is Num.real ->
  (x < `|y| ?<= if b) = ((x < y ?<= if b) || (x < - y ?<= if b)).
Proof. by case: b => ?; rewrite /= real_lter_normr. Qed.

Lemma lteif_nnormr b x y : y < 0 ?<= if ~~ b -> (`|x| < y ?<= if b) = false.
Proof. by case: b => ?; rewrite /= lter_nnormr. Qed.

End LteifNumDomain.

Section LteifRealDomain.

Variable (R : realDomainType) (b : bool) (x y z e : R).

Lemma lteif_norml :
  (`|x| < y ?<= if b) = (- y < x ?<= if b) && (x < y ?<= if b).
Proof. by case: b; rewrite /= lter_norml. Qed.

Lemma lteif_normr :
  (x < `|y| ?<= if b) = (x < y ?<= if b) || (x < - y ?<= if b).
Proof. by case: b; rewrite /= lter_normr. Qed.

Lemma lteif_distl :
  (`|x - y| < e ?<= if b) = (y - e < x ?<= if b) && (x < y + e ?<= if b).
Proof. by case: b; rewrite /= lter_distl. Qed.

End LteifRealDomain.

Section LteifField.

Variable (F : numFieldType) (b : bool) (z x y : F).

Lemma lteif_pdivl_mulr : 0 < z -> x < y / z ?<= if b = (x * z < y ?<= if b).
Proof. by case: b => ? /=; rewrite lter_pdivl_mulr. Qed.

Lemma lteif_pdivr_mulr : 0 < z -> y / z < x ?<= if b = (y < x * z ?<= if b).
Proof. by case: b => ? /=; rewrite lter_pdivr_mulr. Qed.

Lemma lteif_pdivl_mull : 0 < z -> x < z^-1 * y ?<= if b = (z * x < y ?<= if b).
Proof. by case: b => ? /=; rewrite lter_pdivl_mull. Qed.

Lemma lteif_pdivr_mull : 0 < z -> z^-1 * y < x ?<= if b = (y < z * x ?<= if b).
Proof. by case: b => ? /=; rewrite lter_pdivr_mull. Qed.

Lemma lteif_ndivl_mulr : z < 0 -> x < y / z ?<= if b = (y < x * z ?<= if b).
Proof. by case: b => ? /=; rewrite lter_ndivl_mulr. Qed.

Lemma lteif_ndivr_mulr : z < 0 -> y / z < x ?<= if b = (x * z < y ?<= if b).
Proof. by case: b => ? /=; rewrite lter_ndivr_mulr. Qed.

Lemma lteif_ndivl_mull : z < 0 -> x < z^-1 * y ?<= if b = (y < z * x ?<= if b).
Proof. by case: b => ? /=; rewrite lter_ndivl_mull. Qed.

Lemma lteif_ndivr_mull : z < 0 -> z^-1 * y < x ?<= if b = (z * x < y ?<= if b).
Proof. by case: b => ? /=; rewrite lter_ndivr_mull. Qed.

End LteifField.

Section IntervalNumDomain.

Variable R : numFieldType.
Implicit Types x : R.

Lemma mem0_itvcc_xNx x : (0 \in `[-x, x]) = (0 <= x).
Proof. by rewrite !inE /= oppr_le0 andbb. Qed.

Lemma mem0_itvoo_xNx x : 0 \in `](-x), x[ = (0 < x).
Proof. by rewrite !inE /= oppr_lt0 andbb. Qed.

Lemma itv_splitI : forall a b x,
  x \in Interval a b =
  (x \in Interval a (BInfty _)) && (x \in Interval (BInfty _) b).
Proof. by move=> [? ?|] [? ?|] ?; rewrite !inE ?andbT. Qed.

Lemma oppr_itv ba bb (xa xb x : R) :
  (-x \in Interval (BClose_if ba xa) (BClose_if bb xb)) =
  (x \in Interval (BClose_if bb (-xb)) (BClose_if ba (-xa))).
Proof. by rewrite !inE lteif_oppr andbC lteif_oppl. Qed.

Lemma oppr_itvoo (a b x : R) : (-x \in `]a, b[) = (x \in `](-b), (-a)[).
Proof. exact: oppr_itv. Qed.

Lemma oppr_itvco (a b x : R) : (-x \in `[a, b[) = (x \in `](-b), (-a)]).
Proof. exact: oppr_itv. Qed.

Lemma oppr_itvoc (a b x : R) : (-x \in `]a, b]) = (x \in `[(-b), (-a)[).
Proof. exact: oppr_itv. Qed.

Lemma oppr_itvcc (a b x : R) : (-x \in `[a, b]) = (x \in `[(-b), (-a)]).
Proof. exact: oppr_itv. Qed.

End IntervalNumDomain.

Section IntervalField.

Variable R : realFieldType.

Local Notation mid x y := ((x + y) / 2%:R).

Lemma mid_in_itv : forall ba bb (xa xb : R), xa < xb ?<= if ba && bb
  -> mid xa xb \in Interval (BClose_if ba xa) (BClose_if bb xb).
Proof.
by move=> [] [] xa xb /= ?; apply/itv_dec=> /=; rewrite ?midf_lte // ?ltW.
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

Local Notation lersif x y b := (lteif x y (~~ b)) (only parsing).

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
Proof. exact: real_lteifN. Qed.

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
Proof. exact: lteifN. Qed.

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

Local Notation BOpen_if b x := (BClose_if (~~ b) x) (only parsing).

Lemma lersif_in_itv ba bb (xa xb x : R) :
  x \in Interval (BOpen_if ba xa) (BOpen_if bb xb) ->
        xa <= xb ?< if ba || bb.
Proof. by move/lteif_in_itv; rewrite negb_or. Qed.

End IntervalPo.

End mc_1_11.

Notation "@ 'lersif'" :=
  ((fun _ (R : numDomainType) x y b => @lteif _ R x y (~~ b))
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
  ((fun _ => @mc_1_11.real_lersifN) (deprecate real_lersifN real_lteifN))
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
  ((fun _ => @mc_1_11.lersifN) (deprecate lersifN lteifN))
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

(* `BOpen_if` has been deprecated, but `deprecate` does not accept a          *)
(* constructor that takes arguments.                                          *)
Notation "@ 'BOpen_if'" := (fun T b x => @BClose_if T (~~ b) x)
(*  ((fun _ T b x => @BClose_if T (~~ b) x) (deprecate BOpen_if BClose_if))   *)
                             (at level 10, only parsing).

Notation BOpen_if := (@BOpen_if _).

Notation "@ 'lersif_in_itv'" :=
  ((fun _ => @mc_1_11.lersif_in_itv) (deprecate lersif_in_itv lteif_in_itv))
    (at level 10, only parsing).

Notation lersif_in_itv := (@lersif_in_itv _ _ _ _ _ _) (only parsing).

(* `itv_intersection` accepts any `numDomainType` but `Order.meet` accepts    *)
(* only `realDomainType`. Use `Order.meet` instead of `itv_meet`.             *)
(* (`deprecate` does not accept a qualified name.)                            *)
Notation "@ 'itv_intersection'" :=
  ((fun _ (R : realDomainType) => @Order.meet _ [latticeType of interval R])
     (deprecate itv_intersection itv_meet))
    (at level 10, only parsing) : fun_scope.

Notation itv_intersection := (@itv_intersection _) (only parsing).

Notation "@ 'itv_intersection1i'" :=
  ((fun _ => @itv_meet1i _) (deprecate itv_intersection1i itv_meet1i))
    (at level 10, only parsing) : fun_scope.

Notation itv_intersection1i := (@itv_intersection1i _) (only parsing).

Notation "@ 'itv_intersectioni1'" :=
  ((fun _ => @itv_meeti1 _) (deprecate itv_intersectioni1 itv_meeti1))
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
