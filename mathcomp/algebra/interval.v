(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq div choice fintype.
From mathcomp
Require Import bigop ssralg finset fingroup zmodp ssrint ssrnum.

(*****************************************************************************)
(* This file provide support for intervals in numerical and real domains.    *)
(* The datatype (interval R) gives a formal characterization of an           *)
(* interval, as the pair of its right and left bounds.                       *)
(*    interval R    == the type of formal intervals on R.                    *)
(*    x \in i       == when i is a formal interval on a numeric domain,      *)
(*                   \in can be used to test membership.                     *)
(*    itvP x_in_i   == where x_in_i has type x \in i, if i is ground,        *)
(*                   gives a set of rewrite rules that x_in_i imply.         *)
(* x <= y ?< if c   == x is smaller than y, and strictly if c is true        *)
(*                                                                           *)
(* We provide a set of notations to write intervals (see below)              *)
(* `[a, b], `]a, b], ..., `]-oo, a], ..., `]-oo, +oo[                        *)
(* We also provide the lemma subitvP which computes the inequalities one     *)
(* needs to prove when trying to prove the inclusion of intervals.           *)
(*                                                                           *)
(* Remark that we cannot implement a boolean comparison test for intervals   *)
(* on an arbitrary numeric domains, for this problem might be undecidable.   *)
(* Note also that type (interval R) may contain several inhabitants coding   *)
(* for the same interval. However, this pathological issues do nor arise     *)
(* when R is a real domain: we could provide a specific theory for this      *)
(* important case.                                                           *)
(*                                                                           *)
(* See also ``Formal proofs in real algebraic geometry: from ordered fields  *)
(* to quantifier elimination'', LMCS journal, 2012                           *)
(* by Cyril Cohen and Assia Mahboubi                                         *)
(*                                                                           *)
(* And "Formalized algebraic numbers: construction and first-order theory"   *)
(* Cyril Cohen, PhD, 2012, section 4.3.                                      *)
(*****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Local Notation mid x y := ((x + y) / 2%:R).

Section Lersif.

Variable (R : numDomainType).

Definition lersif (x y : R) b := if b then x < y else x <= y.

Local Notation "x <= y ?< 'if' b" := (lersif x y b)
  (at level 70, y at next level,
  format "x '[hv'  <=  y '/'  ?<  'if'  b ']'") : ring_scope.

Lemma subr_lersifr0 b (x y : R) : (y - x <= 0 ?< if b) = (y <= x ?< if b).
Proof. by case: b => /=; rewrite subr_lte0. Qed.

Lemma subr_lersif0r b (x y : R) : (0 <= y - x ?< if b) = (x <= y ?< if b).
Proof. by case: b => /=; rewrite subr_gte0. Qed.

Definition subr_lersif0 := (subr_lersifr0, subr_lersif0r).

Lemma lersif_trans x y z b1 b2 :
  x <= y ?< if b1 -> y <= z ?< if b2 -> x <= z ?< if b1 || b2.
Proof.
case: b1; first by case: b2; [apply: ltr_trans | apply: ltr_le_trans].
by case: b2; [apply: ler_lt_trans | apply: ler_trans].
Qed.

Lemma lersif01 b : 0 <= 1 ?< if b.
Proof. by case: b; apply lter01. Qed.

Lemma lersifxx x b : (x <= x ?< if b) = ~~ b.
Proof. by case: b; rewrite /= lterr. Qed.

Lemma lersifNF x y b : y <= x ?< if ~~ b -> x <= y ?< if b = false.
Proof. by case: b => /= [/ler_gtF|/ltr_geF]. Qed.

Lemma lersifS x y b : x < y -> x <= y ?< if b.
Proof. by case: b => //= /ltrW. Qed.

Lemma lersifT x y : x <= y ?< if true = (x < y). Proof. by []. Qed.

Lemma lersifF x y : x <= y ?< if false = (x <= y). Proof. by []. Qed.

Lemma lersif_oppl b x y : - x <= y ?< if b = (- y <= x ?< if b).
Proof. by case: b; apply lter_oppl. Qed.

Lemma lersif_oppr b x y : x <= - y ?< if b = (y <= - x ?< if b).
Proof. by case: b; apply lter_oppr. Qed.

Lemma lersif_0oppr b x : 0 <= - x ?< if b = (x <= 0 ?< if b).
Proof. by case: b; apply (oppr_ge0, oppr_gt0). Qed.

Lemma lersif_oppr0 b x : - x <= 0 ?< if b = (0 <= x ?< if b).
Proof. by case: b; apply (oppr_le0, oppr_lt0). Qed.

Lemma lersif_opp2 b : {mono -%R : x y /~ x <= y ?< if b}.
Proof. by case: b; apply lter_opp2. Qed.

Definition lersif_oppE := (lersif_0oppr, lersif_oppr0, lersif_opp2).

Lemma lersif_add2l b x : {mono +%R x : y z / y <= z ?< if b}.
Proof. by case: b => ? ?; apply lter_add2. Qed.

Lemma lersif_add2r b x : {mono +%R^~ x : y z / y <= z ?< if b}.
Proof. by case: b => ? ?; apply lter_add2. Qed.

Definition lersif_add2 := (lersif_add2l, lersif_add2r).

Lemma lersif_subl_addr b x y z : (x - y <= z ?< if b) = (x <= z + y ?< if b).
Proof. by case: b; apply lter_sub_addr. Qed.

Lemma lersif_subr_addr b x y z : (x <= y - z ?< if b) = (x + z <= y ?< if b).
Proof. by case: b; apply lter_sub_addr. Qed.

Definition lersif_sub_addr := (lersif_subl_addr, lersif_subr_addr).

Lemma lersif_subl_addl b x y z : (x - y <= z ?< if b) = (x <= y + z ?< if b).
Proof. by case: b; apply lter_sub_addl. Qed.

Lemma lersif_subr_addl b x y z : (x <= y - z ?< if b) = (z + x <= y ?< if b).
Proof. by case: b; apply lter_sub_addl. Qed.

Definition lersif_sub_addl := (lersif_subl_addl, lersif_subr_addl).

Lemma lersif_andb x y : {morph lersif x y : p q / p || q >-> p && q}.
Proof.
by case=> [] [] /=; rewrite ?ler_eqVlt;
  case: (_ < _)%R; rewrite ?(orbT, orbF, andbF, andbb).
Qed.

Lemma lersif_orb x y : {morph lersif x y : p q / p && q >-> p || q}.
Proof.
by case=> [] [] /=; rewrite ?ler_eqVlt;
  case: (_ < _)%R; rewrite ?(orbT, orbF, orbb).
Qed.

Lemma lersif_imply b1 b2 r1 r2 :
  b2 ==> b1 -> r1 <= r2 ?< if b1 -> r1 <= r2 ?< if b2.
Proof. by case: b1 b2 => [] [] //= _ /ltrW. Qed.

Lemma lersifW b x y : x <= y ?< if b -> x <= y.
Proof. by case: b => // /ltrW. Qed.

Lemma ltrW_lersif b x y : x < y -> x <= y ?< if b.
Proof. by case: b => // /ltrW. Qed.

Lemma lersif_pmul2l b x : 0 < x -> {mono *%R x : y z / y <= z ?< if b}.
Proof. by case: b; apply lter_pmul2l. Qed.

Lemma lersif_pmul2r b x : 0 < x -> {mono *%R^~ x : y z / y <= z ?< if b}.
Proof. by case: b; apply lter_pmul2r. Qed.

Lemma lersif_nmul2l b x : x < 0 -> {mono *%R x : y z /~ y <= z ?< if b}.
Proof. by case: b; apply lter_nmul2l. Qed.

Lemma lersif_nmul2r b x : x < 0 -> {mono *%R^~ x : y z /~ y <= z ?< if b}.
Proof. by case: b; apply lter_nmul2r. Qed.

Lemma real_lersifN x y b : x \is Num.real -> y \is Num.real ->
  x <= y ?< if ~~b = ~~ (y <= x ?< if b).
Proof. by case: b => [] xR yR /=; case: real_ltrgtP. Qed.

Lemma real_lersif_norml b x y :
  x \is Num.real ->
  (`|x| <= y ?< if b) = ((- y <= x ?< if b) && (x <= y ?< if b)).
Proof. by case: b; apply real_lter_norml. Qed.

Lemma real_lersif_normr b x y :
  y \is Num.real ->
  (x <= `|y| ?< if b) = ((x <= y ?< if b) || (x <= - y ?< if b)).
Proof. by case: b; apply real_lter_normr. Qed.

Lemma lersif_nnormr b x y : y <= 0 ?< if ~~ b -> (`|x| <= y ?< if b) = false.
Proof. by case: b => /=; apply lter_nnormr. Qed.

End Lersif.

Notation "x <= y ?< 'if' b" := (lersif x y b)
  (at level 70, y at next level,
  format "x '[hv'  <=  y '/'  ?<  'if'  b ']'") : ring_scope.

Section LersifField.

Variable (F : numFieldType) (b : bool) (z x y : F).

Lemma lersif_pdivl_mulr : 0 < z -> x <= y / z ?< if b = (x * z <= y ?< if b).
Proof. by case: b => H /=; rewrite lter_pdivl_mulr. Qed.

Lemma lersif_pdivr_mulr : 0 < z -> y / z <= x ?< if b = (y <= x * z ?< if b).
Proof. by case: b => H /=; rewrite lter_pdivr_mulr. Qed.

Lemma lersif_pdivl_mull : 0 < z -> x <= z^-1 * y ?< if b = (z * x <= y ?< if b).
Proof. by case: b => H /=; rewrite lter_pdivl_mull. Qed.

Lemma lersif_pdivr_mull : 0 < z -> z^-1 * y <= x ?< if b = (y <= z * x ?< if b).
Proof. by case: b => H /=; rewrite lter_pdivr_mull. Qed.

Lemma lersif_ndivl_mulr : z < 0 -> x <= y / z ?< if b = (y <= x * z ?< if b).
Proof. by case: b => H /=; rewrite lter_ndivl_mulr. Qed.

Lemma lersif_ndivr_mulr : z < 0 -> y / z <= x ?< if b = (x * z <= y ?< if b).
Proof. by case: b => H /=; rewrite lter_ndivr_mulr. Qed.

Lemma lersif_ndivl_mull : z < 0 -> x <= z^-1 * y ?< if b = (y <=z * x ?< if b).
Proof. by case: b => H /=; rewrite lter_ndivl_mull. Qed.

Lemma lersif_ndivr_mull : z < 0 -> z^-1 * y <= x ?< if b = (z * x <= y ?< if b).
Proof. by case: b => H /=; rewrite lter_ndivr_mull. Qed.

End LersifField.

Section LersifRealDomain.

Variable (R : realDomainType) (b : bool) (x y z e : R).

Lemma lersif_norml :
  (`|x| <= y ?< if b) = (- y <= x ?< if b) && (x <= y ?< if b).
Proof. by case: b; apply lter_norml. Qed.

Lemma lersif_normr :
  (x <= `|y| ?< if b) = (x <= y ?< if b) || (x <= - y ?< if b).
Proof. by case: b; apply lter_normr. Qed.

Lemma lersif_distl :
  (`|x - y| <= e ?< if b) = (y - e <= x ?< if b) && (x <= y + e ?< if b).
Proof. by case: b; apply lter_distl. Qed.

Lemma lersif_minr :
  (x <= Num.min y z ?< if b) = (x <= y ?< if b) && (x <= z ?< if b).
Proof. by case: b; apply lter_minr. Qed.

Lemma lersif_minl :
  (Num.min y z <= x ?< if b) = (y <= x ?< if b) || (z <= x ?< if b).
Proof. by case: b; apply lter_minl. Qed.

Lemma lersif_maxr :
  (x <= Num.max y z ?< if b) = (x <= y ?< if b) || (x <= z ?< if b).
Proof. by case: b; apply lter_maxr. Qed.

Lemma lersif_maxl :
  (Num.max y z <= x ?< if b) = (y <= x ?< if b) && (z <= x ?< if b).
Proof. by case: b; apply lter_maxl. Qed.

End LersifRealDomain.

Section IntervalPo.

Variant itv_bound (T : Type) : Type := BOpen_if of bool & T | BInfty.
Notation BOpen := (BOpen_if true).
Notation BClose := (BOpen_if false).
Variant interval (T : Type) := Interval of itv_bound T & itv_bound T.

Variable (R : numDomainType).

Definition pred_of_itv (i : interval R) : pred R :=
  [pred x | let: Interval l u := i in
      match l with
        | BOpen a => a < x
        | BClose a => a <= x
        | BInfty => true
      end &&
      match u with
        | BOpen b => x < b
        | BClose b => x <= b
        | BInfty => true
      end].
Canonical Structure itvPredType := Eval hnf in mkPredType pred_of_itv.

(* We provide the 9 following notations to help writing formal intervals *)
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

(* we compute a set of rewrite rules associated to an interval *)
Definition itv_rewrite (i : interval R) x : Type :=
  let: Interval l u := i in
    (match l with
       | BClose a => (a <= x) * (x < a = false)
       | BOpen a => (a <= x) * (a < x) * (x <= a = false)
       | BInfty => forall x : R, x == x
     end *
    match u with
       | BClose b => (x <= b) * (b < x = false)
       | BOpen b => (x <= b) * (x < b) * (b <= x = false)
       | BInfty => forall x : R, x == x
     end *
    match l, u with
       | BClose a, BClose b =>
         (a <= b) * (b < a = false) * (a \in `[a, b]) * (b \in `[a, b])
       | BClose a, BOpen b =>
         (a <= b) * (a < b) * (b <= a = false)
         * (a \in `[a, b]) * (a \in `[a, b[)* (b \in `[a, b]) * (b \in `]a, b])
       | BOpen a, BClose b =>
         (a <= b) * (a < b) * (b <= a = false)
         * (a \in `[a, b]) * (a \in `[a, b[)* (b \in `[a, b]) * (b \in `]a, b])
       | BOpen a, BOpen b =>
         (a <= b) * (a < b) * (b <= a = false)
         * (a \in `[a, b]) * (a \in `[a, b[)* (b \in `[a, b]) * (b \in `]a, b])
       | _, _ => forall x : R, x == x
    end)%type.

Definition itv_decompose (i : interval R) x : Prop :=
  let: Interval l u := i in
  ((match l with
    | BClose a => (a <= x) : Prop
    | BOpen a => (a < x) : Prop
    | BInfty => True
  end : Prop) *
  (match u with
    | BClose b => (x <= b) : Prop
    | BOpen b => (x < b) : Prop
    | BInfty => True
  end : Prop))%type.

Lemma itv_dec : forall (x : R) (i : interval R),
  reflect (itv_decompose i x) (x \in i).
Proof. by move=> x [[[] a|] [[] b|]]; apply: (iffP andP); case. Qed.

Arguments itv_dec {x i}.

Definition le_boundl (b1 b2 : itv_bound R) :=
  match b1, b2 with
    | BOpen_if b1 x1, BOpen_if b2 x2 => x1 <= x2 ?< if (~~ b2 && b1)
    | BOpen_if _ _, BInfty => false
    | _, _ => true
  end.

Definition le_boundr (b1 b2 : itv_bound R) :=
  match b1, b2 with
    | BOpen_if b1 x1, BOpen_if b2 x2 => x1 <= x2 ?< if (~~ b1 && b2)
    | BInfty, BOpen_if _ _ => false
    | _, _ => true
  end.

Lemma itv_boundlr bl br x :
  (x \in Interval bl br) =
  (le_boundl bl (BClose x)) && (le_boundr (BClose x) br).
Proof. by move: bl br => [[] a|] [[] b|]. Qed.

Lemma le_boundl_refl : reflexive le_boundl.
Proof. by move=> [[] b|]; rewrite /le_boundl /= ?lerr. Qed.

Hint Resolve le_boundl_refl : core.

Lemma le_boundr_refl : reflexive le_boundr.
Proof. by move=> [[] b|]; rewrite /le_boundr /= ?lerr. Qed.

Hint Resolve le_boundr_refl : core.

Lemma le_boundl_trans : transitive le_boundl.
Proof.
move=> [lb1 lr1 |] [lb2 lr2 |] [lb3 lr3 |] //= H H0.
apply: {H H0} (lersif_imply _ (lersif_trans H H0)).
by case: lb1; case: lb2; case: lb3.
Qed.

Lemma le_boundr_trans : transitive le_boundr.
Proof.
move=> [lb1 lr1 |] [lb2 lr2 |] [lb3 lr3 |] //= H H0.
apply: {H H0} (lersif_imply _ (lersif_trans H H0)).
by case: lb1; case: lb2; case: lb3.
Qed.

Lemma le_boundl_bb x b1 b2 :
  le_boundl (BOpen_if b1 x) (BOpen_if b2 x) = (b1 ==> b2).
Proof. by rewrite /le_boundl lersifxx andbC negb_and negbK implybE. Qed.

Lemma le_boundr_bb x b1 b2 :
  le_boundr (BOpen_if b1 x) (BOpen_if b2 x) = (b2 ==> b1).
Proof. by rewrite /le_boundr lersifxx andbC negb_and negbK implybE. Qed.

Lemma itv_xx x bl br :
  Interval (BOpen_if bl x) (BOpen_if br x) =i 
  if ~~ (bl || br) then pred1 x else pred0.
Proof.
by move: bl br => [] [] y /=; rewrite !inE 1?eq_sym (eqr_le, lter_anti).
Qed.

Lemma itv_gte ba xa bb xb :  xb <= xa ?< if ~~ (ba || bb) 
  -> Interval (BOpen_if ba xa) (BOpen_if bb xb) =i pred0.
Proof.
move=> hx y; rewrite itv_boundlr inE /=.
by apply/negP => /andP [] /lersif_trans hy /hy {hy}; rewrite lersifNF.
Qed.

Lemma boundl_in_itv : forall ba xa b,
  xa \in Interval (BOpen_if ba xa) b = 
  if ba then false else le_boundr (BClose xa) b.
Proof. by move=> [] xa [[] xb|] //=; rewrite inE lterr. Qed.

Lemma boundr_in_itv : forall bb xb a,
  xb \in Interval a (BOpen_if bb xb) =
  if bb then false else le_boundl a (BClose xb).
Proof. by move=> [] xb [[] xa|] //=; rewrite inE lterr ?andbT ?andbF. Qed.

Definition bound_in_itv := (boundl_in_itv, boundr_in_itv).

Lemma itvP : forall (x : R) (i : interval R), x \in i -> itv_rewrite i x.
Proof.
move=> x [[[] a|] [[] b|]]; move/itv_dec=> //= [hl hu]; do ?[split=> //;
  do ?[by rewrite ltrW | by rewrite ltrWN | by rewrite ltrNW |
    by rewrite (ltr_geF, ler_gtF)]];
  rewrite ?(bound_in_itv) /le_boundl /le_boundr //=; do ?
    [ by rewrite (@ler_trans _ x)
    | by rewrite 1?ltrW // (@ltr_le_trans _ x)
    | by rewrite 1?ltrW // (@ler_lt_trans _ x) // 1?ltrW
    | by apply: negbTE; rewrite ler_gtF // (@ler_trans _ x)
    | by apply: negbTE; rewrite ltr_geF // (@ltr_le_trans _ x) // 1?ltrW
    | by apply: negbTE; rewrite ltr_geF // (@ler_lt_trans _ x)].
Qed.

Hint Rewrite intP : core.
Arguments itvP [x i].

Definition subitv (i1 i2 : interval R) :=
  match i1, i2 with
    | Interval a1 b1, Interval a2 b2 => le_boundl a2 a1 && le_boundr b1 b2
  end.

Lemma subitvP : forall (i2 i1 : interval R), subitv i1 i2 -> {subset i1 <= i2}.
Proof.
by move=> [[[] a2|] [[] b2|]] [[[] a1|] [[] b1|]];
  rewrite /subitv //; case/andP=> /= ha hb x hx; rewrite ?inE;
    rewrite ?(ler_trans ha) ?(ler_lt_trans ha) ?(ltr_le_trans ha) //;
      rewrite ?(ler_trans _ hb) ?(ltr_le_trans _ hb) ?(ler_lt_trans _ hb) //;
        rewrite ?(itvP hx) //.
Qed.

Lemma subitvPr : forall (a b1 b2 : itv_bound R),
  le_boundr b1 b2 -> {subset (Interval a b1) <= (Interval a b2)}.
Proof. by move=> a b1 b2 hb; apply: subitvP=> /=; rewrite hb andbT. Qed.

Lemma subitvPl : forall (a1 a2 b : itv_bound R),
  le_boundl a2 a1 -> {subset (Interval a1 b) <= (Interval a2 b)}.
Proof. by move=> a1 a2 b ha; apply: subitvP=> /=; rewrite ha /=. Qed.

Lemma lersif_in_itv : forall ba bb xa xb x,
  x \in Interval (BOpen_if ba xa) (BOpen_if bb xb) ->
        xa <= xb ?< if ba || bb.
Proof.
by move=> ba bb xa xb y; rewrite itv_boundlr; case/andP; apply: lersif_trans.
Qed.

Lemma ltr_in_itv : forall ba bb xa xb x, ba || bb ->
  x \in Interval (BOpen_if ba xa) (BOpen_if bb xb) -> xa < xb.
Proof.
move=> ba bb xa xb x; case bab: (_ || _) => // _.
by move/lersif_in_itv; rewrite bab.
Qed.

Lemma ler_in_itv : forall ba bb xa xb x,
  x \in Interval (BOpen_if ba xa) (BOpen_if bb xb) -> xa <= xb.
Proof. by move=> ba bb xa xb x; move/lersif_in_itv; move/lersifW. Qed.

Lemma mem0_itvcc_xNx : forall x, (0 \in `[-x, x]) = (0 <= x).
Proof.
by move=> x; rewrite !inE; case hx: (0 <= _); rewrite (andbT, andbF) ?ge0_cp.
Qed.

Lemma mem0_itvoo_xNx : forall x, 0 \in `](-x), x[ = (0 < x).
Proof.
by move=> x; rewrite !inE; case hx: (0 < _); rewrite (andbT, andbF) ?gt0_cp.
Qed.

Lemma itv_splitI : forall a b, forall x,
  x \in Interval a b = (x \in Interval a (BInfty _)) && (x \in Interval (BInfty _) b).
Proof. by move=> [[] a|] [[] b|] x; rewrite ?inE ?andbT. Qed.

Lemma oppr_itv ba bb (xa xb x : R) :
  (-x \in Interval (BOpen_if ba xa) (BOpen_if bb xb)) = 
  (x \in Interval (BOpen_if bb (-xb)) (BOpen_if ba (-xa))).
Proof. by move: ba bb => [] []; rewrite ?inE lter_oppr andbC lter_oppl. Qed.

Lemma oppr_itvoo (a b x : R) : (-x \in `]a, b[) = (x \in `](-b), (-a)[).
Proof. exact: oppr_itv. Qed.

Lemma oppr_itvco (a b x : R) : (-x \in `[a, b[) = (x \in `](-b), (-a)]).
Proof. exact: oppr_itv. Qed.

Lemma oppr_itvoc (a b x : R) : (-x \in `]a, b]) = (x \in `[(-b), (-a)[).
Proof. exact: oppr_itv. Qed.

Lemma oppr_itvcc (a b x : R) : (-x \in `[a, b]) = (x \in `[(-b), (-a)]).
Proof. exact: oppr_itv. Qed.

End IntervalPo.

Notation BOpen := (BOpen_if true).
Notation BClose := (BOpen_if false).
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

Section IntervalOrdered.

Variable R : realDomainType.

Lemma le_boundl_total : total (@le_boundl R).
Proof. by move=> [[] l |] [[] r |] //=; case: (ltrgtP l r). Qed.

Lemma le_boundr_total : total (@le_boundr R).
Proof. by move=> [[] l |] [[] r |] //=; case (ltrgtP l r). Qed.

Lemma lersifN (x y : R) b : (x <= y ?< if ~~ b) = ~~ (y <= x ?< if b).
Proof. by rewrite real_lersifN ?num_real. Qed.

Lemma itv_splitU (xc : R) bc a b : xc \in Interval a b ->
  forall y, y \in Interval a b =
    (y \in Interval a (BOpen_if (~~ bc) xc))
    || (y \in Interval (BOpen_if bc xc) b).
Proof.
move=> hxc y; rewrite !itv_boundlr [le_boundr]lock /=.
have [la /=|nla /=] := boolP (le_boundl a _); rewrite -lock.
  have [lb /=|nlb /=] := boolP (le_boundr _ b); rewrite ?andbT ?andbF ?orbF //.
    by case: bc => //=; case: ltrgtP.
  symmetry; apply: contraNF nlb; rewrite /le_boundr /=.
  case: b hxc => // bb xb hxc hyc.
  suff /(lersif_trans hyc) : xc <= xb ?< if bb.
    by case: bc {hyc} => //= /lersifS.
  by case: a bb hxc {la} => [[] ?|] [] /= /itvP->.
symmetry; apply: contraNF nla => /andP [hc _].
case: a hxc hc => [[] xa|] hxc; rewrite /le_boundl //=.
  by move=> /lersifW /(ltr_le_trans _) -> //; move: b hxc=> [[] ?|] /itvP->.
by move=> /lersifW /(ler_trans _) -> //; move: b hxc=> [[] ?|] /itvP->.
Qed.

Lemma itv_splitU2 (x : R) a b : x \in Interval a b ->
  forall y, y \in Interval a b =
    [|| (y \in Interval a (BOpen x)), (y == x)
      | (y \in Interval (BOpen x) b)].
Proof.
move=> xab y; rewrite (itv_splitU false xab y); congr (_ || _).
rewrite (@itv_splitU x true _ _ _ y); first by rewrite itv_xx inE.
by move: xab; rewrite boundl_in_itv itv_boundlr => /andP [].
Qed.

End IntervalOrdered.

Section IntervalField.

Variable R : realFieldType.

Lemma mid_in_itv : forall ba bb (xa xb : R), xa <= xb ?< if ba || bb
  -> mid xa xb \in Interval (BOpen_if ba xa) (BOpen_if bb xb).
Proof.
by move=> [] [] xa xb /= hx; apply/itv_dec=> /=; rewrite ?midf_lte // ?ltrW.
Qed.

Lemma mid_in_itvoo : forall (xa xb : R), xa < xb -> mid xa xb \in `]xa, xb[.
Proof. by move=> xa xb hx; apply: mid_in_itv. Qed.

Lemma mid_in_itvcc : forall (xa xb : R), xa <= xb -> mid xa xb \in `[xa, xb].
Proof. by move=> xa xb hx; apply: mid_in_itv. Qed.

End IntervalField.
