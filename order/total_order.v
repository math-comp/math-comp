(* (c) Copyright 2006-2019 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import path fintype bigop finset preorder porder lattice.

(******************************************************************************)
(*                 Types equipped with total order relations                  *)
(*                                                                            *)
(* NB: See CONTRIBUTING.md for an introduction to HB concepts and commands.   *)
(*                                                                            *)
(* NB: See the header of all_order.v for general remarks about the preorder   *)
(*     and order structures in MathComp, and the files in this directory.     *)
(*                                                                            *)
(* * Interfaces                                                               *)
(* We provide the following interfaces for types equipped with an order:      *)
(*                                                                            *)
(*               orderType d == the type of totally ordered types             *)
(*                              The HB class is called Total.                 *)
(*              bOrderType d == orderType with a bottom element               *)
(*                              The HB class is called BTotal.                *)
(*              tOrderType d == orderType with a top element                  *)
(*                              The HB class is called TTotal.                *)
(*             tbOrderType d == orderType with both a top and a bottom        *)
(*                              The HB class is called TBTotal.               *)
(*            finOrderType d == the type of totally ordered finite types      *)
(*                              The HB class is called FinTotal.              *)
(*          finTBOrderType d == the type of nonempty totally ordered finite   *)
(*                              types                                         *)
(*                              The HB class is called FinTBTotal.            *)
(*                                                                            *)
(* and their joins with subType:                                              *)
(*                                                                            *)
(*           subOrder d T P d' == join of orderType d' and                    *)
(*                                subLatticeType d T P d'                     *)
(*                                The HB class is called SubOrder.            *)
(*                                                                            *)
(* The following notations are provided to build substructures:               *)
(* [SubLattice_isSubOrder of U by <: with disp] ==                            *)
(* [SubLattice_isSubOrder of U by <:] ==                                      *)
(* [SubPOrder_isSubOrder of U by <: with disp] ==                             *)
(* [SubPOrder_isSubOrder of U by <:] ==                                       *)
(* [SubChoice_isSubOrder of U by <: with disp] ==                             *)
(* [SubChoice_isSubOrder of U by <:] == orderType mixin for a subType whose   *)
(*                          base type is an orderType                         *)
(*                                                                            *)
(* Acknowledgments: The files in this directory are based on prior work by    *)
(* D. Dreyer, G. Gonthier, A. Nanevski, P-Y Strub, B. Ziliani                 *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope order_scope.

Module Order.

Export Order.
Import Order.Theory.

#[key="T", primitive]
HB.mixin Record DistrLattice_isTotal d T & DistrLattice d T :=
  { le_total : total (<=%O : rel T) }.

#[short(type="orderType")]
HB.structure Definition Total d :=
  { T of DistrLattice_isTotal d T & DistrLattice d T }.

#[short(type="bOrderType")]
HB.structure Definition BTotal d := { T of Total d T & hasBottom d T }.

#[short(type="tOrderType")]
HB.structure Definition TTotal d := { T of Total d T & hasTop d T }.

#[short(type="tbOrderType")]
HB.structure Definition TBTotal d := { T of BTotal d T & hasTop d T }.

(**********)
(* FINITE *)
(**********)

#[short(type="finOrderType")]
HB.structure Definition FinTotal d := { T of Finite T & Total d T }.

#[short(type="finTBOrderType")]
HB.structure Definition FinTBTotal d := { T of Finite T & TBTotal d T }.

(************)
(* SUBTYPES *)
(************)

#[short(type="subOrder")]
HB.structure Definition SubOrder d (T : orderType d) S d' :=
  { U of @SubLattice d T S d' U & Total d' U }.

(********)
(* DUAL *)
(********)

(*
FIXME: we have two issues in the dual instance declarations in the DualOrder
module below:
1. HB.saturate is slow, and
2. if we declare them by HB.instance, some declarations fail because it unfolds
   [dual] and the generated instance does not typecheck
   (math-comp/hierarchy-builder#257).
*)
Module DualOrder.

HB.instance Definition _ d (T : orderType d) :=
  DistrLattice_isTotal.Build (dual_display d) T^d (fun x y => le_total y x).

HB.saturate.

End DualOrder.
HB.export DualOrder.

(**********)
(* THEORY *)
(**********)

Module Import TotalTheory.
Section TotalTheory.
Context {disp : disp_t} {T : orderType disp}.
Implicit Types (x y z t : T) (s : seq T).

Definition le_total : total (<=%O : rel T) := le_total.
Hint Resolve le_total : core.

Lemma ge_total : total (>=%O : rel T).
Proof. by move=> ? ?; apply: le_total. Qed.
Hint Resolve ge_total : core.

Lemma comparableT x y : x >=< y. Proof. exact: le_total. Qed.
Hint Extern 0 (is_true (_ >=< _)%O) => solve [apply: comparableT] : core.

Lemma sort_le_sorted s : sorted <=%O (sort <=%O s).
Proof. exact: sort_sorted. Qed.
Hint Resolve sort_le_sorted : core.

Lemma sort_lt_sorted s : sorted <%O (sort <=%O s) = uniq s.
Proof. by rewrite lt_sorted_uniq_le sort_uniq sort_le_sorted andbT. Qed.

Lemma perm_sort_leP s1 s2 : reflect (sort <=%O s1 = sort <=%O s2) (perm_eq s1 s2).
Proof. exact/perm_sortP/le_anti/le_trans/le_total. Qed.

Lemma filter_sort_le p s : filter p (sort <=%O s) = sort <=%O (filter p s).
Proof. exact/filter_sort/le_trans/le_total. Qed.

Lemma mask_sort_le s (m : bitseq) :
  {m_s : bitseq | mask m_s (sort <=%O s) = sort <=%O (mask m s)}.
Proof. exact/mask_sort/le_trans/le_total. Qed.

Lemma sorted_mask_sort_le s (m : bitseq) :
  sorted <=%O (mask m s) -> {m_s : bitseq | mask m_s (sort <=%O s) = mask m s}.
Proof. exact/sorted_mask_sort/le_trans/le_total. Qed.

Lemma subseq_sort_le : {homo sort <=%O : s1 s2 / @subseq T s1 s2}.
Proof. exact/subseq_sort/le_trans/le_total. Qed.

Lemma sorted_subseq_sort_le s1 s2 :
  subseq s1 s2 -> sorted <=%O s1 -> subseq s1 (sort <=%O s2).
Proof. exact/sorted_subseq_sort/le_trans/le_total. Qed.

Lemma mem2_sort_le s x y : x <= y -> mem2 s x y -> mem2 (sort <=%O s) x y.
Proof. exact/mem2_sort/le_trans/le_total. Qed.

Lemma leNgt x y : (x <= y) = ~~ (y < x). Proof. exact: comparable_leNgt. Qed.

Lemma ltNge x y : (x < y) = ~~ (y <= x). Proof. exact: comparable_ltNge. Qed.

Definition ltgtP x y := LatticeTheory.lcomparable_ltgtP (comparableT x y).
Definition leP x y := LatticeTheory.lcomparable_leP (comparableT x y).
Definition ltP x y := LatticeTheory.lcomparable_ltP (comparableT x y).

Lemma wlog_le P :
     (forall x y, P y x -> P x y) -> (forall x y, x <= y -> P x y) ->
   forall x y, P x y.
Proof. by move=> sP hP x y; case: (leP x y) => [| /ltW] /hP // /sP. Qed.

Lemma wlog_lt P :
    (forall x, P x x) ->
    (forall x y, (P y x -> P x y)) -> (forall x y, x < y -> P x y) ->
  forall x y, P x y.
Proof. by move=> rP sP hP x y; case: (ltgtP x y) => [||->] // /hP // /sP. Qed.

Lemma neq_lt x y : (x != y) = (x < y) || (y < x). Proof. by case: ltgtP. Qed.

Lemma lt_total x y : x != y -> (x < y) || (y < x). Proof. by case: ltgtP. Qed.

Lemma eq_leLR x y z t :
  (x <= y -> z <= t) -> (y < x -> t < z) -> (x <= y) = (z <= t).
Proof. by rewrite !ltNge => ? /contraTT ?; apply/idP/idP. Qed.

Lemma eq_leRL x y z t :
  (x <= y -> z <= t) -> (y < x -> t < z) -> (z <= t) = (x <= y).
Proof. by move=> *; apply/esym/eq_leLR. Qed.

Lemma eq_ltLR x y z t :
  (x < y -> z < t) -> (y <= x -> t <= z) -> (x < y) = (z < t).
Proof. by rewrite !leNgt => ? /contraTT ?; apply/idP/idP. Qed.

Lemma eq_ltRL x y z t :
  (x < y -> z < t) -> (y <= x -> t <= z) -> (z < t) = (x < y).
Proof. by move=> *; apply/esym/eq_ltLR. Qed.

Lemma le_gtP {x y} : reflect (forall z, z < x -> z < y) (x <= y).
Proof.
by apply: (iffP idP) => [xy z /lt_le_trans|/(_ y)/[!ltNge]/contraTT]; apply.
Qed.

Lemma le_ltP {x y} : reflect (forall z, y < z -> x < z) (x <= y).
Proof.
by apply: (iffP idP) => [xy z /(le_lt_trans _)|/(_ x)/[!ltNge]/contraTT]; apply.
Qed.

Lemma eq_gtP {x y} : reflect (forall z, (z < x) = (z < y)) (x == y).
Proof.
by apply: (iffP eq_leP) => + k => /(_ k)/[!ltNge]/(congr1 negb); rewrite ?negbK.
Qed.

Lemma eq_ltP {x y} : reflect (forall z, (x < z) = (y < z)) (x == y).
Proof.
by apply: (iffP eq_geP) => + k => /(_ k)/[!ltNge]/(congr1 negb); rewrite ?negbK.
Qed.

(* max and min is join and meet *)

Lemma meetEtotal x y : x `&` y = min x y. Proof. by case: leP. Qed.
Lemma joinEtotal x y : x `|` y = max x y. Proof. by case: leP. Qed.

(* max and min theory *)

Lemma minEgt x y : min x y = if x > y then y else x. Proof. by case: ltP. Qed.
Lemma maxEgt x y : max x y = if x > y then x else y. Proof. by case: ltP. Qed.
Lemma minEge x y : min x y = if x >= y then y else x. Proof. by case: leP. Qed.
Lemma maxEge x y : max x y = if x >= y then x else y. Proof. by case: leP. Qed.

Lemma minC : commutative (min : T -> T -> T).
Proof. by move=> x y; apply: comparable_minC. Qed.

Lemma maxC : commutative (max : T -> T -> T).
Proof. by move=> x y; apply: comparable_maxC. Qed.

Lemma minA : associative (min : T -> T -> T).
Proof. by move=> x y z; apply: comparable_minA. Qed.

Lemma maxA : associative (max : T -> T -> T).
Proof. by move=> x y z; apply: comparable_maxA. Qed.

Lemma minAC : right_commutative (min : T -> T -> T).
Proof. by move=> x y z; apply: comparable_minAC. Qed.

Lemma maxAC : right_commutative (max : T -> T -> T).
Proof. by move=> x y z; apply: comparable_maxAC. Qed.

Lemma minCA : left_commutative (min : T -> T -> T).
Proof. by move=> x y z; apply: comparable_minCA. Qed.

Lemma maxCA : left_commutative (max : T -> T -> T).
Proof. by move=> x y z; apply: comparable_maxCA. Qed.

Lemma minACA : interchange (min : T -> T -> T) min.
Proof. by move=> x y z t; apply: comparable_minACA. Qed.

Lemma maxACA : interchange (max : T -> T -> T) max.
Proof. by move=> x y z t; apply: comparable_maxACA. Qed.

Lemma eq_minr x y : (min x y == y) = (y <= x).
Proof. exact: comparable_eq_minr. Qed.

Lemma eq_maxl x y : (max x y == x) = (y <= x).
Proof. exact: comparable_eq_maxl. Qed.

Lemma min_idPr x y : reflect (min x y = y) (y <= x).
Proof. exact: comparable_min_idPr. Qed.

Lemma max_idPl x y : reflect (max x y = x) (y <= x).
Proof. exact: comparable_max_idPl. Qed.

Lemma le_min z x y : (z <= min x y) = (z <= x) && (z <= y).
Proof. exact: comparable_le_min. Qed.

Lemma ge_min z x y : (min x y <= z) = (x <= z) || (y <= z).
Proof. exact: comparable_ge_min. Qed.

Lemma lt_min z x y : (z < min x y) = (z < x) && (z < y).
Proof. exact: comparable_lt_min. Qed.

Lemma gt_min z x y : (min x y < z) = (x < z) || (y < z).
Proof. exact: comparable_gt_min. Qed.

Lemma le_max z x y : (z <= max x y) = (z <= x) || (z <= y).
Proof. exact: comparable_le_max. Qed.

Lemma ge_max z x y : (max x y <= z) = (x <= z) && (y <= z).
Proof. exact: comparable_ge_max. Qed.

Lemma lt_max z x y : (z < max x y) = (z < x) || (z < y).
Proof. exact: comparable_lt_max. Qed.

Lemma gt_max z x y : (max x y < z) = (x < z) && (y < z).
Proof. exact: comparable_gt_max. Qed.

Lemma minxK x y : max (min x y) y = y. Proof. exact: comparable_minxK. Qed.
Lemma minKx x y : max x (min x y) = x. Proof. exact: comparable_minKx. Qed.
Lemma maxxK x y : min (max x y) y = y. Proof. exact: comparable_maxxK. Qed.
Lemma maxKx x y : min x (max x y) = x. Proof. exact: comparable_maxKx. Qed.

Lemma max_minl : left_distributive (max : T -> T -> T) min.
Proof. by move=> x y z; apply: comparable_max_minl. Qed.

Lemma min_maxl : left_distributive (min : T -> T -> T) max.
Proof. by move=> x y z; apply: comparable_min_maxl. Qed.

Lemma max_minr : right_distributive (max : T -> T -> T) min.
Proof. by move=> x y z; apply: comparable_max_minr. Qed.

Lemma min_maxr : right_distributive (min : T -> T -> T) max.
Proof. by move=> x y z; apply: comparable_min_maxr. Qed.

HB.instance Definition _ := SemiGroup.isComLaw.Build T max maxA maxC.
HB.instance Definition _ := SemiGroup.isComLaw.Build T min minA minC.

Lemma leIx x y z : (meet y z <= x) = (y <= x) || (z <= x).
Proof. by rewrite meetEtotal ge_min. Qed.

Lemma lexU x y z : (x <= join y z) = (x <= y) || (x <= z).
Proof. by rewrite joinEtotal le_max. Qed.

Lemma ltxI x y z : (x < meet y z) = (x < y) && (x < z).
Proof. by rewrite !ltNge leIx negb_or. Qed.

Lemma ltIx x y z : (meet y z < x) = (y < x) || (z < x).
Proof. by rewrite !ltNge lexI negb_and. Qed.

Lemma ltxU x y z : (x < join y z) = (x < y) || (x < z).
Proof. by rewrite !ltNge leUx negb_and. Qed.

Lemma ltUx x y z : (join y z < x) = (y < x) && (z < x).
Proof. by rewrite !ltNge lexU negb_or. Qed.

Definition ltexI := (@lexI _ T, ltxI).
Definition lteIx := (leIx, ltIx).
Definition ltexU := (lexU, ltxU).
Definition lteUx := (@leUx _ T, ltUx).

Lemma le_min2 x y z t : x <= z -> y <= t -> Order.min x y <= Order.min z t.
Proof. exact: comparable_le_min2. Qed.

Lemma le_max2 x y z t : x <= z -> y <= t -> Order.max x y <= Order.max z t.
Proof. exact: comparable_le_max2. Qed.

(* lteif *)

Lemma lteifNE x y C : (x < y ?<= if ~~ C) = ~~ (y < x ?<= if C).
Proof. by case: C => /=; case: leP. Qed.

Lemma lteif_minr z x y C :
  (z < min x y ?<= if C) = (z < x ?<= if C) && (z < y ?<= if C).
Proof. by case: C; rewrite /= (le_min, lt_min). Qed.

Lemma lteif_minl z x y C :
  (min x y < z ?<= if C) = (x < z ?<= if C) || (y < z ?<= if C).
Proof. by case: C; rewrite /= (ge_min, gt_min). Qed.

Lemma lteif_maxr z x y C :
  (z < max x y ?<= if C) = (z < x ?<= if C) || (z < y ?<= if C).
Proof. by case: C; rewrite /= (le_max, lt_max). Qed.

Lemma lteif_maxl z x y C :
  (max x y < z ?<= if C) = (x < z ?<= if C) && (y < z ?<= if C).
Proof. by case: C; rewrite /= (ge_max, gt_max). Qed.

Section ArgExtremum.
Context (I : finType) (i0 : I) (P : {pred I}) (F : I -> T) (Pi0 : P i0).

Lemma arg_minP: extremum_spec <=%O P F (arg_min i0 P F).
Proof. by apply: extremumP => //; apply: le_trans. Qed.

Lemma arg_maxP: extremum_spec >=%O P F (arg_max i0 P F).
Proof. by apply: extremumP => //; [apply: ge_refl | apply: ge_trans]. Qed.

End ArgExtremum.

Lemma count_le_gt x s : count (<= x) s = size s - count (> x) s.
Proof.
by rewrite -(count_predC (> x)) addKn; apply: eq_count => y; rewrite /= leNgt.
Qed.

Lemma count_lt_ge x s : count (< x) s = size s - count (>= x) s.
Proof.
by rewrite -(count_predC (>= x)) addKn; apply: eq_count => y; rewrite /= ltNge.
Qed.

Section bigminmax_Type.
Context (I : Type) (r : seq I) (x : T).
Implicit Types (P : pred I) (F : I -> T).

Lemma bigmin_mkcond P F : \big[min/x]_(i <- r | P i) F i =
  \big[min/x]_(i <- r) (if P i then F i else x).
Proof. by rewrite big_mkcond_idem //= minxx. Qed.

Lemma bigmax_mkcond P F :
  \big[max/x]_(i <- r | P i) F i = \big[max/x]_(i <- r) if P i then F i else x.
Proof. by rewrite big_mkcond_idem //= maxxx. Qed.

Lemma bigmin_mkcondl P Q F :
  \big[min/x]_(i <- r | P i && Q i) F i
  = \big[min/x]_(i <- r | Q i) if P i then F i else x.
Proof.
rewrite bigmin_mkcond [RHS]bigmin_mkcond.
by apply: eq_bigr => i _; case: P; case: Q.
Qed.

Lemma bigmin_mkcondr P Q F :
  \big[min/x]_(i <- r | P i && Q i) F i
  = \big[min/x]_(i <- r | P i) if Q i then F i else x.
Proof. by under eq_bigl do rewrite andbC; apply: bigmin_mkcondl. Qed.

Lemma bigmax_mkcondl P Q F :
  \big[max/x]_(i <- r | P i && Q i) F i
  = \big[max/x]_(i <- r | Q i) if P i then F i else x.
Proof.
rewrite bigmax_mkcond [RHS]bigmax_mkcond.
by apply: eq_bigr => i _; case: P; case: Q.
Qed.

Lemma bigmax_mkcondr P Q F :
  \big[max/x]_(i <- r | P i && Q i) F i
  = \big[max/x]_(i <- r | P i) if Q i then F i else x.
Proof. by under eq_bigl do rewrite andbC; apply: bigmax_mkcondl. Qed.

Lemma bigmin_split P F1 F2 :
  \big[min/x]_(i <- r | P i) (min (F1 i) (F2 i)) =
    min (\big[min/x]_(i <- r | P i) F1 i) (\big[min/x]_(i <- r | P i) F2 i).
Proof. by rewrite big_split_idem //= minxx. Qed.

Lemma bigmax_split P F1 F2 :
  \big[max/x]_(i <- r | P i) (max (F1 i) (F2 i)) =
    max (\big[max/x]_(i <- r | P i) F1 i) (\big[max/x]_(i <- r | P i) F2 i).
Proof. by rewrite big_split_idem //= maxxx. Qed.

Lemma bigmin_idl P F :
  \big[min/x]_(i <- r | P i) F i = min x (\big[min/x]_(i <- r | P i) F i).
Proof. by rewrite minC big_id_idem //= minxx. Qed.

Lemma bigmax_idl P F :
  \big[max/x]_(i <- r | P i) F i = max x (\big[max/x]_(i <- r | P i) F i).
Proof. by rewrite maxC big_id_idem //= maxxx. Qed.

Lemma bigmin_idr P F :
  \big[min/x]_(i <- r | P i) F i = min (\big[min/x]_(i <- r | P i) F i) x.
Proof. by rewrite [LHS]bigmin_idl minC. Qed.

Lemma bigmax_idr P F :
  \big[max/x]_(i <- r | P i) F i = max (\big[max/x]_(i <- r | P i) F i) x.
Proof. by rewrite [LHS]bigmax_idl maxC. Qed.

Lemma bigminID a P F : \big[min/x]_(i <- r | P i) F i =
  min (\big[min/x]_(i <- r | P i && a i) F i)
      (\big[min/x]_(i <- r | P i && ~~ a i) F i).
Proof. by rewrite (bigID_idem _ _ a) //= minxx. Qed.

Lemma bigmaxID a P F : \big[max/x]_(i <- r | P i) F i =
  max (\big[max/x]_(i <- r | P i && a i) F i)
      (\big[max/x]_(i <- r | P i && ~~ a i) F i).
Proof. by rewrite (bigID_idem _ _ a) //= maxxx. Qed.

End bigminmax_Type.

Let ge_min_id (x y : T) : x >= min x y. Proof. by rewrite ge_min lexx. Qed.
Let le_max_id (x y : T) : x <= max x y. Proof. by rewrite le_max lexx. Qed.

Lemma sub_bigmin [x0] I r (P P' : {pred I}) (F : I -> T) :
    (forall i, P' i -> P i) ->
  \big[min/x0]_(i <- r | P i) F i <= \big[min/x0]_(i <- r | P' i) F i.
Proof. exact: (sub_le_big ge_refl). Qed.

Lemma sub_bigmax [x0] I r (P P' : {pred I}) (F : I -> T) :
    (forall i, P i -> P' i) ->
  \big[max/x0]_(i <- r | P i) F i <= \big[max/x0]_(i <- r | P' i) F i.
Proof. exact: sub_le_big. Qed.

Lemma sub_bigmin_seq [x0] (I : eqType) r r' P (F : I -> T) : {subset r' <= r} ->
  \big[min/x0]_(i <- r | P i) F i <= \big[min/x0]_(i <- r' | P i) F i.
Proof. exact: (idem_sub_le_big ge_refl _ minxx). Qed.

Lemma sub_bigmax_seq [x0] (I : eqType) r r' P (F : I -> T) : {subset r <= r'} ->
  \big[max/x0]_(i <- r | P i) F i <= \big[max/x0]_(i <- r' | P i) F i.
Proof. exact: (idem_sub_le_big _ _ maxxx). Qed.

Lemma sub_bigmin_cond [x0] (I : eqType) r r' P P' (F : I -> T) :
    {subset [seq i <- r | P i] <= [seq i <- r' | P' i]} ->
  \big[min/x0]_(i <- r' | P' i) F i <= \big[min/x0]_(i <- r | P i) F i.
Proof. exact: (idem_sub_le_big_cond ge_refl _ minxx). Qed.

Lemma sub_bigmax_cond [x0] (I : eqType) r r' P P' (F : I -> T) :
    {subset [seq i <- r | P i] <= [seq i <- r' | P' i]} ->
  \big[max/x0]_(i <- r | P i) F i <= \big[max/x0]_(i <- r' | P' i) F i.
Proof. exact: (idem_sub_le_big_cond _ _ maxxx). Qed.

Lemma sub_in_bigmin [x0] [I : eqType] (r : seq I) (P P' : {pred I}) F :
    {in r, forall i, P' i -> P i} ->
  \big[min/x0]_(i <- r | P i) F i <= \big[min/x0]_(i <- r | P' i) F i.
Proof. exact: (sub_in_le_big ge_refl). Qed.

Lemma sub_in_bigmax [x0] [I : eqType] (r : seq I) (P P' : {pred I}) F :
    {in r, forall i, P i -> P' i} ->
  \big[max/x0]_(i <- r | P i) F i <= \big[max/x0]_(i <- r | P' i) F i.
Proof. exact: sub_in_le_big. Qed.

Lemma le_bigmin_nat [x0] n m n' m' P (F : nat -> T) :
    (n <= n')%N -> (m' <= m)%N ->
  \big[min/x0]_(n <= i < m | P i) F i <= \big[min/x0]_(n' <= i < m' | P i) F i.
Proof. exact: (le_big_nat ge_refl). Qed.

Lemma le_bigmax_nat [x0] n m n' m' P (F : nat -> T) :
    (n' <= n)%N -> (m <= m')%N ->
  \big[max/x0]_(n <= i < m | P i) F i <= \big[max/x0]_(n' <= i < m' | P i) F i.
Proof. exact: le_big_nat. Qed.

Lemma le_bigmin_nat_cond [x0] n m n' m' (P P' : pred nat) (F : nat -> T) :
    (n <= n')%N -> (m' <= m)%N -> (forall i, (n' <= i < m')%N -> P' i -> P i) ->
  \big[min/x0]_(n <= i < m | P i) F i <= \big[min/x0]_(n' <= i < m' | P' i) F i.
Proof. exact: (le_big_nat_cond ge_refl). Qed.

Lemma le_bigmax_nat_cond [x0] n m n' m' (P P' : {pred nat}) (F : nat -> T) :
    (n' <= n)%N -> (m <= m')%N -> (forall i, (n <= i < m)%N -> P i -> P' i) ->
  \big[max/x0]_(n <= i < m | P i) F i <= \big[max/x0]_(n' <= i < m' | P' i) F i.
Proof. exact: le_big_nat_cond. Qed.

Lemma le_bigmin_ord [x0] n m (P : pred nat) (F : nat -> T) : (m <= n)%N ->
  \big[min/x0]_(i < n | P i) F i <= \big[min/x0]_(i < m | P i) F i.
Proof. exact: (le_big_ord ge_refl). Qed.

Lemma le_bigmax_ord [x0] n m (P : {pred nat}) (F : nat -> T) : (n <= m)%N ->
  \big[max/x0]_(i < n | P i) F i <= \big[max/x0]_(i < m | P i) F i.
Proof. exact: le_big_ord. Qed.

Lemma le_bigmin_ord_cond [x0] n m (P P' : pred nat) (F : nat -> T) :
    (m <= n)%N -> (forall i : 'I_m, P' i -> P i) ->
  \big[min/x0]_(i < n | P i) F i <= \big[min/x0]_(i < m | P' i) F i.
Proof. exact: (le_big_ord_cond ge_refl). Qed.

Lemma le_bigmax_ord_cond [x0] n m (P P' : {pred nat}) (F : nat -> T) :
    (n <= m)%N -> (forall i : 'I_n, P i -> P' i) ->
  \big[max/x0]_(i < n | P i) F i <= \big[max/x0]_(i < m | P' i) F i.
Proof. exact: le_big_ord_cond. Qed.

Lemma subset_bigmin [x0] [I : finType] [A A' P : {pred I}] (F : I -> T) :
    A' \subset A ->
  \big[min/x0]_(i in A | P i) F i <= \big[min/x0]_(i in A' | P i) F i.
Proof. exact: (subset_le_big ge_refl). Qed.

Lemma subset_bigmax [x0] [I : finType] (A A' P : {pred I}) (F : I -> T) :
    A \subset A' ->
  \big[max/x0]_(i in A | P i) F i <= \big[max/x0]_(i in A' | P i) F i.
Proof. exact: subset_le_big. Qed.

Lemma subset_bigmin_cond [x0] (I : finType) (A A' P P' : {pred I}) (F : I -> T) :
    [set i in A' | P' i]  \subset [set i in A | P i] ->
  \big[min/x0]_(i in A | P i) F i <= \big[min/x0]_(i in A' | P' i) F i.
Proof. exact: (subset_le_big_cond ge_refl). Qed.

Lemma subset_bigmax_cond [x0] (I : finType) (A A' P P' : {pred I}) (F : I -> T) :
    [set i in A | P i]  \subset [set i in A' | P' i] ->
  \big[max/x0]_(i in A | P i) F i <= \big[max/x0]_(i in A' | P' i) F i.
Proof. exact: subset_le_big_cond. Qed.

Section bigminmax_Type.
Context (I : Type) (r : seq I) (x : T).
Implicit Types (P : pred I) (F : I -> T).

Lemma bigmin_le_id P F : \big[min/x]_(i <- r | P i) F i <= x.
Proof. by rewrite bigmin_idl. Qed.

Lemma bigmax_ge_id P F : \big[max/x]_(i <- r | P i) F i >= x.
Proof. by rewrite bigmax_idl. Qed.

Lemma bigmin_eq_id P F :
  (forall i, P i -> x <= F i) -> \big[min/x]_(i <- r | P i) F i = x.
Proof. by move=> x_le; apply: le_anti; rewrite bigmin_le_id le_bigmin. Qed.

Lemma bigmax_eq_id P F :
  (forall i, P i -> x >= F i) -> \big[max/x]_(i <- r | P i) F i = x.
Proof. by move=> x_ge; apply: le_anti; rewrite bigmax_ge_id bigmax_le. Qed.

End bigminmax_Type.

Section bigminmax_eqType.
Context (I : eqType) (r : seq I) (x : T).
Implicit Types (P : pred I) (F : I -> T).

Lemma ge_bigmin_seq i0 P F :
  i0 \in r -> P i0 -> \big[min/x]_(i <- r | P i) F i <= F i0.
Proof.
move=> + Pi0; elim: r => // h t ih; rewrite inE big_cons.
move=> /predU1P[<-|i0t]; first by rewrite Pi0 ge_min// lexx.
by case: ifPn => Ph; [rewrite ge_min ih// orbT|rewrite ih].
Qed.

Lemma le_bigmax_seq i0 P F :
  i0 \in r -> P i0 -> F i0 <= \big[max/x]_(i <- r | P i) F i.
Proof.
move=> + Pi0; elim: r => // h t ih; rewrite inE big_cons.
move=> /predU1P[<-|i0t]; first by rewrite Pi0 le_max// lexx.
by case: ifPn => Ph; [rewrite le_max ih// orbT|rewrite ih].
Qed.

Lemma bigmin_inf_seq i0 P t F :
  i0 \in r -> P i0 -> F i0 <= t -> \big[min/x]_(i <- r | P i) F i <= t.
Proof. by move=> ? ? ?; exact: le_trans (@ge_bigmin_seq i0 _ _ _ _) _. Qed.

Lemma bigmax_sup_seq i0 P t F :
  i0 \in r -> P i0 -> t <= F i0 -> t <= \big[max/x]_(i <- r | P i) F i.
Proof. by move=> ? ? ?; exact: le_trans (@le_bigmax_seq i0 _ _ _ _). Qed.

End bigminmax_eqType.

Section bigminmax_finType.
Context (I : finType) (x : T).
Implicit Types (P : pred I) (F : I -> T).

Lemma bigminD1 j P F : P j ->
  \big[min/x]_(i | P i) F i = min (F j) (\big[min/x]_(i | P i && (i != j)) F i).
Proof. by move/(bigD1 _) ->. Qed.

Lemma bigmaxD1 j P F : P j ->
  \big[max/x]_(i | P i) F i = max (F j) (\big[max/x]_(i | P i && (i != j)) F i).
Proof. by move/(bigD1 _) ->. Qed.

Lemma bigmin_le_cond j P F : P j -> \big[min/x]_(i | P i) F i <= F j.
Proof.
have := mem_index_enum j; rewrite unlock; elim: (index_enum I) => //= i l ih.
rewrite inE => /orP [/eqP-> ->|/ih leminlfi Pi]; first by rewrite ge_min lexx.
by case: ifPn => Pj; [rewrite ge_min leminlfi// orbC|exact: leminlfi].
Qed.

Lemma le_bigmax_cond j P F : P j -> F j <= \big[max/x]_(i | P i) F i.
Proof. by move=> Pj; rewrite (bigmaxD1 _ Pj) le_max lexx. Qed.

Lemma bigmin_le j F : \big[min/x]_i F i <= F j.
Proof. exact: bigmin_le_cond. Qed.

Lemma le_bigmax F j : F j <= \big[max/x]_i F i.
Proof. exact: le_bigmax_cond. Qed.

Lemma bigmin_inf j P m F : P j -> F j <= m -> \big[min/x]_(i | P i) F i <= m.
Proof. by move=> Pj ?; apply: le_trans (bigmin_le_cond _ Pj) _. Qed.

(* NB: as of [2022-08-02], bigop.bigmax_sup already exists for nat *)
Lemma bigmax_sup j P m F : P j -> m <= F j -> m <= \big[max/x]_(i | P i) F i.
Proof. by move=> Pj ?; apply: le_trans (le_bigmax_cond _ Pj). Qed.

Lemma bigmin_geP m P F :
  reflect (m <= x /\ forall i, P i -> m <= F i)
          (m <= \big[min/x]_(i | P i) F i).
Proof.
apply: (iffP idP) => [lemFi|[lemx lemPi]]; [split|exact: le_bigmin].
- by rewrite (le_trans lemFi)// bigmin_idl ge_min lexx.
- by move=> i Pi; rewrite (le_trans lemFi)// (bigminD1 _ Pi)// le_minl lexx.
Qed.

Lemma bigmax_leP m P F :
  reflect (x <= m /\ forall i, P i -> F i <= m)
          (\big[max/x]_(i | P i) F i <= m).
Proof.
apply: (iffP idP) => [|[? ?]]; last exact: bigmax_le.
rewrite bigmax_idl ge_max => /andP[-> leFm]; split=> // i Pi.
by apply: le_trans leFm; exact: le_bigmax_cond.
Qed.

Lemma bigmin_gtP m P F :
  reflect (m < x /\ forall i, P i -> m < F i) (m < \big[min/x]_(i | P i) F i).
Proof.
apply: (iffP idP) => [lemFi|[lemx lemPi]]; [split|exact: lt_bigmin].
- by rewrite (lt_le_trans lemFi)// bigmin_idl ge_min lexx.
- by move=> i Pi; rewrite (lt_le_trans lemFi)// (bigminD1 _ Pi)// le_minl lexx.
Qed.

Lemma bigmax_ltP m P F :
  reflect (x < m /\ forall i, P i -> F i < m) (\big[max/x]_(i | P i) F i < m).
Proof.
apply: (iffP idP) => [|[? ?]]; last exact: bigmax_lt.
rewrite bigmax_idl gt_max => /andP[-> ltFm]; split=> // i Pi.
by apply: le_lt_trans ltFm; exact: le_bigmax_cond.
Qed.

Lemma bigmin_eq_arg j P F : P j -> (forall i, P i -> F i <= x) ->
  \big[min/x]_(i | P i) F i = F [arg min_(i < j | P i) F i].
Proof.
move=> Pi0; case: arg_minP => //= i Pi PF PFx.
apply/eqP; rewrite eq_le bigmin_le_cond //=.
by apply/bigmin_geP; split => //; exact: PFx.
Qed.

Lemma bigmax_eq_arg j P F : P j -> (forall i, P i -> x <= F i) ->
  \big[max/x]_(i | P i) F i = F [arg max_(i > j | P i) F i].
Proof.
move=> Pi0; case: arg_maxP => //= i Pi PF PxF.
apply/eqP; rewrite eq_le le_bigmax_cond // andbT.
by apply/bigmax_leP; split => //; exact: PxF.
Qed.

Lemma eq_bigmin j P F : P j -> (forall i, P i -> F i <= x) ->
  {i0 | i0 \in P & \big[min/x]_(i | P i) F i = F i0}.
Proof.
by move=> Pi0 Hx; rewrite (bigmin_eq_arg Pi0) //; eexists=> //; case: arg_minP.
Qed.

Lemma eq_bigmax j P F : P j -> (forall i, P i -> x <= F i) ->
  {i0 | i0 \in P & \big[max/x]_(i | P i) F i = F i0}.
Proof.
by move=> Pi0 Hx; rewrite (bigmax_eq_arg Pi0) //; eexists=> //; case: arg_maxP.
Qed.

Lemma le_bigmin2 P F1 F2 : (forall i, P i -> F1 i <= F2 i) ->
  \big[min/x]_(i | P i) F1 i <= \big[min/x]_(i | P i) F2 i.
Proof.
move=> FG; elim/big_ind2 : _ => // a b e f ba fe.
rewrite ge_min 2!le_min ba fe /= andbT.
move: (le_total a e) => /orP[/(le_trans ba)-> // | /(le_trans fe)->].
by rewrite orbT.
Qed.

Lemma le_bigmax2 P F1 F2 : (forall i, P i -> F1 i <= F2 i) ->
  \big[max/x]_(i | P i) F1 i <= \big[max/x]_(i | P i) F2 i.
Proof.
move=> FG; elim/big_ind2 : _ => // a b e f ba fe.
rewrite le_max 2!ge_max ba fe /= andbT; have [//|/= af] := leP f a.
by rewrite (le_trans ba) // (le_trans _ fe) // ltW.
Qed.

Lemma bigmaxUl (A B : {set I}) F :
  \big[max/x]_(i in A) F i <= \big[max/x]_(i in A :|: B) F i.
Proof. by apply: sub_bigmax => t; rewrite in_setU => ->. Qed.

Lemma bigmaxUr (A B : {set I}) F :
  \big[max/x]_(i in B) F i <= \big[max/x]_(i in A :|: B) F i.
Proof. by under [leRHS]eq_bigl do rewrite setUC; apply: bigmaxUl. Qed.

Lemma bigminUl (A B : {set I}) F :
  \big[min/x]_(i in A) F i >= \big[min/x]_(i in A :|: B) F i.
Proof. by apply: sub_bigmin => t; rewrite in_setU => ->. Qed.

Lemma bigminUr (A B : {set I}) F :
  \big[min/x]_(i in B) F i >= \big[min/x]_(i in A :|: B) F i.
Proof. by under [leLHS]eq_bigl do rewrite setUC; apply: bigminUl. Qed.

Lemma bigmaxIl (A B : {set I}) F :
  \big[max/x]_(i in A) F i >= \big[max/x]_(i in A :&: B) F i.
Proof. by apply: sub_bigmax => t; rewrite in_setI => /andP[-> _]. Qed.

Lemma bigmaxIr (A B : {set I}) F :
  \big[max/x]_(i in B) F i >= \big[max/x]_(i in A :&: B) F i.
Proof. by under eq_bigl do rewrite setIC; apply: bigmaxIl. Qed.

Lemma bigminIl (A B : {set I}) F :
  \big[min/x]_(i in A) F i <= \big[min/x]_(i in A :&: B) F i.
Proof. by apply: sub_bigmin => t; rewrite in_setI => /andP[->_]. Qed.

Lemma bigminIr (A B : {set I}) F :
  \big[min/x]_(i in B) F i <= \big[min/x]_(i in A :&: B) F i.
Proof. by under [leRHS]eq_bigl do rewrite setIC; apply: bigminIl. Qed.

Lemma bigmaxD (A B : {set I}) F :
  \big[max/x]_(i in B) F i >= \big[max/x]_(i in B :\: A) F i.
Proof. by apply: sub_bigmax => t; rewrite in_setD => /andP[_->]. Qed.

Lemma bigminD (A B : {set I}) F :
  \big[min/x]_(i in B) F i <= \big[min/x]_(i in B :\: A) F i.
Proof. by apply: sub_bigmin => t; rewrite in_setD => /andP[_->]. Qed.

Lemma bigmaxU (A B : {set I}) F :
  \big[max/x]_(i in A :|: B) F i
  = max (\big[max/x]_(i in A) F i) (\big[max/x]_(i in B) F i).
Proof.
apply: le_anti; rewrite ge_max bigmaxUl bigmaxUr !andbT; apply/bigmax_leP.
split=> [|i /[!in_setU]/orP[iA|iB]]; first by rewrite le_max bigmax_ge_id.
- by rewrite le_max le_bigmax_cond.
- by rewrite le_max orbC le_bigmax_cond.
Qed.

Lemma bigminU (A B : {set I}) F :
  \big[min/x]_(i in A :|: B) F i
  = min (\big[min/x]_(i in A) F i) (\big[min/x]_(i in B) F i).
Proof.
apply: le_anti; rewrite le_min bigminUl bigminUr !andbT; apply/bigmin_geP.
split=> [|i /[!in_setU]/orP[iA|iB]]; first by rewrite ge_min bigmin_le_id.
- by rewrite ge_min bigmin_le_cond.
- by rewrite ge_min orbC bigmin_le_cond.
Qed.

Lemma bigmin_set1 j F : \big[min/x]_(i in [set j]) F i = min (F j) x.
Proof. exact: big_set1E. Qed.

Lemma bigmax_set1 j F : \big[max/x]_(i in [set j]) F i = max (F j) x.
Proof. exact: big_set1E. Qed.

End bigminmax_finType.

Lemma bigmin_imset [I J : finType] x [h : I -> J] [A : {set I}] (F : J -> T) :
  \big[min/x]_(j in [set h x | x in A]) F j = \big[min/x]_(i in A) F (h i).
Proof. by apply: big_imset_idem; apply: minxx. Qed.

Lemma bigmax_imset [I J : finType] x [h : I -> J] [A : {set I}] (F : J -> T) :
  \big[max/x]_(j in [set h x | x in A]) F j = \big[max/x]_(i in A) F (h i).
Proof. by apply: big_imset_idem; apply: maxxx. Qed.

End TotalTheory.

#[global] Hint Resolve le_total : core.
#[global] Hint Resolve ge_total : core.
#[global] Hint Extern 0 (is_true (_ >=< _)%O) => solve [apply: comparableT]
  : core.
#[global] Hint Resolve sort_le_sorted : core.

Arguments min_idPr {disp T x y}.
Arguments max_idPl {disp T x y}.
Arguments bigmin_mkcond {disp T I r}.
Arguments bigmax_mkcond {disp T I r}.
Arguments bigminID {disp T I r}.
Arguments bigmaxID {disp T I r}.
Arguments bigminD1 {disp T I x} j.
Arguments bigmaxD1 {disp T I x} j.
Arguments bigmin_inf {disp T I x} j.
Arguments bigmax_sup {disp T I x} j.
Arguments bigmin_eq_arg {disp T I} x j.
Arguments bigmax_eq_arg {disp T I} x j.
Arguments eq_bigmin {disp T I x} j.
Arguments eq_bigmax {disp T I x} j.
Arguments ge_bigmin_seq {disp T I r} x i0 P.
Arguments le_bigmax_seq {disp T I r} x i0 P.
Arguments bigmin_inf_seq {disp T I r} x i0 P.
Arguments bigmax_sup_seq {disp T I r} x i0 P.

(* FIXME: some lemmas in the following section should hold for any porderType *)
Module Import DualTotalTheory.
Section DualTotalTheory.
Context {disp : disp_t} {T : orderType disp}.
Implicit Type s : seq T.

Lemma sorted_filter_gt x s :
  sorted <=%O s -> [seq y <- s | x < y] = drop (count (<= x) s) s.
Proof.
move=> s_sorted; rewrite count_le_gt -[LHS]revK -filter_rev.
rewrite (@sorted_filter_lt _ T^d); last by rewrite take_rev revK count_rev.
by rewrite rev_sorted.
Qed.

Lemma sorted_filter_ge x s :
  sorted <=%O s -> [seq y <- s | x <= y] = drop (count (< x) s) s.
Proof.
move=> s_sorted; rewrite count_lt_ge -[LHS]revK -filter_rev.
rewrite (@sorted_filter_le _ T^d); last by rewrite take_rev revK count_rev.
by rewrite rev_sorted.
Qed.

Lemma nth_count_ge x x0 s i : sorted <=%O s ->
  (count (< x) s <= i < size s)%N -> x <= nth x0 s i.
Proof.
move=> ss /andP[ige ilt]; rewrite -(subnKC ige) -nth_drop -sorted_filter_ge //.
apply/(all_nthP _ (filter_all _ _)).
by rewrite size_filter ltn_subLR // count_lt_ge subnK // count_size.
Qed.

Lemma nth_count_gt x x0 s i : sorted <=%O s ->
  (count (<= x) s <= i < size s)%N -> x < nth x0 s i.
Proof.
move=> ss /andP[ige ilt]; rewrite -(subnKC ige) -nth_drop -sorted_filter_gt //.
apply/(all_nthP _ (filter_all _ _)).
by rewrite size_filter ltn_subLR // count_le_gt subnK // count_size.
Qed.

Lemma nth_count_eq x x0 s i : sorted <=%O s ->
  (count (< x) s <= i < count (<= x) s)%N -> nth x0 s i = x.
Proof.
move=> ss /andP[ige ilt]; apply/le_anti.
by rewrite nth_count_le// nth_count_ge// ige (leq_trans ilt (count_size _ _)).
Qed.

End DualTotalTheory.
End DualTotalTheory.

(* contra lemmas *)

Section ContraTheory.
Context {disp1 disp2 : disp_t} {T1 : porderType disp1} {T2 : orderType disp2}.
Implicit Types (x y : T1) (z t : T2) (b : bool) (m n : nat) (P : Prop).

Lemma contraTle b z t : (t < z -> ~~ b) -> (b -> z <= t).
Proof. exact: comparable_contraTle. Qed.

Lemma contraTlt b z t : (t <= z -> ~~ b) -> (b -> z < t).
Proof. exact: comparable_contraTlt. Qed.

Lemma contraPle P z t : (t < z -> ~ P) -> (P -> z <= t).
Proof. exact: comparable_contraPle. Qed.

Lemma contraPlt P z t : (t <= z -> ~ P) -> (P -> z < t).
Proof. exact: comparable_contraPlt. Qed.

Lemma contraNle b z t : (t < z -> b) -> (~~ b -> z <= t).
Proof. exact: comparable_contraNle. Qed.

Lemma contraNlt b z t : (t <= z -> b) -> (~~ b -> z < t).
Proof. exact: comparable_contraNlt. Qed.

Lemma contra_not_le P z t : (t < z -> P) -> (~ P -> z <= t).
Proof. exact: comparable_contra_not_le. Qed.

Lemma contra_not_lt P z t : (t <= z -> P) -> (~ P -> z < t).
Proof. exact: comparable_contra_not_lt. Qed.

Lemma contraFle b z t : (t < z -> b) -> (b = false -> z <= t).
Proof. exact: comparable_contraFle. Qed.

Lemma contraFlt b z t : (t <= z -> b) -> (b = false -> z < t).
Proof. exact: comparable_contraFlt. Qed.

Lemma contra_leq_le m n z t : (t < z -> (n < m)%N) -> ((m <= n)%N -> z <= t).
Proof. exact: comparable_contra_leq_le. Qed.

Lemma contra_leq_lt m n z t : (t <= z -> (n < m)%N) -> ((m <= n)%N -> z < t).
Proof. exact: comparable_contra_leq_lt. Qed.

Lemma contra_ltn_le m n z t : (t < z -> (n <= m)%N) -> ((m < n)%N -> z <= t).
Proof. exact: comparable_contra_ltn_le. Qed.

Lemma contra_ltn_lt m n z t : (t <= z -> (n <= m)%N) -> ((m < n)%N -> z < t).
Proof. exact: comparable_contra_ltn_lt. Qed.

Lemma contra_le x y z t : (t < z -> y < x) -> (x <= y -> z <= t).
Proof. exact: comparable_contra_le. Qed.

Lemma contra_le_lt x y z t : (t <= z -> y < x) -> (x <= y -> z < t).
Proof. exact: comparable_contra_le_lt. Qed.

Lemma contra_lt_le x y z t : (t < z -> y <= x) -> (x < y -> z <= t).
Proof. exact: comparable_contra_lt_le. Qed.

Lemma contra_lt x y z t : (t <= z -> y <= x) -> (x < y -> z < t).
Proof. exact: comparable_contra_lt. Qed.

End ContraTheory.

Section TotalMonotonyTheory.
Context {disp disp' : disp_t} {T : orderType disp} {T' : porderType disp'}.
Context (D : {pred T}) (f : T -> T').
Implicit Types (x y z : T) (u v w : T').

Let leT_anti    := @le_anti _ T.
Let leT'_anti   := @le_anti _ T'.
Let ltT_neqAle  := @lt_neqAle _ T.
Let ltT'_neqAle := @lt_neqAle _ T'.
Let ltT_def     := @lt_def _ T.
Let leT_total   := @le_total _ T.

Lemma le_mono : {homo f : x y / x < y} -> {mono f : x y / x <= y}.
Proof. exact: total_homo_mono. Qed.

Lemma le_nmono : {homo f : x y /~ x < y} -> {mono f : x y /~ x <= y}.
Proof. by apply: total_homo_mono => // x y; rewrite eq_sym. Qed.

Lemma le_mono_in :
  {in D &, {homo f : x y / x < y}} -> {in D &, {mono f : x y / x <= y}}.
Proof. exact: total_homo_mono_in. Qed.

Lemma le_nmono_in :
  {in D &, {homo f : x y /~ x < y}} -> {in D &, {mono f : x y /~ x <= y}}.
Proof. by apply: total_homo_mono_in => // x y; rewrite eq_sym. Qed.

End TotalMonotonyTheory.

End TotalTheory.

(*************)
(* FACTORIES *)
(*************)

HB.factory Record Lattice_isTotal d T & Lattice d T := {
  le_total : total (<=%O : rel T)
}.

HB.builders Context d T & Lattice_isTotal d T.

Fact meetUl : @left_distributive T T meet join.
Proof.
pose leP x y := lcomparable_leP (le_total x y); move=> x y z; apply/esym.
by case: (leP x y) (leP x z) (leP y z) => [|/ltW] xy [|/ltW] xz [|/ltW] yz;
  (apply/join_idPl || apply/join_idPr) => //; apply: le_trans xy.
Qed.

HB.instance Definition _ := Lattice_Meet_isDistrLattice.Build d T meetUl.
HB.instance Definition _ := DistrLattice_isTotal.Build d T le_total.

HB.end.

HB.factory Record POrder_isTotal d T & POrder d T := {
  le_total : total (<=%O : rel T) }.

HB.builders Context d T & POrder_isTotal d T.

Fact lexI (x y z : T) : (x <= min y z) = (x <= y) && (x <= z).
Proof. exact/comparable_le_min/le_total. Qed.
Fact leUx (x y z : T) : (max x y <= z) = (x <= z) && (y <= z).
Proof. exact/comparable_ge_max/le_total. Qed.

HB.instance Definition _ := POrder_MeetJoin_isLattice.Build d T lexI leUx.
HB.instance Definition _ := Lattice_isTotal.Build d T le_total.

HB.end.

HB.factory Record isOrder (d : disp_t) T & Choice T := {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  join : T -> T -> T;
  lt_def : forall x y, lt x y = (y != x) && le x y;
  meet_def : forall x y, meet x y = if lt x y then x else y;
  join_def : forall x y, join x y = if lt x y then y else x;
  le_anti : antisymmetric le;
  le_trans : transitive le;
  le_total : total le;
}.

HB.builders Context d T & isOrder d T.

Fact le_refl : reflexive le.
Proof. by move=> x; case: (le x x) (le_total x x). Qed.

Fact lt_le_def x y : lt x y = (le x y) && ~~ (le y x).
Proof.
rewrite lt_def andbC; case/boolP: (le x y) => //= xy.
congr negb; apply/eqP/idP => [->|yx]; first exact/le_refl.
by apply/le_anti/andP; split.
Qed.

HB.instance Definition _ := isPreorder.Build d T lt_le_def le_refl le_trans.
HB.instance Definition _ := Preorder_isPOrder.Build d T le_anti.

Section GeneratedOrder.

Local Definition T' := T.
HB.instance Definition _ := POrder.on T'.
HB.instance Definition _ := POrder_isTotal.Build d T' le_total.
Implicit Types (x y z : T').

Fact meetE x y : meet x y = x `&` y. Proof. by rewrite meet_def. Qed.
Fact joinE x y : join x y = x `|` y. Proof. by rewrite join_def. Qed.

Fact lexI x y z : (x <= meet y z) = (x <= y) && (x <= z).
Proof. by rewrite meetE lexI. Qed.
Fact leUx x y z : (join x y <= z) = (x <= z) && (y <= z).
Proof. by rewrite joinE [LHS]leUx. Qed.

End GeneratedOrder.

HB.instance Definition _ := POrder_MeetJoin_isLattice.Build d T lexI leUx.
HB.instance Definition _ := Lattice_isTotal.Build d T le_total.

HB.end.

HB.factory Record LtOrder (d : disp_t) T & Choice T := {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  join : T -> T -> T;
  le_def   : forall x y, le x y = (x == y) || lt x y;
  meet_def : forall x y, meet x y = if lt x y then x else y;
  join_def : forall x y, join x y = if lt x y then y else x;
  lt_irr   : irreflexive lt;
  lt_trans : transitive lt;
  lt_total : forall x y, x != y -> lt x y || lt y x;
}.

HB.builders Context d T & LtOrder d T.

Fact lt_def x y : lt x y = (y != x) && le x y.
Proof. by rewrite le_def; case: eqVneq => //= ->; rewrite lt_irr. Qed.

Fact meet_def_le x y : meet x y = if lt x y then x else y.
Proof. by rewrite meet_def lt_def; case: eqP. Qed.

Fact join_def_le x y : join x y = if lt x y then y else x.
Proof. by rewrite join_def lt_def; case: eqP. Qed.

Fact le_anti : antisymmetric le.
Proof.
move=> x y; rewrite !le_def; case: eqVneq => //= _ /andP [] hxy.
by move/(lt_trans hxy); rewrite lt_irr.
Qed.

Fact le_trans : transitive le.
Proof.
move=> y x z; rewrite !le_def; case: eqVneq => [->|_] //=.
by case: eqVneq => [-> ->|_ hxy /(lt_trans hxy) ->]; rewrite orbT.
Qed.

Fact le_total : total le.
Proof. by move=> x y; rewrite !le_def; case: eqVneq => //; exact: lt_total. Qed.

HB.instance Definition _ :=
  isOrder.Build d T lt_def meet_def_le join_def_le le_anti le_trans le_total.
HB.end.

HB.factory Record MonoTotal disp T & POrder disp T := {
  disp' : disp_t;
  T' : orderType disp';
  f : T -> T';
  f_mono : {mono f : x y / x <= y}
}.
HB.builders Context disp T & MonoTotal disp T.
Fact totalT : total (<=%O : rel T).
Proof. by move=> x y; rewrite -!f_mono le_total. Qed.
HB.instance Definition _ := POrder_isTotal.Build disp T totalT.
HB.end.

Section CancelTotal.
Variables (disp : disp_t) (T : choiceType).
Variables (disp' : disp_t) (T' : orderType disp') (f : T -> T').

Section PCan.

Variables (f' : T' -> option T) (f_can : pcancel f f').

#[local]
HB.instance Definition _ :=
   MonoTotal.Build disp (pcan_type f_can) (fun _ _ => erefl).

Definition PCanIsTotal : DistrLattice_isTotal _ (pcan_type f_can) :=
  Total.on (pcan_type f_can).

End PCan.

Section Can.

Variables (f' : T' -> T) (f_can : cancel f f').

#[local]
HB.instance Definition _ :=
   MonoTotal.Build disp (can_type f_can) (fun _ _ => erefl).

Definition CanIsTotal : DistrLattice_isTotal _ (can_type f_can) :=
  Total.on (can_type f_can).

End Can.
End CancelTotal.

(* subtypes *)

HB.factory Record SubLattice_isSubOrder d (T : orderType d) S d' U
    & @SubLattice d T S d' U := {}.

HB.builders Context d T S d' U & SubLattice_isSubOrder d T S d' U.
Lemma totalU : total (<=%O : rel U).
Proof. by move=> x y; rewrite -!le_val le_total. Qed.
HB.instance Definition _ := Lattice_isTotal.Build d' U totalU.
HB.end.

HB.factory Record SubPOrder_isSubOrder d (T : orderType d) S d' U
    & @SubPOrder d T S d' U := {}.

HB.builders Context d T S d' U & SubPOrder_isSubOrder d T S d' U.
Fact opredI : meet_closed S.
Proof. by move=> x y Sx Sy; rewrite meetEtotal; case: leP. Qed.
Fact opredU : join_closed S.
Proof. by move=> x y Sx Sy; rewrite joinEtotal; case: leP. Qed.
HB.instance Definition _ := SubPOrder_isSubLattice.Build d T S d' U opredI opredU.
HB.instance Definition _ := SubLattice_isSubOrder.Build d T S d' U.
HB.end.

HB.factory Record SubChoice_isSubOrder d (T : orderType d) S (d' : disp_t) U
    & @SubChoice T S U := {}.

HB.builders Context d T S d' U & SubChoice_isSubOrder d T S d' U.
HB.instance Definition _ := SubChoice_isSubPOrder.Build d T S d' U.
HB.instance Definition _ := SubPOrder_isSubOrder.Build d T S d' U.
HB.end.

Module SubOrderExports.

Notation "[ 'SubLattice_isSubOrder' 'of' U 'by' <: ]" :=
  (SubLattice_isSubOrder.Build _ _ _ _ U)
  (format "[ 'SubLattice_isSubOrder'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubLattice_isSubOrder' 'of' U 'by' <: 'with' disp ]" :=
  (SubLattice_isSubOrder.Build _ _ _ disp U)
  (format "[ 'SubLattice_isSubOrder'  'of'  U  'by'  <:  'with'  disp ]")
  : form_scope.
Notation "[ 'SubPOrder_isSubOrder' 'of' U 'by' <: ]" :=
  (SubPOrder_isSubOrder.Build _ _ _ _ U)
  (format "[ 'SubPOrder_isSubOrder'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubPOrder_isSubOrder' 'of' U 'by' <: 'with' disp ]" :=
  (SubPOrder_isSubOrder.Build _ _ _ disp U)
  (format "[ 'SubPOrder_isSubOrder'  'of'  U  'by'  <:  'with'  disp ]")
  : form_scope.
Notation "[ 'SubChoice_isSubOrder' 'of' U 'by' <: ]" :=
  (SubChoice_isSubOrder.Build _ _ _ _ U)
  (format "[ 'SubChoice_isSubOrder'  'of'  U  'by'  <: ]")
  : form_scope.
Notation "[ 'SubChoice_isSubOrder' 'of' U 'by' <: 'with' disp ]" :=
  (SubChoice_isSubOrder.Build _ _ _ disp U)
  (format "[ 'SubChoice_isSubOrder'  'of'  U  'by'  <:  'with'  disp ]")
  : form_scope.

End SubOrderExports.
HB.export SubOrderExports.

Module Theory.
Export Order.Theory.
Export TotalTheory.
End Theory.

Module Exports.
HB.reexport.
End Exports.
End Order.

Export Order.Exports.
