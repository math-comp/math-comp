(* (c) Copyright 2006-2019 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import path fintype tuple finfun bigop preorder.

(******************************************************************************)
(*                Types equipped with partial order relations                 *)
(*                                                                            *)
(* NB: See CONTRIBUTING.md for an introduction to HB concepts and commands.   *)
(*                                                                            *)
(* NB: See the header of all_order.v for general remarks about the preorder   *)
(*     and order structures in MathComp, and the files in this directory.     *)
(*                                                                            *)
(* * Interfaces                                                               *)
(* We provide the following interfaces for types equipped with an order:      *)
(*                                                                            *)
(*              porderType d == the type of partially ordered types           *)
(*                              The HB class is called POrder.                *)
(*             bPOrderType d == porderType with a bottom element (\bot)       *)
(*                              The HB class is called BPOrder.               *)
(*             tPOrderType d == porderType with a top element (\top)          *)
(*                              The HB class is called TPOrder.               *)
(*            tbPOrderType d == porderType with both a top and a bottom       *)
(*                              The HB class is called TBPOrder.              *)
(*           finPOrderType d == the type of partially ordered finite types    *)
(*                              The HB class is called FinPOrder.             *)
(*          finBPOrderType d == finPOrderType with a bottom element           *)
(*                              The HB class is called FinBPOrder.            *)
(*          finTPOrderType d == finPOrderType with a top element              *)
(*                              The HB class is called FinTPOrder.            *)
(*         finTBPOrderType d == finPOrderType with both a top and a bottom    *)
(*                              The HB class is called FinTBPOrder.           *)
(*                                                                            *)
(* and their joins with subType:                                              *)
(*                                                                            *)
(*          subPOrder d T P d' == join of porderType d' and subType           *)
(*                                (P : pred T) such that val is monotonic     *)
(*                                The HB class is called SubPOrder.           *)
(*                                                                            *)
(* The following notations are provided to build substructures:               *)
(* [SubChoice_isSubPOrder of U by <: with disp] ==                            *)
(* [SubChoice_isSubPOrder of U by <:] == porderType mixin for a subType       *)
(*                          whose base type is a porderType                   *)
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
HB.mixin Record Preorder_isDuallyPOrder (d : disp_t) T & Preorder d T := {
  le_anti  : antisymmetric (@le d T);
  ge_anti  : antisymmetric (fun x y => @le d T y x);
}.

#[short(type="porderType")]
HB.structure Definition POrder (d : disp_t) :=
  { T of Preorder d T & Preorder_isDuallyPOrder d T }.

#[short(type="bPOrderType")]
HB.structure Definition BPOrder d := { T of hasBottom d T & POrder d T }.
#[short(type="tPOrderType")]
HB.structure Definition TPOrder d := { T of hasTop d T & POrder d T }.
#[short(type="tbPOrderType")]
HB.structure Definition TBPOrder d := { T of hasTop d T & BPOrder d T }.

Module POrderExports.
Arguments le_trans {disp T} [_ _ _].
End POrderExports.
HB.export POrderExports.

(* Bind Scope order_scope with POrder.sort. *)

(**********)
(* FINITE *)
(**********)

#[short(type="finPOrderType")]
HB.structure Definition FinPOrder d := { T of Finite T & POrder d T }.

#[short(type="finBPOrderType")]
HB.structure Definition FinBPOrder d := { T of FinPOrder d T & hasBottom d T }.

#[short(type="finTPOrderType")]
HB.structure Definition FinTPOrder d := { T of FinPOrder d T & hasTop d T }.

#[short(type="finTBPOrderType")]
HB.structure Definition FinTBPOrder d := { T of FinBPOrder d T & hasTop d T }.

(************)
(* SUBTYPES *)
(************)

#[short(type="subPOrder")]
HB.structure Definition SubPOrder d (T : porderType d) S d' :=
  { U of SubEquality T S U & POrder d' U & isSubPreorder d T S d' U }.

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

HB.instance Definition _ (d : disp_t) (T : porderType d) :=
  Preorder_isDuallyPOrder.Build (dual_display d) T^d
    ge_anti le_anti.

HB.saturate.

End DualOrder.
HB.export DualOrder.

(**********)
(* THEORY *)
(**********)

Module Import POrderTheory.

(* FIXME: removing the following line breaks Gaia and CoqEAL *)
Include PreorderTheory.

Section POrderTheory.

Context {disp : disp_t} {T : porderType disp}.

Implicit Types (x y : T) (s : seq T).

Lemma le_anti: antisymmetric (<=%O : rel T).
Proof. exact: le_anti. Qed.

Lemma ge_anti: antisymmetric (>=%O : rel T).
Proof. by move=> x y /le_anti. Qed.

Lemma eq_le x y: (x == y) = (x <= y <= x).
Proof. by apply/eqP/idP => [->|/le_anti]; rewrite ?lexx. Qed.

Lemma lt_def x y : (x < y) = (y != x) && (x <= y).
Proof.
rewrite andbC lt_le_def; case/boolP: (x <= y) => //= xy.
congr negb; apply/idP/eqP => [yx|->]; last exact/lexx.
by apply/le_anti; rewrite yx.
Qed.

Lemma lt_neqAle x y: (x < y) = (x != y) && (x <= y).
Proof. by rewrite lt_def eq_sym. Qed.

Lemma le_eqVlt x y: (x <= y) = (x == y) || (x < y).
Proof. by rewrite lt_neqAle; case: eqP => //= ->; rewrite lexx. Qed.

Definition lte_anti := (=^~ eq_le, @lt_asym disp T, @lt_le_asym disp T, @le_lt_asym disp T).

Lemma eq_geP {x y} : reflect (forall z, (z <= x) = (z <= y)) (x == y).
Proof.
by apply: (iffP idP) => [/eqP->//|/[dup]] /[!eq_le] -> <-; rewrite !lexx.
Qed.

Lemma eq_leP {x y} : reflect (forall z, (x <= z) = (y <= z)) (x == y).
Proof.
by apply: (iffP idP) => [/eqP->//|/[dup]] /[!eq_le] <- ->; rewrite !lexx.
Qed.

Lemma lt_sorted_uniq_le s : sorted <%O s = uniq s && sorted <=%O s.
Proof.
rewrite le_sorted_pairwise lt_sorted_pairwise uniq_pairwise -pairwise_relI.
by apply/eq_pairwise => ? ?; rewrite lt_neqAle.
Qed.

Lemma le_sorted_eq s1 s2 :
  sorted <=%O s1 -> sorted <=%O s2 -> perm_eq s1 s2 -> s1 = s2.
Proof. exact/sorted_eq/le_anti/le_trans. Qed.

Lemma count_lt_le_mem x s : (count (< x) s < count (<= x) s)%N = (x \in s).
Proof.
have := count_predUI (pred1 x) (< x) s.
have -> : count (predI (pred1 x) (< x)) s = 0%N.
  rewrite (@eq_count _ _ pred0) ?count_pred0 // => y /=.
  by rewrite lt_neqAle; case: eqP => //= ->; rewrite eqxx.
have /eq_count-> : [predU1 x & < x] =1 (<= x) by move=> y /=; rewrite le_eqVlt.
by rewrite addn0 => ->; rewrite -add1n leq_add2r -has_count has_pred1.
Qed.

Lemma comparable_ltgtP x y : x >=< y ->
  compare x y (min y x) (min x y) (max y x) (max x y)
  (y == x) (x == y) (x >= y) (x <= y) (x > y) (x < y).
Proof.
rewrite /min /max />=<%O !le_eqVlt [y == x]eq_sym.
have := (eqVneq x y, (boolP (x < y), boolP (y < x))).
move=> [[->//|neq_xy /=] [[] xy [] //=]] ; do ?by rewrite ?ltxx; constructor.
  by rewrite ltxx in xy.
by rewrite le_gtF // ltW.
Qed.

Lemma comparable_leP x y : x >=< y ->
  le_xor_gt x y (min y x) (min x y) (max y x) (max x y) (x <= y) (y < x).
Proof. by move=> /comparable_ltgtP [?|?|->]; constructor; rewrite // ltW. Qed.

Lemma comparable_ltP x y : x >=< y ->
  lt_xor_ge x y (min y x) (min x y) (max y x) (max x y) (y <= x) (x < y).
Proof. by move=> /comparable_ltgtP [?|?|->]; constructor; rewrite // ltW. Qed.

Lemma comparableP x y : incompare x y
  (min y x) (min x y) (max y x) (max x y)
  (y == x) (x == y) (x >= y) (x <= y) (x > y) (x < y)
  (y >=< x) (x >=< y).
Proof.
rewrite ![y >=< _]comparable_sym; have [c_xy|i_xy] := boolP (x >=< y).
  by case: (comparable_ltgtP c_xy) => ?; constructor.
by rewrite /min /max ?incomparable_eqF ?incomparable_leF;
   rewrite ?incomparable_ltF// 1?comparable_sym //; constructor.
Qed.

(* leif *)

Lemma leifP x y C : reflect (x <= y ?= iff C) (if C then x == y else x < y).
Proof.
rewrite /leif le_eqVlt; apply: (iffP idP)=> [|[]].
  by case: C => [/eqP->|lxy]; rewrite ?eqxx // lxy lt_eqF.
by move=> /orP[/eqP->|lxy] <-; rewrite ?eqxx // lt_eqF.
Qed.

Lemma leif_trans x1 x2 x3 C12 C23 :
  x1 <= x2 ?= iff C12 -> x2 <= x3 ?= iff C23 -> x1 <= x3 ?= iff C12 && C23.
Proof.
move=> ltx12 ltx23; apply/leifP; rewrite -ltx12.
case eqx12: (x1 == x2).
  by rewrite (eqP eqx12) lt_neqAle !ltx23 andbT; case C23.
by rewrite (@lt_le_trans _ _ x2) ?ltx23 // lt_neqAle eqx12 ltx12.
Qed.

Lemma leif_le x y : x <= y -> x <= y ?= iff (x >= y).
Proof. by move=> lexy; split=> //; rewrite eq_le lexy. Qed.

Lemma leif_eq x y : x <= y -> x <= y ?= iff (x == y).
Proof. by []. Qed.

Lemma ge_leif x y C : x <= y ?= iff C -> (y <= x) = C.
Proof. by case=> le_xy; rewrite eq_le le_xy. Qed.

Lemma lt_leif x y C : x <= y ?= iff C -> (x < y) = ~~ C.
Proof. by move=> le_xy; rewrite lt_neqAle !le_xy andbT. Qed.

Lemma ltNleif x y C : x <= y ?= iff ~~ C -> (x < y) = C.
Proof. by move=> /lt_leif; rewrite negbK. Qed.

(* lteif *)

Lemma lteif_anti C1 C2 x y :
  (x < y ?<= if C1) && (y < x ?<= if C2) = C1 && C2 && (x == y).
Proof. by case: C1 C2 => [][]; rewrite lte_anti. Qed.

Lemma lteifN C x y : x < y ?<= if ~~ C -> ~~ (y < x ?<= if C).
Proof. by case: C => /=; case: comparableP. Qed.

(* min and max *)

Lemma minEle x y : min x y = if x <= y then x else y.
Proof. by case: comparableP. Qed.

Lemma maxEle x y : max x y = if x <= y then y else x.
Proof. by case: comparableP. Qed.

Lemma comparable_minEgt x y : x >=< y -> min x y = if x > y then y else x.
Proof. by case: comparableP. Qed.
Lemma comparable_maxEgt x y : x >=< y -> max x y = if x > y then x else y.
Proof. by case: comparableP. Qed.
Lemma comparable_minEge x y : x >=< y -> min x y = if x >= y then y else x.
Proof. by case: comparableP. Qed.
Lemma comparable_maxEge x y : x >=< y -> max x y = if x >= y then x else y.
Proof. by case: comparableP. Qed.

Lemma min_l x y : x <= y -> min x y = x. Proof. by case: comparableP. Qed.
Lemma min_r x y : y <= x -> min x y = y. Proof. by case: comparableP. Qed.
Lemma max_l x y : y <= x -> max x y = x. Proof. by case: comparableP. Qed.
Lemma max_r x y : x <= y -> max x y = y. Proof. by case: comparableP. Qed.

Lemma eq_minl x y : (min x y == x) = (x <= y).
Proof. by rewrite !(fun_if, if_arg) eqxx; case: comparableP. Qed.

Lemma eq_maxr x y : (max x y == y) = (x <= y).
Proof. by rewrite !(fun_if, if_arg) eqxx; case: comparableP. Qed.

Lemma min_idPl x y : reflect (min x y = x) (x <= y).
Proof. by rewrite -eq_minl; apply/eqP. Qed.

Lemma max_idPr x y : reflect (max x y = y) (x <= y).
Proof. by rewrite -eq_maxr; apply/eqP. Qed.

Section Comparable2.
Context (z x y : T) (cmp_xy : x >=< y).

Lemma comparable_minC : min x y = min y x.
Proof. by case: comparableP cmp_xy. Qed.

Lemma comparable_maxC : max x y = max y x.
Proof. by case: comparableP cmp_xy. Qed.

Lemma comparable_eq_minr : (min x y == y) = (y <= x).
Proof. by rewrite !(fun_if, if_arg) eqxx; case: comparableP cmp_xy. Qed.

Lemma comparable_eq_maxl : (max x y == x) = (y <= x).
Proof. by rewrite !(fun_if, if_arg) eqxx; case: comparableP cmp_xy. Qed.

Lemma comparable_min_idPr : reflect (min x y = y) (y <= x).
Proof. by rewrite -comparable_eq_minr; apply/eqP. Qed.

Lemma comparable_max_idPl : reflect (max x y = x) (y <= x).
Proof. by rewrite -comparable_eq_maxl; apply/eqP. Qed.

Lemma comparable_lteifNE C :
  x >=< y -> (x < y ?<= if ~~ C) = ~~ (y < x ?<= if C).
Proof. by case: C => /=; case: comparableP. Qed.

End Comparable2.

Section Comparable3.
Context (x y z : T) (cmp_xy : x >=< y) (cmp_xz : x >=< z) (cmp_yz : y >=< z).
Let P := comparableP.

Lemma comparable_max_minl : max (min x y) z = min (max x z) (max y z).
Proof.
move: cmp_xy cmp_xz cmp_yz; rewrite !(fun_if, if_arg)/=.
move: (P x y) (P x z) (P y z).
move=> [xy|xy|xy|<-] [xz|xz|xz|<-] [yz|yz|yz|//->]//= _; rewrite ?ltxx//.
- by have := lt_trans xy (lt_trans yz xz); rewrite ltxx.
- by have := lt_trans xy (lt_trans xz yz); rewrite ltxx.
Qed.

End Comparable3.

Section Comparable4.
Context (x y z w : T) (cmp_xy : x >=< y) (cmp_zw : z >=< w).

Lemma comparable_le_min2 : x <= z -> y <= w ->
  Order.min x y <= Order.min z w.
Proof.
move: cmp_xy cmp_zw => /comparable_leP[] xy /comparable_leP[] zw // xz yw.
- exact: le_trans xy yw.
- exact: le_trans (ltW xy) xz.
Qed.

Lemma comparable_le_max2 : x <= z -> y <= w ->
  Order.max x y <= Order.max z w.
Proof.
move: cmp_xy cmp_zw => /comparable_leP[] xy /comparable_leP[] zw // xz yw.
- exact: le_trans yw (ltW zw).
- exact: le_trans xz zw.
Qed.

End Comparable4.

Lemma comparable_minAC x y z : x >=< y -> x >=< z -> y >=< z ->
  min (min x y) z = min (min x z) y.
Proof.
move=> xy xz yz; rewrite -comparable_minA// [min y z]comparable_minC//.
by rewrite comparable_minA// 1?comparable_sym.
Qed.

Lemma comparable_maxAC x y z : x >=< y -> x >=< z -> y >=< z ->
  max (max x y) z = max (max x z) y.
Proof.
move=> xy xz yz; rewrite -comparable_maxA// [max y z]comparable_maxC//.
by rewrite comparable_maxA// 1?comparable_sym.
Qed.

Lemma comparable_minCA x y z : x >=< y -> x >=< z -> y >=< z ->
  min x (min y z) = min y (min x z).
Proof.
move=> xy xz yz; rewrite comparable_minA// [min x y]comparable_minC//.
by rewrite -comparable_minA// 1?comparable_sym.
Qed.

Lemma comparable_maxCA x y z : x >=< y -> x >=< z -> y >=< z ->
  max x (max y z) = max y (max x z).
Proof.
move=> xy xz yz; rewrite comparable_maxA// [max x y]comparable_maxC//.
by rewrite -comparable_maxA// 1?comparable_sym.
Qed.

Lemma comparable_minACA x y z t :
    x >=< y -> x >=< z -> x >=< t -> y >=< z -> y >=< t -> z >=< t ->
  min (min x y) (min z t) = min (min x z) (min y t).
Proof.
move=> xy xz xt yz yt zt; rewrite comparable_minA// ?comparable_minl//.
rewrite [min _ z]comparable_minAC// -comparable_minA// ?comparable_minl//.
by rewrite inE comparable_sym.
Qed.

Lemma comparable_maxACA x y z t :
    x >=< y -> x >=< z -> x >=< t -> y >=< z -> y >=< t -> z >=< t ->
  max (max x y) (max z t) = max (max x z) (max y t).
Proof.
move=> xy xz xt yz yt zt; rewrite comparable_maxA// ?comparable_maxl//.
rewrite [max _ z]comparable_maxAC// -comparable_maxA// ?comparable_maxl//.
by rewrite inE comparable_sym.
Qed.

Lemma comparable_min_maxr x y z : x >=< y -> x >=< z -> y >=< z ->
  min x (max y z) = max (min x y) (min x z).
Proof.
move=> xy xz yz; rewrite ![min x _]comparable_minC// ?comparable_maxr//.
by rewrite comparable_min_maxl// 1?comparable_sym.
Qed.

(* monotonicity *)

Lemma mono_in_leif (A : {pred T}) (f : T -> T) C :
   {in A &, {mono f : x y / x <= y}} ->
  {in A &, forall x y, (f x <= f y ?= iff C) = (x <= y ?= iff C)}.
Proof. by move=> mf x y Ax Ay; rewrite /leif !eq_le !mf. Qed.

Lemma mono_leif (f : T -> T) C :
    {mono f : x y / x <= y} ->
  forall x y, (f x <= f y ?= iff C) = (x <= y ?= iff C).
Proof. by move=> mf x y; rewrite /leif !eq_le !mf. Qed.

Lemma nmono_in_leif (A : {pred T}) (f : T -> T) C :
    {in A &, {mono f : x y /~ x <= y}} ->
  {in A &, forall x y, (f x <= f y ?= iff C) = (y <= x ?= iff C)}.
Proof. by move=> mf x y Ax Ay; rewrite /leif !eq_le !mf. Qed.

Lemma nmono_leif (f : T -> T) C : {mono f : x y /~ x <= y} ->
  forall x y, (f x <= f y ?= iff C) = (y <= x ?= iff C).
Proof. by move=> mf x y; rewrite /leif !eq_le !mf. Qed.

Section bigminmax.
Context (I : Type) (r : seq I) (f : I -> T) (x0 x : T) (P : pred I).

Lemma bigmax_le : x0 <= x -> (forall i, P i -> f i <= x) ->
  \big[max/x0]_(i <- r | P i) f i <= x.
Proof. by move=> ? ?; elim/big_ind: _ => // *; rewrite maxEle; case: ifPn. Qed.

Lemma le_bigmin : x <= x0 -> (forall i, P i -> x <= f i) ->
  x <= \big[min/x0]_(i <- r | P i) f i.
Proof. by move=> ? ?; elim/big_ind: _ => // *; rewrite minEle; case: ifPn. Qed.

End bigminmax.

End POrderTheory.

#[global] Hint Resolve comparable_minr comparable_minl : core.
#[global] Hint Resolve comparable_maxr comparable_maxl : core.

Section ContraTheory.
Context {disp1 disp2 : disp_t} {T1 : porderType disp1} {T2 : porderType disp2}.
Implicit Types (x y : T1) (z t : T2) (b : bool) (m n : nat) (P : Prop).

Lemma contra_leT b x y : (~~ b -> x < y) -> (y <= x -> b).
Proof. by case: comparableP; case: b. Qed.

Lemma contra_ltT b x y : (~~ b -> x <= y) -> (y < x -> b).
Proof. by case: comparableP; case: b. Qed.

Lemma contra_leN b x y : (b -> x < y) -> (y <= x -> ~~ b).
Proof. by case: comparableP; case: b. Qed.

Lemma contra_ltN b x y : (b -> x <= y) -> (y < x -> ~~ b).
Proof. by case: comparableP; case: b. Qed.

Lemma contra_le_not P x y : (P -> x < y) -> (y <= x -> ~ P).
Proof. by case: comparableP => // _ PF _ /PF. Qed.

Lemma contra_lt_not P x y : (P -> x <= y) -> (y < x -> ~ P).
Proof. by case: comparableP => // _ PF _ /PF. Qed.

Lemma contra_leF b x y : (b -> x < y) -> (y <= x -> b = false).
Proof. by case: comparableP; case: b => // _ /implyP. Qed.

Lemma contra_ltF b x y : (b -> x <= y) -> (y < x -> b = false).
Proof. by case: comparableP; case: b => // _ /implyP. Qed.

Lemma contra_le_leq x y m n : ((n < m)%N -> y < x) -> (x <= y -> (m <= n)%N).
Proof. by case: comparableP; case: ltngtP. Qed.

Lemma contra_le_ltn x y m n : ((n <= m)%N -> y < x) -> (x <= y -> (m < n)%N).
Proof. by case: comparableP; case: ltngtP. Qed.

Lemma contra_lt_leq x y m n : ((n < m)%N -> y <= x) -> (x < y -> (m <= n)%N).
Proof. by case: comparableP; case: ltngtP. Qed.

Lemma contra_lt_ltn x y m n : ((n <= m)%N -> y <= x) -> (x < y -> (m < n)%N).
Proof. by case: comparableP; case: ltngtP. Qed.

End ContraTheory.

Section POrderMonotonyTheory.
Context {disp disp' : disp_t} {T : porderType disp} {T' : porderType disp'}.
Context (D D' : {pred T}) (f : T -> T').

Let leT_anti := @le_anti _ T.
Hint Resolve lexx lt_neqAle : core.

Let ge_antiT : antisymmetric (>=%O : rel T).
Proof. by move=> ? ? /le_anti. Qed.

Lemma ltW_homo : {homo f : x y / x < y} -> {homo f : x y / x <= y}.
Proof. exact: homoW. Qed.

Lemma ltW_nhomo : {homo f : x y /~ x < y} -> {homo f : x y /~ x <= y}.
Proof. by apply: homoW=> // x y; rewrite eq_sym. Qed.

Lemma inj_homo_lt :
  injective f -> {homo f : x y / x <= y} -> {homo f : x y / x < y}.
Proof. exact: inj_homo. Qed.

Lemma inj_nhomo_lt :
  injective f -> {homo f : x y /~ x <= y} -> {homo f : x y /~ x < y}.
Proof. by apply: inj_homo=> // x y; rewrite eq_sym. Qed.

Lemma inc_inj : {mono f : x y / x <= y} -> injective f.
Proof. exact: mono_inj. Qed.

Lemma dec_inj : {mono f : x y /~ x <= y} -> injective f.
Proof. exact: mono_inj. Qed.

(* Monotony in D D' *)
Lemma ltW_homo_in :
  {in D & D', {homo f : x y / x < y}} -> {in D & D', {homo f : x y / x <= y}}.
Proof. exact: homoW_in. Qed.

Lemma ltW_nhomo_in :
  {in D & D', {homo f : x y /~ x < y}} -> {in D & D', {homo f : x y /~ x <= y}}.
Proof. by apply: homoW_in=> // x y; rewrite eq_sym. Qed.

Lemma inj_homo_lt_in :
    {in D & D', injective f} ->  {in D & D', {homo f : x y / x <= y}} ->
  {in D & D', {homo f : x y / x < y}}.
Proof. exact: inj_homo_in. Qed.

Lemma inj_nhomo_lt_in :
    {in D & D', injective f} -> {in D & D', {homo f : x y /~ x <= y}} ->
  {in D & D', {homo f : x y /~ x < y}}.
Proof. by apply: inj_homo_in=> // x y; rewrite eq_sym. Qed.

Lemma inc_inj_in : {in D &, {mono f : x y / x <= y}} ->
   {in D &, injective f}.
Proof. exact: mono_inj_in. Qed.

Lemma dec_inj_in :
  {in D &, {mono f : x y /~ x <= y}} -> {in D &, injective f}.
Proof. exact: mono_inj_in. Qed.

End POrderMonotonyTheory.

(* TODO: move to the POrderMonotonyTheory section? *)
Lemma omorph_lt (d : disp_t) (T : porderType d) (d' : disp_t) (T' : porderType d')
(f : {omorphism T -> T'}) : injective f -> {homo f : x y / x < y}.
Proof. by move/inj_homo_lt; apply; apply: omorph_le. Qed.

End POrderTheory.

Arguments leifP {disp T x y C}.
Arguments mono_in_leif [disp T A f C].
Arguments nmono_in_leif [disp T A f C].
Arguments mono_leif [disp T f C].
Arguments nmono_leif [disp T f C].
Arguments min_idPl {disp T x y}.
Arguments max_idPr {disp T x y}.
Arguments comparable_min_idPr {disp T x y _}.
Arguments comparable_max_idPl {disp T x y _}.

Module Import BPOrderTheory.

Section BPOrderTheory.
Context {disp : disp_t} {T : bPOrderType disp}.
Implicit Types (x y : T).

Lemma lex0 x : (x <= \bot) = (x == \bot).
Proof. by rewrite le_eqVlt ltx0 orbF. Qed.

Lemma lt0x x : (\bot < x) = (x != \bot).
Proof. by rewrite lt_def le0x andbT. Qed.

Variant eq0_xor_gt0 x : bool -> bool -> Set :=
    Eq0NotPOs : x = \bot -> eq0_xor_gt0 x true false
  | POsNotEq0 : \bot < x -> eq0_xor_gt0 x false true.

Lemma posxP x : eq0_xor_gt0 x (x == \bot) (\bot < x).
Proof. by rewrite lt0x; have [] := eqVneq; constructor; rewrite ?lt0x. Qed.

End BPOrderTheory.
End BPOrderTheory.

Module Import TPOrderTheory.
Section TPOrderTheory.
Context {disp : disp_t} {T : tPOrderType disp}.
Implicit Types (x y : T).

Lemma le1x x : (\top <= x) = (x == \top). Proof. exact: (@lex0 _ T^d). Qed.
Lemma ltx1 x : (x < \top) = (x != \top). Proof. exact: (@lt0x _ T^d). Qed.

End TPOrderTheory.
End TPOrderTheory.

Lemma mono_unique d (T T' : finPOrderType d) (f g : T -> T') :
    total (<=%O : rel T) -> (#|T'| <= #|T|)%N ->
    {mono f : x y / x <= y} -> {mono g : x y / x <= y} ->
  f =1 g.
Proof.
move=> le_total leT'T lef leg x0; move: {+}x0.
suff: finfun f = finfun g by move=> /ffunP + x => /(_ x); rewrite !ffunE.
apply: (can_inj fgraphK); apply/val_inj => /=; rewrite !codomE.
under eq_map do rewrite ffunE; under [RHS]eq_map do rewrite ffunE.
have [finj ginj] := (inc_inj lef, inc_inj leg).
have [f' fK f'K] := inj_card_bij finj leT'T.
have [g' gK g'K] := inj_card_bij ginj leT'T.
apply/eqP; have : [seq f i | i <- enum T] = [seq g i | i <- enum T].
  apply: (@sorted_eq _ <=%O le_trans le_anti); rewrite ?mono_sorted_enum//.
  apply: uniq_perm; rewrite ?map_inj_uniq ?enum_uniq//.
  move=> x; apply/mapP/mapP => -[y _ ->].
    by exists (g' (f y)); rewrite ?mem_enum.
  by exists (f' (g y)); rewrite ?mem_enum.
move=> /eqP; rewrite !eq_map_all all_map [in X in _ -> X]all_map.
by have /permPl/perm_all-> := perm_sort <=%O (fintype.enum T).
Qed.

(*************)
(* FACTORIES *)
(*************)

HB.factory Record Preorder_isPOrder (d : disp_t) T & Preorder d T := {
  le_anti  : antisymmetric (@le d T);
}.

HB.builders Context (d : disp_t) T & Preorder_isPOrder d T.

Let ge_anti : antisymmetric (fun x y => @le d T y x).
Proof. by move=> x y; rewrite andbC; apply: le_anti. Qed.

HB.instance Definition _ := Preorder_isDuallyPOrder.Build d T le_anti ge_anti.

HB.end.

HB.factory Record isPOrder (d : disp_t) T & Choice T := {
  le       : rel T;
  lt       : rel T;
  lt_def   : forall x y, lt x y = (y != x) && (le x y);
  le_refl  : reflexive     le;
  le_anti  : antisymmetric le;
  le_trans : transitive    le;
}.

HB.builders Context (d : disp_t) T & isPOrder d T.

Let lt_le_def x y : lt x y = le x y && ~~ le y x.
Proof.
rewrite lt_def andbC; case /boolP: (le x y) => //= xy.
have [->|/negP xyE /=] := eqVneq y x; first by rewrite le_refl.
by apply/esym/negP => yx; apply/xyE/eqP/le_anti; rewrite yx.
Qed.

HB.instance Definition _ := isPreorder.Build d T lt_le_def le_refl le_trans.
HB.instance Definition _ := Preorder_isPOrder.Build d T le_anti.

HB.end.

HB.factory Record Le_isPOrder (d : disp_t) T & Choice T := {
  le       : rel T;
  le_refl  : reflexive     le;
  le_anti  : antisymmetric le;
  le_trans : transitive    le;
}.

HB.builders Context (d : disp_t) T & Le_isPOrder d T.
(* TODO: print nice error message when keyed type is not provided *)
HB.instance Definition _ := @Le_isPreorder.Build d T le le_refl le_trans.
HB.instance Definition _ := @Preorder_isPOrder.Build d T le_anti.
HB.end.

HB.factory Record LtLe_isPOrder (d : disp_t) T & Choice T := {
  le : rel T;
  lt : rel T;
  le_def   : forall x y, le x y = (x == y) || lt x y;
  lt_irr   : irreflexive lt;
  lt_trans : transitive lt;
}.

HB.builders Context (d : disp_t) T & LtLe_isPOrder d T.

HB.instance Definition _ := @LtLe_isPreorder.Build d T le lt le_def lt_irr lt_trans.

Let le_anti : antisymmetric le.
Proof.
move=> x y; rewrite !le_def [y == _]eq_sym.
have [//|neq_xy/=] := eqVneq x y => /andP[xy yx].
by have := lt_trans xy yx; rewrite lt_irr.
Qed.

HB.instance Definition _ := @Preorder_isPOrder.Build d T le_anti.

HB.end.

HB.factory Record Lt_isPOrder (d : disp_t) T & Choice T := {
  lt       : rel T;
  lt_irr   : irreflexive lt;
  lt_trans : transitive  lt;
}.

HB.builders Context d T & Lt_isPOrder d T.
HB.instance Definition _ := @LtLe_isPOrder.Build d T
  _ lt (fun _ _ => erefl) lt_irr lt_trans.
HB.end.

HB.factory Record IsoBottom disp T & Order.POrder disp T := {
  disp' : Order.disp_t;
  T' : bPOrderType disp';
  f : T -> T';
  f' : T' -> T;
  f_can : cancel f f';
  f'_can : cancel f' f;
  f_mono : {mono f : x y / x <= y}%O;
}.

HB.builders Context disp T & IsoBottom disp T.

Definition bottom := f' \bot%O.
Lemma isobottom x : (bottom <= x)%O.
Proof. by rewrite /bottom -f_mono f'_can Order.le0x. Qed.

HB.instance Definition _ := Order.hasBottom.Build _ T isobottom.
HB.end.

HB.factory Record IsoTop disp T & Order.POrder disp T := {
  disp' : Order.disp_t;
  T' : tPOrderType disp';
  f : T -> T';
  f' : T' -> T;
  f_can : cancel f f';
  f'_can : cancel f' f;
  f_mono : {mono f : x y / x <= y}%O;
}.

HB.builders Context disp T & IsoTop disp T.

Definition top := f' \top%O.
Lemma isotop x : (x <= top)%O.
Proof. by rewrite /top -f_mono f'_can Order.lex1. Qed.

HB.instance Definition _ := Order.hasTop.Build _ T isotop.
HB.end.

Module CancelPartial.
Import PreCancelPartial.
Section CancelPartial.
Variables (disp : disp_t) (T : choiceType).
Variables (disp' : disp_t) (T' : porderType disp') (f : T -> T').

Section Pcan.
Variables (f' : T' -> option T) (f_can : pcancel f f').

Fact anti : antisymmetric (le f).
Proof. by move=> ? ? /le_anti; apply: pcan_inj. Qed.

Fact lt_def x y :
  lt f x y = (y != x) && le f x y.
Proof. by rewrite /lt lt_def (inj_eq (pcan_inj f_can)). Qed.

Definition Pcan := isPOrder.Build disp (Choice.Pack (Choice.class T))
  lt_def (@refl T disp' T' f) anti (@trans T disp' T' f).

End Pcan.

Definition Can f' (f_can : cancel f f') := Pcan (can_pcan f_can).

End CancelPartial.
End CancelPartial.

Notation PCanIsPartial := CancelPartial.Pcan.
Notation CanIsPartial := CancelPartial.Can.

#[export]
HB.instance Definition _ (disp : disp_t) (T : choiceType)
  (disp' : disp_t) (T' : porderType disp') (f : T -> T')
  (f' : T' -> option T) (f_can : pcancel f f') :=
  Preorder_isPOrder.Build disp (pcan_type f_can) (CancelPartial.anti f_can).

#[export]
HB.instance Definition _ (disp : disp_t) (T : choiceType)
  (disp' : disp_t) (T' : porderType disp') (f : T -> T') (f' : T' ->  T)
  (f_can : cancel f f') :=
  Preorder_isPOrder.Build disp (can_type f_can)
    (CancelPartial.anti (can_pcan f_can)).

HB.factory Record SubChoice_isSubPOrder d (T : porderType d) S (d' : disp_t) U
& SubChoice T S U := {}.

HB.builders Context d T S d' U & SubChoice_isSubPOrder d T S d' U.
HB.instance Definition _ := SubChoice_isSubPreorder.Build d T S d' U.
HB.instance Definition _ := Preorder_isPOrder.Build d' U
                              (@CancelPartial.anti U d T _ _ (@valK _ _ U)).
HB.end.

#[export]
  HB.instance Definition _ d (T : porderType d) (S : pred T) (d' : disp_t)
  (U : subType S) := SubChoice_isSubPOrder.Build d T S d' (sub_type U).

Module SubOrderExports.

Notation "[ 'SubChoice_isSubPOrder' 'of' U 'by' <: ]" :=
  (SubChoice_isSubPOrder.Build _ _ _ _ U)
    (format "[ 'SubChoice_isSubPOrder'  'of'  U  'by'  <: ]")
    : form_scope.
Notation "[ 'SubChoice_isSubPOrder' 'of' U 'by' <: 'with' disp ]" :=
  (SubChoice_isSubPOrder.Build _ _ _ disp U)
    (format "[ 'SubChoice_isSubPOrder'  'of'  U  'by'  <:  'with'  disp ]")
    : form_scope.

End SubOrderExports.
HB.export SubOrderExports.

Module Theory.
Export Order.Theory.
Export POrderTheory.
Export BPOrderTheory.
Export TPOrderTheory.
End Theory.

Module Exports.
HB.reexport.
End Exports.
End Order.

Export Order.Exports.
