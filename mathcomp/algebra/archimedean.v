(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype bigop order ssralg poly ssrnum ssrint.

(******************************************************************************)
(*                           Archimedean structures                           *)
(*                                                                            *)
(* NB: See CONTRIBUTING.md for an introduction to HB concepts and commands.   *)
(*                                                                            *)
(* This file defines some numeric structures extended with the Archimedean    *)
(* axiom. To use this file, insert "Import Num.Theory." and optionally        *)
(* "Import Num.Def." before your scripts as in the ssrnum library.            *)
(* The modules provided by this library subsume those from ssrnum.            *)
(*                                                                            *)
(* NB: the Archimedean structures are actually defined in ssrnum, but they    *)
(* are deprecated in ssrnum and will be relocated to this file in a future    *)
(* release.                                                                   *)
(*                                                                            *)
(* This file defines the following structures:                                *)
(*                                                                            *)
(*      archiNumDomainType == numDomainType with the Archimedean axiom        *)
(*                            The HB class is called ArchiNumDomain.          *)
(*       archiNumFieldType == numFieldType with the Archimedean axiom         *)
(*                            The HB class is called ArchiNumField.           *)
(*    archiClosedFieldType == closedFieldType with the Archimedean axiom      *)
(*                            The HB class is called ArchiClosedField.        *)
(*         archiDomainType == realDomainType with the Archimedean axiom       *)
(*                            The HB class is called ArchiDomain.             *)
(*          archiFieldType == realFieldType with the Archimedean axiom        *)
(*                            The HB class is called ArchiField.              *)
(*            archiRcfType == rcfType with the Archimedean axiom              *)
(*                            The HB class is called ArchiRealClosedField.    *)
(*                                                                            *)
(* Over these structures, we have the following operations:                   *)
(*  x \is a Num.int <=> x is an integer, i.e., x = m%:~R for some m : int     *)
(*  x \is a Num.nat <=> x is a natural number, i.e., x = m%:R for some m : nat*)
(*      Num.floor x == the m : int such that m%:~R <= z < (m + 1)%:~R         *)
(*                     when x \is a Num.real, otherwise 0%Z                   *)
(*       Num.ceil x == the m : int such that (m - 1)%:~R < z <= m%:~R         *)
(*                     when x \is a NUm.real, otherwise 0%Z                   *)
(*      Num.trunc x == the n : nat such that n%:R <= z < n.+1%:R              *)
(*                     when 0 <= n, otherwise 0%N                             *)
(*      Num.bound x == an upper bound for x, i.e., an n such that `|x| < n%:R *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import Order.TTheory GRing.Theory Num.Theory.

Module Num.

Module Import Exports.

Notation archiNumDomainType := Num.ArchiNumDomain.type.
Notation archiNumFieldType := Num.ArchiNumField.type.
Notation archiClosedFieldType := Num.ArchiClosedField.type.
Notation archiDomainType := Num.ArchiDomain.type.
Notation archiFieldType := Num.ArchiField.type.
Notation archiRcfType := Num.ArchiRealClosedField.type.

End Exports.

Module Import Internals.

Section ArchiNumDomain.
Variable R : archiNumDomainType.
Implicit Types x y : R.

Local Notation trunc := (@Num.Def.trunc R).

Definition truncP x :
  if 0 <= x then (trunc x)%:R <= x < (trunc x).+1%:R else trunc x == 0%N :=
  Num.Internals.truncP x.

Definition trunc_itv x : 0 <= x -> (trunc x)%:R <= x < (trunc x).+1%:R :=
  @Num.Internals.trunc_itv R x.

Fact floor_subproof x :
  {m | if x \is Num.real then m%:~R <= x < (m + 1)%:~R else m == 0}.
Proof.
have [Rx | _] := boolP (x \is Num.real); last by exists 0.
without loss x_ge0: x Rx / x >= 0.
  have [x_ge0 | /ltW x_le0] := real_ge0P Rx; first exact.
  case/(_ (- x)) => [||m]; rewrite ?rpredN ?oppr_ge0 //.
  rewrite lerNr ltrNl -!rmorphN opprD /= le_eqVlt.
  case: eqP => [-> _ | _ /andP[lt_x_m lt_m_x]].
    by exists (- m); rewrite lexx rmorphD ltrDl ltr01.
  by exists (- m - 1); rewrite (ltW lt_m_x) subrK.
by exists (Posz (trunc x)); rewrite addrC -intS -!pmulrn trunc_itv.
Qed.

End ArchiNumDomain.

End Internals.

Module Import Def.
Export ssrnum.Num.Def.
Definition floor {R : archiNumDomainType} (x : R) := sval (floor_subproof x).
Definition ceil {R : archiNumDomainType} (x : R) := - floor (- x).
End Def.

Notation trunc := trunc.
Notation floor := floor.
Notation ceil := ceil.
Notation bound := Num.ExtraDef.archi_bound.

Module Import Theory.
Export ssrnum.Num.Theory.

Section ArchiNumDomainTheory.

Variable R : archiNumDomainType.
Implicit Types x y z : R.

Local Notation trunc := (@Num.trunc R).
Local Notation floor := (@Num.floor R).
Local Notation ceil := (@Num.ceil R).
Local Notation nat_num := (@nat_num R).
Local Notation int_num := (@int_num R).

(* trunc and nat_num *)

Definition trunc_itv x : 0 <= x -> (trunc x)%:R <= x < (trunc x).+1%:R :=
  @trunc_itv R x.

Definition natrE x : (x \is a nat_num) = ((trunc x)%:R == x) :=
  @ssrnum.Num.Theory.mc_2_0.natrE R x.

Definition archi_boundP x : 0 <= x -> x < (bound x)%:R :=
  @ssrnum.Num.Theory.mc_2_0.archi_boundP R x.

Definition trunc_def x n : n%:R <= x < n.+1%:R -> trunc x = n :=
  @ssrnum.Num.Theory.mc_2_0.trunc_def R x n.

Definition natrK : cancel (GRing.natmul 1) trunc :=
  @ssrnum.Num.Theory.mc_2_0.natrK R.

Lemma truncK : {in nat_num, cancel trunc (GRing.natmul 1)}.
Proof. by move=> x; rewrite natrE => /eqP. Qed.

Lemma trunc0 : trunc 0 = 0%N. Proof. exact: natrK 0%N. Qed.
Lemma trunc1 : trunc 1 = 1%N. Proof. exact: natrK 1%N. Qed.
#[local] Hint Resolve trunc0 trunc1 : core.

Definition natr_nat n : n%:R \is a nat_num :=
  @ssrnum.Num.Theory.mc_2_0.natr_nat R n.
#[local] Hint Resolve natr_nat : core.

Definition natrP x : reflect (exists n, x = n%:R) (x \is a nat_num) :=
  @ssrnum.Num.Theory.mc_2_0.natrP R x.

Lemma truncD : {in nat_num & Rnneg, {morph trunc : x y / x + y >-> (x + y)%N}}.
Proof.
move=> _ y /natrP[n ->] y_ge0; apply: trunc_def.
by rewrite -addnS !natrD !natrK lerD2l ltrD2l trunc_itv.
Qed.

Lemma truncM : {in nat_num &, {morph trunc : x y / x * y >-> (x * y)%N}}.
Proof. by move=> _ _ /natrP[n1 ->] /natrP[n2 ->]; rewrite -natrM !natrK. Qed.

Lemma truncX n : {in nat_num, {morph trunc : x / x ^+ n >-> (x ^ n)%N}}.
Proof. by move=> _ /natrP[n1 ->]; rewrite -natrX !natrK. Qed.

Lemma rpred_nat_num (S : semiringClosed R) x : x \is a nat_num -> x \in S.
Proof. by move=> /natrP[n ->]; apply: rpred_nat. Qed.

Definition nat_num0 : 0 \is a nat_num := @ssrnum.Num.Theory.mc_2_0.nat_num0 R.
Definition nat_num1 : 1 \is a nat_num := @ssrnum.Num.Theory.mc_2_0.nat_num1 R.
#[local] Hint Resolve nat_num0 nat_num1 : core.

Definition nat_num_semiring : semiring_closed nat_num :=
  @ssrnum.Num.Theory.mc_2_0.nat_num_semiring R.
#[export]
HB.instance Definition _ := GRing.isSemiringClosed.Build R Num.nat_num_subdef
  nat_num_semiring.

Lemma Rreal_nat : {subset nat_num <= Rreal}.
Proof. by move=> _ /natrP[m ->]. Qed.

Lemma natr_normK x : x \is a nat_num -> `|x| ^+ 2 = x ^+ 2.
Proof. by move/Rreal_nat/real_normK. Qed.

Lemma trunc_gt0 x : (0 < trunc x)%N = (1 <= x).
Proof.
case: ifP (truncP x) => [le0x /andP[lemx ltxm1] | le0x /eqP ->]; last first.
  by apply/esym; apply/contraFF/le_trans: le0x.
apply/idP/idP => [m_gt0 | x_ge1]; first by apply: le_trans lemx; rewrite ler1n.
by rewrite -ltnS -(ltr_nat R) (le_lt_trans x_ge1).
Qed.

Lemma trunc0Pn x : reflect (trunc x = 0%N) (~~ (1 <= x)).
Proof. by rewrite -trunc_gt0 -eqn0Ngt; apply: eqP. Qed.

Lemma natr_ge0 x : x \is a nat_num -> 0 <= x.
Proof. by move=> /natrP[n ->]; apply: ler0n. Qed.

Lemma natr_gt0 x : x \is a nat_num -> (0 < x) = (x != 0).
Proof. by move=> /natrP[n ->]; rewrite pnatr_eq0 ltr0n lt0n. Qed.

Lemma norm_natr x : x \is a nat_num -> `|x| = x.
Proof. by move/natr_ge0/ger0_norm. Qed.

Lemma sum_truncK I r (P : pred I) F : (forall i, P i -> F i \is a nat_num) ->
  (\sum_(i <- r | P i) trunc (F i))%:R = \sum_(i <- r | P i) F i.
Proof.
by move=> natr; rewrite -sumrMnr; apply: eq_bigr => i Pi; rewrite truncK ?natr.
Qed.

Lemma prod_truncK I r (P : pred I) F : (forall i, P i -> F i \is a nat_num) ->
  (\prod_(i <- r | P i) trunc (F i))%:R = \prod_(i <- r | P i) F i.
Proof.
by move=> natr; rewrite natr_prod; apply: eq_bigr => i Pi; rewrite truncK ?natr.
Qed.

Lemma natr_sum_eq1 (I : finType) (P : pred I) (F : I -> R) :
     (forall i, P i -> F i \is a nat_num) -> \sum_(i | P i) F i = 1 ->
   {i : I | [/\ P i, F i = 1 & forall j, j != i -> P j -> F j = 0]}.
Proof.
move=> natF /eqP; rewrite -sum_truncK// -[1]/1%:R eqr_nat => /sum_nat_eq1 exi.
have [i /and3P[Pi /eqP f1 /forallP a]] : {i : I | [&& P i, trunc (F i) == 1%N
    & [forall j : I, ((j != i) ==> P j ==> (trunc (F j) == 0%N))]]}.
  apply/sigW; have [i [Pi /eqP f1 a]] := exi; exists i; apply/and3P; split=> //.
  by apply/forallP => j; apply/implyP => ji; apply/implyP => Pj; apply/eqP/a.
exists i; split=> [//||j ji Pj]; rewrite -[LHS]truncK ?natF ?f1//; apply/eqP.
by rewrite -[0]/0%:R eqr_nat; apply: implyP Pj; apply: implyP ji; apply: a.
Qed.

Lemma natr_mul_eq1 x y :
  x \is a nat_num -> y \is a nat_num -> (x * y == 1) = (x == 1) && (y == 1).
Proof. by do 2!move/truncK <-; rewrite -natrM !pnatr_eq1 muln_eq1. Qed.

Lemma natr_prod_eq1 (I : finType) (P : pred I) (F : I -> R) :
    (forall i, P i -> F i \is a nat_num) -> \prod_(i | P i) F i = 1 ->
  forall i, P i -> F i = 1.
Proof.
move=> natF /eqP; rewrite -prod_truncK// -[1]/1%:R eqr_nat prod_nat_seq_eq1.
move/allP => a i Pi; apply/eqP; rewrite -[F i]truncK ?natF// eqr_nat.
by apply: implyP Pi; apply: a; apply: mem_index_enum.
Qed.

(* floor and int_num *)

Local Lemma floorP x :
  if x \is Rreal then
    (floor x)%:~R <= x < (floor x + 1)%:~R else floor x == 0%N.
Proof. by rewrite /floor; case: (floor_subproof x). Qed.

Definition intrE x : (x \is a int_num) = (x \is a nat_num) || (- x \is a nat_num) :=
  @ssrnum.Num.Theory.mc_2_0.intrE R x.

Lemma floor_itv x : x \is Rreal -> (floor x)%:~R <= x < (floor x + 1)%:~R.
Proof. by case: (x \is _) (floorP x). Qed.

Lemma ge_floor x : x \is Rreal -> (floor x)%:~R <= x.
Proof. by move=> /floor_itv /andP[]. Qed.

Lemma lt_succ_floor x : x \is Rreal -> x < (floor x + 1)%:~R.
Proof. by move=> /floor_itv /andP[]. Qed.

Lemma floor_def x m : m%:~R <= x < (m + 1)%:~R -> floor x = m.
Proof.
case/andP=> lemx ltxm1; apply/eqP; rewrite eq_le -!ltzD1.
move: (ger_real lemx); rewrite realz => /floor_itv/andP[lefx ltxf1].
by rewrite -!(ltr_int R) 2?(@le_lt_trans _ _ x).
Qed.

Lemma floor_ge_int x n : x \is Rreal -> n%:~R <= x = (n <= floor x).
Proof.
move=> /floor_itv /andP[lefx ltxf1]; apply/idP/idP => lenx.
  by rewrite -ltzD1 -(ltr_int R); apply: le_lt_trans ltxf1.
by apply: le_trans lefx; rewrite ler_int.
Qed.

Lemma floor_le : {homo floor : x y / x <= y}.
Proof.
move=> x y lexy; move: (floorP x) (floorP y); rewrite (ger_real lexy).
case: ifP => [_ /andP[lefx _] /andP[_] | _ /eqP-> /eqP-> //].
by move=> /(le_lt_trans lexy) /(le_lt_trans lefx); rewrite ltr_int ltzD1.
Qed.

Lemma intrKfloor : cancel intr floor.
Proof. by move=> m; apply: floor_def; rewrite lexx rmorphD ltrDl ltr01. Qed.

Lemma intr_int m : m%:~R \is a int_num.
Proof. by rewrite intrE; case: m => n; rewrite ?opprK natr_nat ?orbT. Qed.
#[local] Hint Resolve intr_int : core.

Lemma intrP x : reflect (exists m, x = m%:~R) (x \is a int_num).
Proof.
apply: (iffP idP) => [x_int | [m -> //]].
rewrite -[x]opprK; move: x_int; rewrite intrE.
move=> /orP[] /natrP[n ->]; first by exists n; rewrite opprK.
by exists (- n%:R); rewrite mulrNz mulrz_nat.
Qed.

Lemma intrEfloor x : x \is a int_num = ((floor x)%:~R == x).
Proof.
by apply/intrP/eqP => [[n ->] | <-]; [rewrite intrKfloor | exists (floor x)].
Qed.

Lemma floorK : {in int_num, cancel floor intr}.
Proof. by move=> z; rewrite intrEfloor => /eqP. Qed.

Lemma floor0 : floor 0 = 0. Proof. exact: intrKfloor 0. Qed.
Lemma floor1 : floor 1 = 1. Proof. exact: intrKfloor 1. Qed.
#[local] Hint Resolve floor0 floor1 : core.

Lemma floorD : {in int_num & Rreal, {morph floor : x y / x + y}}.
Proof.
move=> _ y /intrP[m ->] Ry; apply: floor_def.
by rewrite -addrA 2!rmorphD /= intrKfloor lerD2l ltrD2l floor_itv.
Qed.

Lemma floorN : {in int_num, {morph floor : x / - x}}.
Proof. by move=> _ /intrP[m ->]; rewrite -rmorphN !intrKfloor. Qed.

Lemma floorM : {in int_num &, {morph floor : x y / x * y}}.
Proof.
by move=> _ _ /intrP[m1 ->] /intrP[m2 ->]; rewrite -rmorphM !intrKfloor.
Qed.

Lemma floorX n : {in int_num, {morph floor : x / x ^+ n}}.
Proof. by move=> _ /intrP[m ->]; rewrite -rmorphXn !intrKfloor. Qed.

(* ceil and int_num *)

Lemma ceil_itv x : x \is Rreal -> (ceil x - 1)%:~R < x <= (ceil x)%:~R.
Proof.
by move=> Rx; rewrite -opprD !mulrNz ltrNl lerNr andbC floor_itv ?realN.
Qed.

Lemma gt_pred_ceil x : x \is Rreal -> (ceil x - 1)%:~R < x.
Proof. by move=> /ceil_itv /andP[]. Qed.

Lemma le_ceil x : x \is Rreal -> x <= (ceil x)%:~R.
Proof. by move=> /ceil_itv /andP[]. Qed.

Lemma ceil_def x m : (m - 1)%:~R < x <= m%:~R -> ceil x = m.
Proof.
move=> Hx; apply/eqP; rewrite eqr_oppLR; apply/eqP/floor_def.
by rewrite lerNr ltrNl andbC -!mulrNz opprD opprK.
Qed.

Lemma ceil_le_int x n : x \is Rreal -> x <= n%:~R = (ceil x <= n).
Proof.
rewrite -realN; move=> /(floor_ge_int (- n)).
by rewrite mulrNz lerNl opprK => ->; rewrite lerNl.
Qed.

Lemma ceil_le : {homo ceil : x y / x <= y}.
Proof. by move=> x y lexy; rewrite /ceil lerN2 floor_le ?lerN2. Qed.

Lemma intrKceil : cancel intr ceil.
Proof. by move=> m; apply/eqP; rewrite eqr_oppLR -mulrNz intrKfloor. Qed.

Lemma intrEceil x : x \is a int_num = ((ceil x)%:~R == x).
Proof. by rewrite mulrNz eqr_oppLR -intrEfloor !intrE opprK orbC. Qed.

Lemma ceilK : {in int_num, cancel ceil intr}.
Proof. by move=> z; rewrite intrEceil => /eqP. Qed.

Lemma ceil0 : ceil 0 = 0. Proof. exact: intrKceil 0. Qed.
Lemma ceil1 : ceil 1 = 1. Proof. exact: intrKceil 1. Qed.
#[local] Hint Resolve ceil0 ceil1 : core.

Lemma ceilD : {in int_num & Rreal, {morph ceil : x y / x + y}}.
Proof.
move=> _ y /intrP[m ->] Ry; apply: ceil_def.
by rewrite -addrA 3!rmorphD /= intrKceil lerD2l ltrD2l -rmorphD ceil_itv.
Qed.

Lemma ceilN : {in int_num, {morph ceil : x / - x}}.
Proof. by move=> _ /intrP[m ->]; rewrite -rmorphN !intrKceil. Qed.

Lemma ceilM : {in int_num &, {morph ceil : x y / x * y}}.
Proof.
by move=> _ _ /intrP[m1 ->] /intrP[m2 ->]; rewrite -rmorphM !intrKceil.
Qed.

Lemma ceilX n : {in int_num, {morph ceil : x / x ^+ n}}.
Proof. by move=> _ /intrP[m ->]; rewrite -rmorphXn !intrKceil. Qed.

Lemma ceil_floor x : x \is Rreal -> ceil x = floor x + (~~ (x \is a int_num)).
Proof.
case Ix: (x \is a int_num) => Rx /=.
  by apply/eqP; rewrite addr0 eqr_oppLR floorN.
apply/ceil_def; rewrite addrK; move: (floor_itv Rx).
by rewrite le_eqVlt -intrEfloor Ix /= => /andP[-> /ltW].
Qed.

Lemma rpred_int_num (S : subringClosed R) x : x \is a int_num -> x \in S.
Proof. by move=> /intrP[n ->]; rewrite rpred_int. Qed.

Lemma int_num0 : 0 \is a int_num. Proof. by rewrite intrE nat_num0. Qed.
Definition int_num1 : 1 \is a int_num := @ssrnum.Num.Theory.mc_2_0.int_num1 R.
#[local] Hint Resolve int_num0 int_num1 : core.

Fact int_num_subring : subring_closed int_num.
Proof.
by split=> // _ _ /intrP[n ->] /intrP[m ->]; rewrite -?mulrzBr -?intrM intr_int.
Qed.
#[export]
HB.instance Definition _ := GRing.isSubringClosed.Build R Num.int_num_subdef
  int_num_subring.

Lemma intr_nat : {subset nat_num <= int_num}.
Proof. by move=> ?; rewrite intrE => ->. Qed.

Lemma Rreal_int : {subset int_num <= Rreal}. Proof. exact: rpred_int_num. Qed.

Lemma intr_normK x : x \is a int_num -> `|x| ^+ 2 = x ^+ 2.
Proof. by move/Rreal_int/real_normK. Qed.

Lemma intrEsign x : x \is a int_num -> x = (-1) ^+ (x < 0)%R * `|x|.
Proof. by move/Rreal_int/realEsign. Qed.

Lemma natr_norm_int x : x \is a int_num -> `|x| \is a nat_num.
Proof. by move=> /intrP[m ->]; rewrite -intr_norm rpred_nat_num ?natr_nat. Qed.

Lemma natrEint x : (x \is a nat_num) = (x \is a int_num) && (0 <= x).
Proof.
apply/idP/andP=> [Nx | [Zx x_ge0]]; first by rewrite intr_nat ?natr_ge0.
by rewrite -(ger0_norm x_ge0) natr_norm_int.
Qed.

Lemma intrEge0 x : 0 <= x -> (x \is a int_num) = (x \is a nat_num).
Proof. by rewrite natrEint andbC => ->. Qed.

Lemma natr_exp_even x n : ~~ odd n -> x \is a int_num -> x ^+ n \is a nat_num.
Proof.
move=> n_oddF x_intr.
by rewrite natrEint rpredX //= real_exprn_even_ge0 // Rreal_int.
Qed.

Lemma norm_intr_ge1 x : x \is a int_num -> x != 0 -> 1 <= `|x|.
Proof.
rewrite -normr_eq0 => /natr_norm_int/natrP[n ->].
by rewrite pnatr_eq0 ler1n lt0n.
Qed.

Lemma sqr_intr_ge1 x : x \is a int_num -> x != 0 -> 1 <= x ^+ 2.
Proof.
by move=> Zx nz_x; rewrite -intr_normK // expr_ge1 ?normr_ge0 ?norm_intr_ge1.
Qed.

Lemma intr_ler_sqr x : x \is a int_num -> x <= x ^+ 2.
Proof.
move=> Zx; have [-> | nz_x] := eqVneq x 0; first by rewrite expr0n.
apply: le_trans (_ : `|x| <= _); first by rewrite real_ler_norm ?Rreal_int.
by rewrite -intr_normK // ler_eXnr // norm_intr_ge1.
Qed.

Lemma floorpK : {in polyOver int_num, cancel (map_poly floor) (map_poly intr)}.
Proof.
move=> p /(all_nthP 0) Zp; apply/polyP=> i.
rewrite coef_map coef_map_id0 //= -[p]coefK coef_poly.
by case: ifP => [/Zp/floorK // | _]; rewrite floor0.
Qed.

Lemma floorpP (p : {poly R}) :
  p \is a polyOver int_num -> {q | p = map_poly intr q}.
Proof. by exists (map_poly floor p); rewrite floorpK. Qed.

(* Relating Cnat and oldCnat. *)

Lemma trunc_floor x : trunc x = if 0 <= x then `|floor x|%N else 0%N.
Proof.
case: ifP => [x_ge0 | x_ge0F]; last first.
  by apply/trunc0Pn; apply/contraFN: x_ge0F; apply/le_trans.
apply/trunc_def; rewrite !pmulrn intS addrC abszE; have/floor_le := x_ge0.
by rewrite floor0 => /normr_idP ->; exact/floor_itv/ger0_real.
Qed.

(* predCmod *)
Variables (U V : lmodType R) (f : {additive U -> V}).

Lemma raddfZ_nat a u : a \is a nat_num -> f (a *: u) = a *: f u.
Proof. by move=> /natrP[n ->]; apply: raddfZnat. Qed.

Lemma rpredZ_nat (S : addrClosed V) :
  {in nat_num & S, forall z u, z *: u \in S}.
Proof. by move=> _ u /natrP[n ->]; apply: rpredZnat. Qed.

Lemma raddfZ_int a u : a \is a int_num -> f (a *: u) = a *: f u.
Proof. by move=> /intrP[m ->]; rewrite !scaler_int raddfMz. Qed.

Lemma rpredZ_int (S : zmodClosed V) :
  {in int_num & S, forall z u, z *: u \in S}.
Proof. by move=> _ u /intrP[m ->] ?; rewrite scaler_int rpredMz. Qed.

(* autC *)
Implicit Type nu : {rmorphism R -> R}.

Lemma aut_natr nu : {in nat_num, nu =1 id}.
Proof. by move=> _ /natrP[n ->]; apply: rmorph_nat. Qed.

Lemma aut_intr nu : {in int_num, nu =1 id}.
Proof. by move=> _ /intrP[m ->]; apply: rmorph_int. Qed.

End ArchiNumDomainTheory.

Arguments natrK {R} _%N.
Arguments intrKfloor {R}.
Arguments intrKceil {R}.
Arguments natrP {R x}.
Arguments intrP {R x}.
#[global] Hint Resolve trunc0 trunc1 : core.
#[global] Hint Resolve floor0 floor1 : core.
#[global] Hint Resolve ceil0 ceil1 : core.
#[global] Hint Extern 0 (is_true (_%:R \is a nat_num)) => apply: natr_nat : core.
#[global] Hint Extern 0 (is_true (_%:R \in Num.nat_num_subdef)) => apply: natr_nat : core.
#[global] Hint Extern 0 (is_true (_%:~R \is a int_num)) => apply: intr_int : core.
#[global] Hint Extern 0 (is_true (_%:~R \in Num.int_num_subdef)) => apply: intr_int : core.
#[global] Hint Extern 0 (is_true (0 \is a nat_num)) => apply: nat_num0 : core.
#[global] Hint Extern 0 (is_true (0 \in Num.nat_num_subdef)) => apply: nat_num0 : core.
#[global] Hint Extern 0 (is_true (1 \is a nat_num)) => apply: nat_num1 : core.
#[global] Hint Extern 0 (is_true (1 \in Num.int_num_subdef)) => apply: nat_num1 : core.
#[global] Hint Extern 0 (is_true (0 \is a int_num)) => apply: int_num0 : core.
#[global] Hint Extern 0 (is_true (0 \in Num.int_num_subdef)) => apply: int_num0 : core.
#[global] Hint Extern 0 (is_true (1 \is a int_num)) => apply: int_num1 : core.
#[global] Hint Extern 0 (is_true (1 \in Num.int_num_subdef)) => apply: int_num1 : core.

Section ArchiDomainTheory.

Variables (R : archiDomainType).

Definition upper_nthrootP (x : R) i : (bound x <= i)%N -> x < 2%:R ^+ i :=
  @ssrnum.Num.Theory.mc_2_0.upper_nthrootP R x i.

End ArchiDomainTheory.

Section ArchiNumFieldTheory.

Variable R : archiNumFieldType.

(* autLmodC *)
Implicit Type nu : {rmorphism R -> R}.

Lemma natr_aut nu x : (nu x \is a nat_num) = (x \is a nat_num).
Proof. by apply/idP/idP=> /[dup] ? /(aut_natr nu) => [/fmorph_inj <-| ->]. Qed.

Lemma intr_aut nu x : (nu x \is a int_num) = (x \is a int_num).
Proof. by rewrite !intrE -rmorphN !natr_aut. Qed.

End ArchiNumFieldTheory.

Section ArchiClosedFieldTheory.

Variable R : archiClosedFieldType.

Implicit Type x : R.

Lemma conj_natr x : x \is a nat_num -> x^* = x.
Proof. by move/Rreal_nat/CrealP. Qed.

Lemma conj_intr x : x \is a int_num -> x^* = x.
Proof. by move/Rreal_int/CrealP. Qed.

End ArchiClosedFieldTheory.

Section ZnatPred.

Notation Znat_def := ssrint.mc_2_0.Znat_def.
Notation ZnatP := ssrint.mc_2_0.ZnatP.

End ZnatPred.

End Theory.

Module PredInstances.
HB.reexport.
End PredInstances.

Notation nat := nat_num.
Notation int := int_num.

End Num.

Export Num.ArchiNumDomain.Exports Num.ArchiNumField.Exports.
Export Num.ArchiClosedField.Exports Num.ArchiDomain.Exports.
Export Num.ArchiField.Exports Num.ArchiRealClosedField.Exports.
Export Num.Exports Num.PredInstances.
