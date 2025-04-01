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
(* This file defines the following structures:                                *)
(*                                                                            *)
(*      archiNumDomainType == numDomainType with the Archimedean axiom        *)
(*                            The HB class is called ArchiNumDomain.          *)
(*       archiNumFieldType == numFieldType with the Archimedean axiom         *)
(*                            The HB class is called ArchiNumField.           *)
(*    archiClosedFieldType == closedFieldType with the Archimedean axiom      *)
(*                            The HB class is called ArchiClosedField.        *)
(*     archiRealDomainType == realDomainType with the Archimedean axiom       *)
(*                            The HB class is called ArchiRealDomain.         *)
(*      archiRealFieldType == realFieldType with the Archimedean axiom        *)
(*                            The HB class is called ArchiRealField.          *)
(*            archiRcfType == rcfType with the Archimedean axiom              *)
(*                            The HB class is called ArchiRealClosedField.    *)
(*                                                                            *)
(* Over these structures, we have the following operations:                   *)
(*  x \is a Num.int <=> x is an integer, i.e., x = m%:~R for some m : int     *)
(*  x \is a Num.nat <=> x is a natural number, i.e., x = m%:R for some m : nat*)
(*      Num.floor x == the m : int such that m%:~R <= x < (m + 1)%:~R         *)
(*                     when x \is a Num.real, otherwise 0%Z                   *)
(*       Num.ceil x == the m : int such that (m - 1)%:~R < x <= m%:~R         *)
(*                     when x \is a Num.real, otherwise 0%Z                   *)
(*     Num.truncn x == the n : nat such that n%:R <= x < n.+1%:R              *)
(*                     when 0 <= n, otherwise 0%N                             *)
(*      Num.bound x == an upper bound for x, i.e., an n such that `|x| < n%:R *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import Order.TTheory GRing.Theory Num.Theory.

Module Num.
Import Num.Def.

HB.mixin Record NumDomain_hasFloorCeilTruncn R of Num.NumDomain R := {
  floor : R -> int;
  ceil  : R -> int;
  truncn : R -> nat;
  int_num_subdef : pred R;
  nat_num_subdef : pred R;
  floor_subproof :
    forall x,
      if x \is Rreal then (floor x)%:~R <= x < (floor x + 1)%:~R
      else floor x == 0;
  ceil_subproof : forall x, ceil x = - floor (- x);
  truncn_subproof : forall x, truncn x = if floor x is Posz n then n else 0;
  int_num_subproof : forall x, reflect (exists n, x = n%:~R) (int_num_subdef x);
  nat_num_subproof : forall x, reflect (exists n, x = n%:R) (nat_num_subdef x);
}.

#[short(type="archiNumDomainType")]
HB.structure Definition ArchiNumDomain :=
  { R of NumDomain_hasFloorCeilTruncn R & Num.NumDomain R }.

Module ArchiNumDomainExports.
Bind Scope ring_scope with ArchiNumDomain.sort.
End ArchiNumDomainExports.
HB.export ArchiNumDomainExports.

#[short(type="archiNumFieldType")]
HB.structure Definition ArchiNumField :=
  { R of NumDomain_hasFloorCeilTruncn R & Num.NumField R }.

Module ArchiNumFieldExports.
Bind Scope ring_scope with ArchiNumField.sort.
End ArchiNumFieldExports.
HB.export ArchiNumFieldExports.

#[short(type="archiClosedFieldType")]
HB.structure Definition ArchiClosedField :=
  { R of NumDomain_hasFloorCeilTruncn R & Num.ClosedField R }.

Module ArchiClosedFieldExports.
Bind Scope ring_scope with ArchiClosedField.sort.
End ArchiClosedFieldExports.
HB.export ArchiClosedFieldExports.

#[short(type="archiRealDomainType")]
HB.structure Definition ArchiRealDomain :=
  { R of NumDomain_hasFloorCeilTruncn R & Num.RealDomain R }.

Module ArchiRealDomainExports.
Bind Scope ring_scope with ArchiRealDomain.sort.
End ArchiRealDomainExports.
HB.export ArchiRealDomainExports.

#[short(type="archiRealFieldType")]
HB.structure Definition ArchiRealField :=
  { R of NumDomain_hasFloorCeilTruncn R & Num.RealField R }.

Module ArchiRealFieldExports.
Bind Scope ring_scope with ArchiRealField.sort.
End ArchiRealFieldExports.
HB.export ArchiRealFieldExports.

#[short(type="archiRcfType")]
HB.structure Definition ArchiRealClosedField :=
  { R of NumDomain_hasFloorCeilTruncn R & Num.RealClosedField R }.

Module ArchiRealClosedFieldExports.
Bind Scope ring_scope with ArchiRealClosedField.sort.
End ArchiRealClosedFieldExports.
HB.export ArchiRealClosedFieldExports.

Section Def.
Context {R : archiNumDomainType}.

Definition nat_num : qualifier 1 R := [qualify a x : R | nat_num_subdef x].
Definition int_num : qualifier 1 R := [qualify a x : R | int_num_subdef x].
Definition bound (x : R) := (truncn `|x|).+1.

End Def.

Arguments floor {R} : rename, simpl never.
Arguments ceil {R} : rename, simpl never.
Arguments truncn {R} : rename, simpl never.
Arguments nat_num {R} : simpl never.
Arguments int_num {R} : simpl never.

#[deprecated(since="mathcomp 2.4.0", note="Renamed to truncn.")]
Notation trunc := truncn.

Module Def.
Export ssrnum.Num.Def.

Notation truncn := truncn.
#[deprecated(since="mathcomp 2.4.0", note="Renamed to truncn.")]
Notation trunc := truncn.
Notation floor := floor.
Notation ceil  := ceil.
Notation nat_num := nat_num.
Notation int_num := int_num.
Notation archi_bound := bound.

End Def.

Module intArchimedean.
Section intArchimedean.

Implicit Types n : int.

Lemma floorP n : if n \is Rreal then n%:~R <= n < (n + 1)%:~R else n == 0.
Proof. by rewrite num_real !intz ltzD1 lexx. Qed.

Lemma intrP n : reflect (exists m, n = m%:~R) true.
Proof. by apply: ReflectT; exists n; rewrite intz. Qed.

Lemma natrP n : reflect (exists m, n = m%:R) (0 <= n).
Proof.
apply: (iffP idP); last by case=> m ->; rewrite ler0n.
by case: n => // n _; exists n; rewrite natz.
Qed.

End intArchimedean.
End intArchimedean.

#[export]
HB.instance Definition _ :=
  @NumDomain_hasFloorCeilTruncn.Build int id id _ xpredT Rnneg_pred
    intArchimedean.floorP (fun=> esym (opprK _)) (fun=> erefl)
    intArchimedean.intrP intArchimedean.natrP.

Module Import Theory.
Export ssrnum.Num.Theory.

Section ArchiNumDomainTheory.

Variable R : archiNumDomainType.
Implicit Types x y z : R.

Local Notation truncn := (@truncn R).
Local Notation floor := (@floor R).
Local Notation ceil := (@ceil R).
Local Notation nat_num := (@Def.nat_num R).
Local Notation int_num := (@Def.int_num R).

Local Lemma floorP x :
  if x \is Rreal then (floor x)%:~R <= x < (floor x + 1)%:~R else floor x == 0.
Proof. exact: floor_subproof. Qed.

Lemma floorNceil x : floor x = - ceil (- x).
Proof. by rewrite ceil_subproof !opprK. Qed.

Lemma ceilNfloor x : ceil x = - floor (- x).
Proof. exact: ceil_subproof. Qed.

Lemma truncEfloor x : truncn x = if floor x is Posz n then n else 0.
Proof. exact: truncn_subproof. Qed.

Lemma natrP x : reflect (exists n, x = n%:R) (x \is a nat_num).
Proof. exact: nat_num_subproof. Qed.

Lemma intrP x : reflect (exists m, x = m%:~R) (x \is a int_num).
Proof. exact: int_num_subproof. Qed.

(* int_num and nat_num *)

Lemma intr_int m : m%:~R \is a int_num. Proof. by apply/intrP; exists m. Qed.
Lemma natr_nat n : n%:R \is a nat_num. Proof. by apply/natrP; exists n. Qed.
#[local] Hint Resolve intr_int natr_nat : core.

Lemma rpred_int_num (S : subringClosed R) x : x \is a int_num -> x \in S.
Proof. by move=> /intrP[n ->]; rewrite rpred_int. Qed.

Lemma rpred_nat_num (S : semiringClosed R) x : x \is a nat_num -> x \in S.
Proof. by move=> /natrP[n ->]; apply: rpred_nat. Qed.

Lemma int_num0 : 0 \is a int_num. Proof. exact: (intr_int 0). Qed.
Lemma int_num1 : 1 \is a int_num. Proof. exact: (intr_int 1). Qed.
Lemma nat_num0 : 0 \is a nat_num. Proof. exact: (natr_nat 0). Qed.
Lemma nat_num1 : 1 \is a nat_num. Proof. exact: (natr_nat 1). Qed.
#[local] Hint Resolve int_num0 int_num1 nat_num0 nat_num1 : core.

Fact int_num_subring : subring_closed int_num.
Proof.
by split=> // _ _ /intrP[n ->] /intrP[m ->]; rewrite -(intrB, intrM).
Qed.
#[export]
HB.instance Definition _ := GRing.isSubringClosed.Build R int_num_subdef
  int_num_subring.

Fact nat_num_semiring : semiring_closed nat_num.
Proof.
by do 2![split] => //= _ _ /natrP[n ->] /natrP[m ->]; rewrite -(natrD, natrM).
Qed.
#[export]
HB.instance Definition _ := GRing.isSemiringClosed.Build R nat_num_subdef
  nat_num_semiring.

Lemma Rreal_nat : {subset nat_num <= Rreal}. Proof. exact: rpred_nat_num. Qed.

Lemma intr_nat : {subset nat_num <= int_num}.
Proof. by move=> _ /natrP[n ->]; rewrite pmulrn intr_int. Qed.

Lemma Rreal_int : {subset int_num <= Rreal}. Proof. exact: rpred_int_num. Qed.

Lemma intrE x : (x \is a int_num) = (x \is a nat_num) || (- x \is a nat_num).
Proof.
apply/idP/orP => [/intrP[[n|n] ->]|[]/intr_nat]; rewrite ?rpredN //.
  by left; apply/natrP; exists n.
by rewrite NegzE intrN opprK; right; apply/natrP; exists n.+1.
Qed.

Lemma intr_normK x : x \is a int_num -> `|x| ^+ 2 = x ^+ 2.
Proof. by move/Rreal_int/real_normK. Qed.

Lemma natr_normK x : x \is a nat_num -> `|x| ^+ 2 = x ^+ 2.
Proof. by move/Rreal_nat/real_normK. Qed.

Lemma natr_norm_int x : x \is a int_num -> `|x| \is a nat_num.
Proof. by move=> /intrP[m ->]; rewrite -intr_norm rpred_nat_num ?natr_nat. Qed.

Lemma natr_ge0 x : x \is a nat_num -> 0 <= x.
Proof. by move=> /natrP[n ->]; apply: ler0n. Qed.

Lemma natr_gt0 x : x \is a nat_num -> (0 < x) = (x != 0).
Proof. by move/natr_ge0; case: comparableP. Qed.

Lemma natrEint x : (x \is a nat_num) = (x \is a int_num) && (0 <= x).
Proof.
apply/idP/andP=> [Nx | [Zx x_ge0]]; first by rewrite intr_nat ?natr_ge0.
by rewrite -(ger0_norm x_ge0) natr_norm_int.
Qed.

Lemma intrEge0 x : 0 <= x -> (x \is a int_num) = (x \is a nat_num).
Proof. by rewrite natrEint andbC => ->. Qed.

Lemma intrEsign x : x \is a int_num -> x = (-1) ^+ (x < 0)%R * `|x|.
Proof. by move/Rreal_int/realEsign. Qed.

Lemma norm_natr x : x \is a nat_num -> `|x| = x.
Proof. by move/natr_ge0/ger0_norm. Qed.

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

(* floor and int_num *)

Lemma real_floor_itv x : x \is Rreal -> (floor x)%:~R <= x < (floor x + 1)%:~R.
Proof. by case: ifP (floorP x). Qed.

Lemma real_floor_le x : x \is Rreal -> (floor x)%:~R <= x.
Proof. by case/real_floor_itv/andP. Qed.

Lemma real_floorD1_gt x : x \is Rreal -> x < (floor x + 1)%:~R.
Proof. by case/real_floor_itv/andP. Qed.

Lemma floor_def x m : m%:~R <= x < (m + 1)%:~R -> floor x = m.
Proof.
case/andP=> lemx ltxm1; apply/eqP; rewrite eq_le -!ltzD1.
move: (ger_real lemx); rewrite realz => /real_floor_itv/andP[lefx ltxf1].
by rewrite -!(ltr_int R) 2?(@le_lt_trans _ _ x).
Qed.

(* TODO: rename to real_floor_ge_int,
   once the currently deprecated one has been removed *)
Lemma real_floor_ge_int_tmp x n : x \is Rreal -> (n <= floor x) = (n%:~R <= x).
Proof.
move=> /real_floor_itv /andP[lefx ltxf1]; apply/idP/idP => lenx.
  by apply: le_trans lefx; rewrite ler_int.
by rewrite -ltzD1 -(ltr_int R); apply: le_lt_trans ltxf1.
Qed.

#[deprecated(since="mathcomp 2.4.0", note="Use real_floor_ge_int_tmp instead.")]
Lemma real_floor_ge_int x n : x \is Rreal -> (n%:~R <= x) = (n <= floor x).
Proof. by move=> ?; rewrite real_floor_ge_int_tmp. Qed.

Lemma real_floor_lt_int x n : x \is Rreal -> (floor x < n) = (x < n%:~R).
Proof.
by move=> ?; rewrite [RHS]real_ltNge ?realz -?real_floor_ge_int_tmp -?ltNge.
Qed.

Lemma real_floor_eq x n : x \is Rreal ->
  (floor x == n) = (n%:~R <= x < (n + 1)%:~R).
Proof.
by move=> xr; apply/eqP/idP => [<-|]; [exact: real_floor_itv|exact: floor_def].
Qed.

Lemma le_floor : {homo floor : x y / x <= y}.
Proof.
move=> x y lexy; move: (floorP x) (floorP y); rewrite (ger_real lexy).
case: ifP => [_ /andP[lefx _] /andP[_] | _ /eqP-> /eqP-> //].
by move=> /(le_lt_trans lexy) /(le_lt_trans lefx); rewrite ltr_int ltzD1.
Qed.

Lemma intrKfloor : cancel intr floor.
Proof. by move=> m; apply: floor_def; rewrite lexx rmorphD ltrDl ltr01. Qed.

Lemma natr_int n : n%:R \is a int_num.
Proof. by rewrite intrE natr_nat. Qed.
#[local] Hint Resolve natr_int : core.

Lemma intrEfloor x : x \is a int_num = ((floor x)%:~R == x).
Proof.
by apply/intrP/eqP => [[n ->] | <-]; [rewrite intrKfloor | exists (floor x)].
Qed.

Lemma floorK : {in int_num, cancel floor intr}.
Proof. by move=> z; rewrite intrEfloor => /eqP. Qed.

Lemma floor0 : floor 0 = 0. Proof. exact: intrKfloor 0. Qed.
Lemma floor1 : floor 1 = 1. Proof. exact: intrKfloor 1. Qed.
#[local] Hint Resolve floor0 floor1 : core.

Lemma real_floorDzr : {in int_num & Rreal, {morph floor : x y / x + y}}.
Proof.
move=> _ y /intrP[m ->] Ry; apply: floor_def.
by rewrite -addrA 2!rmorphD /= intrKfloor lerD2l ltrD2l real_floor_itv.
Qed.

Lemma real_floorDrz : {in Rreal & int_num, {morph floor : x y / x + y}}.
Proof. by move=> x y xr yz; rewrite addrC real_floorDzr // addrC. Qed.

Lemma floorN : {in int_num, {morph floor : x / - x}}.
Proof. by move=> _ /intrP[m ->]; rewrite -rmorphN !intrKfloor. Qed.

Lemma floorM : {in int_num &, {morph floor : x y / x * y}}.
Proof.
by move=> _ _ /intrP[m1 ->] /intrP[m2 ->]; rewrite -rmorphM !intrKfloor.
Qed.

Lemma floorX n : {in int_num, {morph floor : x / x ^+ n}}.
Proof. by move=> _ /intrP[m ->]; rewrite -rmorphXn !intrKfloor. Qed.

Lemma real_floor_ge0 x : x \is Rreal -> (0 <= floor x) = (0 <= x).
Proof. by move=> ?; rewrite real_floor_ge_int_tmp. Qed.

Lemma floor_lt0 x : (floor x < 0) = (x < 0).
Proof.
have := floorP x; case: ifP => [xr _ | xr /eqP<-].
  by rewrite real_floor_lt_int.
by rewrite ltxx; apply/esym/(contraFF _ xr)/ltr0_real.
Qed.

Lemma real_floor_le0 x : x \is Rreal -> (floor x <= 0) = (x < 1).
Proof. by move=> ?; rewrite -ltzD1 add0r real_floor_lt_int. Qed.

Lemma floor_gt0 x : (floor x > 0) = (x >= 1).
Proof.
have := floorP x; case: ifP => [xr _ | xr /eqP->].
  by rewrite gtz0_ge1 real_floor_ge_int_tmp.
by rewrite ltxx; apply/esym/(contraFF _ xr)/ger1_real.
Qed.

Lemma floor_neq0 x : (floor x != 0) = (x < 0) || (x >= 1).
Proof.
have := floorP x; case: ifP => [xr _ | xr /eqP->]; rewrite ?eqxx/=.
  by rewrite neq_lt floor_lt0 floor_gt0.
by apply/esym/(contraFF _ xr) => /orP[]; [exact: ltr0_real|exact: ger1_real].
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

(* ceil and int_num *)

Lemma real_ceil_itv x : x \is Rreal -> (ceil x - 1)%:~R < x <= (ceil x)%:~R.
Proof.
rewrite ceilNfloor -opprD !intrN ltrNl lerNr andbC -realN.
exact: real_floor_itv.
Qed.

Lemma real_ceilB1_lt x : x \is Rreal -> (ceil x - 1)%:~R < x.
Proof. by case/real_ceil_itv/andP. Qed.

Lemma real_ceil_ge x : x \is Rreal -> x <= (ceil x)%:~R.
Proof. by case/real_ceil_itv/andP. Qed.

Lemma ceil_def x m : (m - 1)%:~R < x <= m%:~R -> ceil x = m.
Proof.
rewrite -ltrN2 -lerN2 andbC -!intrN opprD opprK ceilNfloor.
by move=> /floor_def ->; rewrite opprK.
Qed.

(* TODO: rename to real_ceil_le_int,
   once the currently deprecated one has been removed *)
Lemma real_ceil_le_int_tmp x n : x \is Rreal -> (ceil x <= n) = (x <= n%:~R).
Proof.
rewrite ceilNfloor lerNl -realN => /real_floor_ge_int_tmp ->.
by rewrite intrN lerN2.
Qed.

#[deprecated(since="mathcomp 2.4.0", note="Use real_ceil_le_int_tmp instead.")]
Lemma real_ceil_le_int x n : x \is Rreal -> x <= n%:~R = (ceil x <= n).
Proof. by move=> ?; rewrite real_ceil_le_int_tmp. Qed.

Lemma real_ceil_gt_int x n : x \is Rreal -> (n < ceil x) = (n%:~R < x).
Proof.
by move=> ?; rewrite [RHS]real_ltNge ?realz -?real_ceil_le_int_tmp ?ltNge.
Qed.

Lemma real_ceil_eq x n : x \is Rreal ->
  (ceil x == n) = ((n - 1)%:~R < x <= n%:~R).
Proof.
by move=> xr; apply/eqP/idP => [<-|]; [exact: real_ceil_itv|exact: ceil_def].
Qed.

(* TODO: rename to le_ceil,
   once the currently deprecated one has been removed *)
Lemma le_ceil_tmp : {homo ceil : x y / x <= y}.
Proof. by move=> x y lexy; rewrite !ceilNfloor lerN2 le_floor ?lerN2. Qed.

Lemma intrKceil : cancel intr ceil.
Proof. by move=> m; rewrite ceilNfloor -intrN intrKfloor opprK. Qed.

Lemma intrEceil x : x \is a int_num = ((ceil x)%:~R == x).
Proof. by rewrite -rpredN intrEfloor -eqr_oppLR -intrN -ceilNfloor. Qed.

Lemma ceilK : {in int_num, cancel ceil intr}.
Proof. by move=> z; rewrite intrEceil => /eqP. Qed.

Lemma ceil0 : ceil 0 = 0. Proof. exact: intrKceil 0. Qed.
Lemma ceil1 : ceil 1 = 1. Proof. exact: intrKceil 1. Qed.
#[local] Hint Resolve ceil0 ceil1 : core.

Lemma real_ceilDzr : {in int_num & Rreal, {morph ceil : x y / x + y}}.
Proof.
move=> x y x_int y_real.
by rewrite ceilNfloor opprD real_floorDzr ?rpredN // opprD -!ceilNfloor.
Qed.

Lemma real_ceilDrz : {in Rreal & int_num, {morph ceil : x y / x + y}}.
Proof. by move=> x y xr yz; rewrite addrC real_ceilDzr // addrC. Qed.

Lemma ceilN : {in int_num, {morph ceil : x / - x}}.
Proof. by move=> ? ?; rewrite !ceilNfloor !opprK floorN. Qed.

Lemma ceilM : {in int_num &, {morph ceil : x y / x * y}}.
Proof.
by move=> _ _ /intrP[m1 ->] /intrP[m2 ->]; rewrite -rmorphM !intrKceil.
Qed.

Lemma ceilX n : {in int_num, {morph ceil : x / x ^+ n}}.
Proof. by move=> _ /intrP[m ->]; rewrite -rmorphXn !intrKceil. Qed.

Lemma real_ceil_ge0 x : x \is Rreal -> (0 <= ceil x) = (-1 < x).
Proof.
by move=> ?; rewrite ceilNfloor oppr_ge0 real_floor_le0 ?realN 1?ltrNl.
Qed.

Lemma ceil_lt0 x : (ceil x < 0) = (x <= -1).
Proof. by rewrite ceilNfloor oppr_lt0 floor_gt0 lerNr. Qed.

Lemma real_ceil_le0 x : x \is Rreal -> (ceil x <= 0) = (x <= 0).
Proof. by move=> ?; rewrite real_ceil_le_int_tmp. Qed.

Lemma ceil_gt0 x : (ceil x > 0) = (x > 0).
Proof. by rewrite ceilNfloor oppr_gt0 floor_lt0 oppr_lt0. Qed.

Lemma ceil_neq0 x : (ceil x != 0) = (x <= -1) || (x > 0).
Proof. by rewrite ceilNfloor oppr_eq0 floor_neq0 oppr_lt0 lerNr orbC. Qed.

Lemma real_ceil_floor x : x \is Rreal ->
  ceil x = floor x + (~~ (x \is a int_num)).
Proof.
case Ix: (x \is a int_num) => Rx /=.
  by apply/eqP; rewrite addr0 ceilNfloor eqr_oppLR floorN.
apply/ceil_def; rewrite addrK; move: (real_floor_itv Rx).
by rewrite le_eqVlt -intrEfloor Ix /= => /andP[-> /ltW].
Qed.

(* Relating Cnat and oldCnat. *)

Lemma truncn_floor x : truncn x = if 0 <= x then `|floor x|%N else 0%N.
Proof.
move: (floorP x); rewrite truncEfloor realE.
have [/le_floor|_]/= := boolP (0 <= x); first by rewrite floor0; case: floor.
by case: ifP => [/le_floor|_ /eqP->//]; rewrite floor0; case: floor => [[]|].
Qed.

(* trunc and nat_num *)

Local Lemma truncnP x :
  if 0 <= x then (truncn x)%:R <= x < (truncn x).+1%:R else truncn x == 0%N.
Proof.
rewrite truncn_floor.
case: (boolP (0 <= x)) => //= /[dup] /le_floor + /ger0_real/real_floor_itv.
by rewrite floor0; case: (floor x) => // n _; rewrite absz_nat addrC -intS.
Qed.

Lemma truncn_itv x : 0 <= x -> (truncn x)%:R <= x < (truncn x).+1%:R.
Proof. by move=> x_ge0; move: (truncnP x); rewrite x_ge0. Qed.

Lemma truncn_le x : (truncn x)%:R <= x = (0 <= x).
Proof. by have := (truncnP x); case: ifP => [+ /andP[] | + /eqP->//]. Qed.

Lemma real_truncnS_gt x : x \is Rreal -> x < (truncn x).+1%:R.
Proof. by move/real_ge0P => [/truncn_itv/andP[]|/lt_le_trans->]. Qed.

Lemma truncn_def x n : n%:R <= x < n.+1%:R -> truncn x = n.
Proof.
case/andP=> lemx ltxm1; apply/eqP; rewrite eqn_leq -ltnS -[(n <= _)%N]ltnS.
have/truncn_itv/andP[lefx ltxf1]: 0 <= x by apply: le_trans lemx; apply: ler0n.
by rewrite -!(ltr_nat R) 2?(@le_lt_trans _ _ x).
Qed.

Lemma truncn_ge_nat x n : 0 <= x -> (n <= truncn x)%N = (n%:R <= x).
Proof.
move=> /truncn_itv /andP[letx ltxt1]; apply/idP/idP => lenx.
  by apply: le_trans letx; rewrite ler_nat.
by rewrite -ltnS -(ltr_nat R); apply: le_lt_trans ltxt1.
Qed.

Lemma truncn_gt_nat x n : (n < truncn x)%N = (n.+1%:R <= x).
Proof.
have := truncnP x; case: ifP => [x0 _ | x0 /eqP->].
  by rewrite truncn_ge_nat.
by rewrite ltn0; apply/esym/(contraFF _ x0)/le_trans.
Qed.

Lemma truncn_lt_nat x n : 0 <= x -> (truncn x < n)%N = (x < n%:R).
Proof. by move=> ?; rewrite real_ltNge ?ger0_real// ltnNge truncn_ge_nat. Qed.

Lemma real_truncn_le_nat x n : x \is Rreal -> (truncn x <= n)%N = (x < n.+1%:R).
Proof. by move=> ?; rewrite real_ltNge// leqNgt truncn_gt_nat. Qed.

Lemma truncn_eq x n : 0 <= x -> (truncn x == n) = (n%:R <= x < n.+1%:R).
Proof.
by move=> xr; apply/eqP/idP => [<-|]; [exact: truncn_itv|exact: truncn_def].
Qed.

Lemma le_truncn : {homo truncn : x y / x <= y >-> (x <= y)%N}.
Proof.
move=> x y lexy; move: (truncnP x) (truncnP y).
case: ifP => [x0 /andP[letx _] | x0 /eqP->//].
case: ifP => [y0 /andP[_] | y0 /eqP->]; [|by rewrite (le_trans x0 lexy) in y0].
by move=> /(le_lt_trans lexy) /(le_lt_trans letx); rewrite ltr_nat ltnS.
Qed.

Lemma natrK : cancel (GRing.natmul 1) truncn.
Proof. by move=> m; apply: truncn_def; rewrite ler_nat ltr_nat ltnS leqnn. Qed.

Lemma natrEtruncn x : (x \is a nat_num) = ((truncn x)%:R == x).
Proof.
by apply/natrP/eqP => [[n ->]|<-]; [rewrite natrK | exists (truncn x)].
Qed.

Lemma archi_boundP x : 0 <= x -> x < (bound x)%:R.
Proof.
move=> x_ge0; case/truncn_itv/andP: (normr_ge0 x) => _.
exact/le_lt_trans/real_ler_norm/ger0_real.
Qed.

Lemma truncnK : {in nat_num, cancel truncn (GRing.natmul 1)}.
Proof. by move=> x; rewrite natrEtruncn => /eqP. Qed.

Lemma truncn0 : truncn 0 = 0%N. Proof. exact: natrK 0%N. Qed.
Lemma truncn1 : truncn 1 = 1%N. Proof. exact: natrK 1%N. Qed.
#[local] Hint Resolve truncn0 truncn1 : core.

Lemma truncnD :
  {in nat_num & Rnneg, {morph truncn : x y / x + y >-> (x + y)%N}}.
Proof.
move=> _ y /natrP[n ->] y_ge0; apply: truncn_def.
by rewrite -addnS !natrD !natrK lerD2l ltrD2l truncn_itv.
Qed.

Lemma truncnM : {in nat_num &, {morph truncn : x y / x * y >-> (x * y)%N}}.
Proof. by move=> _ _ /natrP[n1 ->] /natrP[n2 ->]; rewrite -natrM !natrK. Qed.

Lemma truncnX n : {in nat_num, {morph truncn : x / x ^+ n >-> (x ^ n)%N}}.
Proof. by move=> _ /natrP[n1 ->]; rewrite -natrX !natrK. Qed.

Lemma truncn_gt0 x : (0 < truncn x)%N = (1 <= x).
Proof.
case: ifP (truncnP x) => [le0x /andP[lemx ltxm1] | le0x /eqP ->]; last first.
  by apply/esym; apply/contraFF/le_trans: le0x.
apply/idP/idP => [m_gt0 | x_ge1]; first by apply: le_trans lemx; rewrite ler1n.
by rewrite -ltnS -(ltr_nat R) (le_lt_trans x_ge1).
Qed.

Lemma truncn0Pn x : reflect (truncn x = 0%N) (~~ (1 <= x)).
Proof. by rewrite -truncn_gt0 -eqn0Ngt; apply: eqP. Qed.

Lemma sum_truncnK I r (P : pred I) F : (forall i, P i -> F i \is a nat_num) ->
  (\sum_(i <- r | P i) truncn (F i))%:R = \sum_(i <- r | P i) F i.
Proof. by rewrite natr_sum => natr; apply: eq_bigr => i /natr /truncnK. Qed.

Lemma prod_truncnK I r (P : pred I) F : (forall i, P i -> F i \is a nat_num) ->
  (\prod_(i <- r | P i) truncn (F i))%:R = \prod_(i <- r | P i) F i.
Proof. by rewrite natr_prod => natr; apply: eq_bigr => i /natr /truncnK. Qed.

Lemma natr_sum_eq1 (I : finType) (P : pred I) (F : I -> R) :
     (forall i, P i -> F i \is a nat_num) -> \sum_(i | P i) F i = 1 ->
   {i : I | [/\ P i, F i = 1 & forall j, j != i -> P j -> F j = 0]}.
Proof.
move=> natF /eqP; rewrite -sum_truncnK// -[1]/1%:R eqr_nat => /sum_nat_eq1 exi.
have [i /and3P[Pi /eqP f1 /forallP a]] : {i : I | [&& P i, truncn (F i) == 1
    & [forall j : I, ((j != i) ==> P j ==> (truncn (F j) == 0))]]}.
  apply/sigW; have [i [Pi /eqP f1 a]] := exi; exists i; apply/and3P; split=> //.
  by apply/forallP => j; apply/implyP => ji; apply/implyP => Pj; apply/eqP/a.
exists i; split=> [//||j ji Pj]; rewrite -[LHS]truncnK ?natF ?f1//; apply/eqP.
by rewrite -[0]/0%:R eqr_nat; apply: implyP Pj; apply: implyP ji; apply: a.
Qed.

Lemma natr_mul_eq1 x y :
  x \is a nat_num -> y \is a nat_num -> (x * y == 1) = (x == 1) && (y == 1).
Proof. by do 2!move/truncnK <-; rewrite -natrM !pnatr_eq1 muln_eq1. Qed.

Lemma natr_prod_eq1 (I : finType) (P : pred I) (F : I -> R) :
    (forall i, P i -> F i \is a nat_num) -> \prod_(i | P i) F i = 1 ->
  forall i, P i -> F i = 1.
Proof.
move=> natF /eqP; rewrite -prod_truncnK// -[1]/1%:R eqr_nat prod_nat_seq_eq1.
move/allP => a i Pi; apply/eqP; rewrite -[F i]truncnK ?natF// eqr_nat.
by apply: implyP Pi; apply: a; apply: mem_index_enum.
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

#[deprecated(since="mathcomp 2.4.0", note="Renamed to truncn_itv.")]
Notation trunc_itv := truncn_itv.
#[deprecated(since="mathcomp 2.4.0", note="Renamed to truncn_def.")]
Notation trunc_def := truncn_def.
#[deprecated(since="mathcomp 2.4.0", note="Renamed to truncnK.")]
Notation truncK := truncnK.
#[deprecated(since="mathcomp 2.4.0", note="Renamed to truncn0.")]
Notation trunc0 := truncn0.
#[deprecated(since="mathcomp 2.4.0", note="Renamed to truncn1.")]
Notation trunc1 := truncn1.
#[deprecated(since="mathcomp 2.4.0", note="Renamed to truncnD.")]
Notation truncD := truncnD.
#[deprecated(since="mathcomp 2.4.0", note="Renamed to truncnM.")]
Notation truncM := truncnM.
#[deprecated(since="mathcomp 2.4.0", note="Renamed to truncnX.")]
Notation truncX := truncnX.
#[deprecated(since="mathcomp 2.4.0", note="Renamed to truncn_gt0.")]
Notation trunc_gt0 := truncn_gt0.
#[deprecated(since="mathcomp 2.4.0", note="Renamed to truncn0Pn.")]
Notation trunc0Pn := truncn0Pn.
#[deprecated(since="mathcomp 2.4.0", note="Renamed to sum_truncnK.")]
Notation sum_truncK := sum_truncnK.
#[deprecated(since="mathcomp 2.4.0", note="Renamed to prod_truncnK.")]
Notation prod_truncK := prod_truncnK.
#[deprecated(since="mathcomp 2.4.0", note="Renamed to truncn_floor.")]
Notation trunc_floor := truncn_floor.
#[deprecated(since="mathcomp 2.4.0", note="Renamed to real_floor_le.")]
Notation real_ge_floor := real_floor_le.
#[deprecated(since="mathcomp 2.4.0", note="Renamed to real_floorD1_gt.")]
Notation real_lt_succ_floor := real_floorD1_gt.
#[deprecated(since="mathcomp 2.4.0", note="Renamed to real_ceilB1_lt.")]
Notation real_gt_pred_ceil := real_floorD1_gt.
#[deprecated(since="mathcomp 2.4.0", note="Renamed to real_ceil_ge.")]
Notation real_le_ceil := real_ceil_ge.
#[deprecated(since="mathcomp 2.4.0", note="Renamed to le_floor.")]
Notation floor_le := le_floor.
#[deprecated(since="mathcomp 2.4.0", note="Renamed to le_ceil.")]
Notation ceil_le := le_ceil_tmp.
#[deprecated(since="mathcomp 2.4.0", note="Renamed to natrEtruncn.")]
Notation natrE := natrEtruncn.

Arguments natrK {R} _%_N.
Arguments intrKfloor {R}.
Arguments intrKceil {R}.
Arguments natrP {R x}.
Arguments intrP {R x}.
#[global] Hint Resolve truncn0 truncn1 : core.
#[global] Hint Resolve floor0 floor1 : core.
#[global] Hint Resolve ceil0 ceil1 : core.
#[global] Hint Extern 0 (is_true (_%:R \is a nat_num)) => apply: natr_nat : core.
#[global] Hint Extern 0 (is_true (_%:R \in nat_num_subdef)) => apply: natr_nat : core.
#[global] Hint Extern 0 (is_true (_%:~R \is a int_num)) => apply: intr_int : core.
#[global] Hint Extern 0 (is_true (_%:~R \in int_num_subdef)) => apply: intr_int : core.
#[global] Hint Extern 0 (is_true (_%:R \is a int_num)) => apply: natr_int : core.
#[global] Hint Extern 0 (is_true (_%:R \in int_num_subdef)) => apply: natr_int : core.
#[global] Hint Extern 0 (is_true (0 \is a nat_num)) => apply: nat_num0 : core.
#[global] Hint Extern 0 (is_true (0 \in nat_num_subdef)) => apply: nat_num0 : core.
#[global] Hint Extern 0 (is_true (1 \is a nat_num)) => apply: nat_num1 : core.
#[global] Hint Extern 0 (is_true (1 \in int_num_subdef)) => apply: nat_num1 : core.
#[global] Hint Extern 0 (is_true (0 \is a int_num)) => apply: int_num0 : core.
#[global] Hint Extern 0 (is_true (0 \in int_num_subdef)) => apply: int_num0 : core.
#[global] Hint Extern 0 (is_true (1 \is a int_num)) => apply: int_num1 : core.
#[global] Hint Extern 0 (is_true (1 \in int_num_subdef)) => apply: int_num1 : core.

Section ArchiRealDomainTheory.

Variables (R : archiRealDomainType).
Implicit Type x : R.

Lemma upper_nthrootP x i : (bound x <= i)%N -> x < 2%:R ^+ i.
Proof.
case/truncn_itv/andP: (normr_ge0 x) => _ /ltr_normlW xlt le_b_i.
by rewrite (lt_le_trans xlt) // -natrX ler_nat (ltn_trans le_b_i) // ltn_expl.
Qed.

Lemma truncnS_gt x : x < (truncn x).+1%:R.
Proof. exact: real_truncnS_gt. Qed.

Lemma truncn_le_nat x n : (truncn x <= n)%N = (x < n.+1%:R).
Proof. exact: real_truncn_le_nat. Qed.

Lemma floor_itv x : (floor x)%:~R <= x < (floor x + 1)%:~R.
Proof. exact: real_floor_itv. Qed.

(* TODO: rename to floor_le, once the deprecated one has been removed *)
Lemma floor_le_tmp x : (floor x)%:~R <= x. Proof. exact: real_floor_le. Qed.

Lemma floorD1_gt x : x < (floor x + 1)%:~R.
Proof. exact: real_floorD1_gt. Qed.

#[deprecated(since="mathcomp 2.4.0", note="Use floor_ge_int_tmp instead.")]
Lemma floor_ge_int x n : n%:~R <= x = (n <= floor x).
Proof. by rewrite real_floor_ge_int_tmp. Qed.

(* TODO: rename to floor_ge_int,
   once the currently deprecated one has been removed *)
Lemma floor_ge_int_tmp x n : (n <= floor x) = (n%:~R <= x).
Proof. exact: real_floor_ge_int_tmp. Qed.

Lemma floor_lt_int x n : (floor x < n) = (x < n%:~R).
Proof. exact: real_floor_lt_int. Qed.

Lemma floor_eq x n : (floor x == n) = (n%:~R <= x < (n + 1)%:~R).
Proof. exact: real_floor_eq. Qed.

Lemma floorDzr : {in @int_num R, {morph floor : x y / x + y}}.
Proof. by move=> x xz y; apply/real_floorDzr/num_real. Qed.

Lemma floorDrz x y : y \is a int_num -> floor (x + y) = floor x + floor y.
Proof. by move=> yz; apply/real_floorDrz/yz/num_real. Qed.

Lemma floor_ge0 x : (0 <= floor x) = (0 <= x).
Proof. exact: real_floor_ge0. Qed.

Lemma floor_le0 x : (floor x <= 0) = (x < 1).
Proof. exact: real_floor_le0. Qed.

Lemma ceil_itv x : (ceil x - 1)%:~R < x <= (ceil x)%:~R.
Proof. exact: real_ceil_itv. Qed.

Lemma ceilB1_lt x : (ceil x - 1)%:~R < x.
Proof. exact: real_ceilB1_lt. Qed.

Lemma ceil_ge x : x <= (ceil x)%:~R. Proof. exact: real_ceil_ge. Qed.

#[deprecated(since="mathcomp 2.4.0", note="Use ceil_le_int_tmp instead.")]
Lemma ceil_le_int x n : x <= n%:~R = (ceil x <= n).
Proof. by rewrite real_ceil_le_int_tmp. Qed.

(* TODO: rename to ceil_le_int,
   once the currently deprecated one has been removed *)
Lemma ceil_le_int_tmp x n : (ceil x <= n) = (x <= n%:~R).
Proof. exact: real_ceil_le_int_tmp. Qed.

Lemma ceil_gt_int x n : (n < ceil x) = (n%:~R < x).
Proof. exact: real_ceil_gt_int. Qed.

Lemma ceil_eq x n : (ceil x == n) = ((n - 1)%:~R < x <= n%:~R).
Proof. exact: real_ceil_eq. Qed.

Lemma ceilDzr : {in @int_num R, {morph ceil : x y / x + y}}.
Proof. by move=> x xz y; apply/real_ceilDzr/num_real. Qed.

Lemma ceilDrz x y : y \is a int_num -> ceil (x + y) = ceil x + ceil y.
Proof. by move=> yz; apply/real_ceilDrz/yz/num_real. Qed.

Lemma ceil_ge0 x : (0 <= ceil x) = (-1 < x).
Proof. exact: real_ceil_ge0. Qed.

Lemma ceil_le0 x : (ceil x <= 0) = (x <= 0).
Proof. exact: real_ceil_le0. Qed.

Lemma ceil_floor x : ceil x = floor x + (~~ (x \is a int_num)).
Proof. exact: real_ceil_floor. Qed.

End ArchiRealDomainTheory.

#[deprecated(since="mathcomp 2.4.0", note="Renamed to floor_le_tmp.")]
Notation ge_floor := floor_le_tmp.
#[deprecated(since="mathcomp 2.4.0", note="Renamed to floorD1_gt.")]
Notation lt_succ_floor := floorD1_gt.
#[deprecated(since="mathcomp 2.4.0", note="Renamed to ceilB1_lt.")]
Notation gt_pred_ceil := ceilB1_lt.
#[deprecated(since="mathcomp 2.4.0", note="Renamed to ceil_ge.")]
Notation le_ceil := ceil_ge.

Section ArchiNumFieldTheory.

(* autLmodC *)
Variables (R : archiNumFieldType) (nu : {rmorphism R -> R}).

Lemma natr_aut x : (nu x \is a nat_num) = (x \is a nat_num).
Proof. by apply/idP/idP=> /[dup] ? /(aut_natr nu) => [/fmorph_inj <-| ->]. Qed.

Lemma intr_aut x : (nu x \is a int_num) = (x \is a int_num).
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

Lemma Znat_def (n : int) : (n \is a nat_num) = (0 <= n).
Proof. by []. Qed.

Lemma ZnatP (m : int) : reflect (exists n : nat, m = n) (m \is a nat_num).
Proof. by case: m => m; constructor; [exists m | case]. Qed.

End ZnatPred.

End Theory.

(* Factories *)

HB.factory Record NumDomain_hasTruncn R of Num.NumDomain R := {
  trunc : R -> nat;
  nat_num : pred R;
  int_num : pred R;
  truncP : forall x,
    if 0 <= x then (trunc x)%:R <= x < (trunc x).+1%:R else trunc x == 0;
  natrE : forall x, nat_num x = ((trunc x)%:R == x);
  intrE : forall x, int_num x = nat_num x || nat_num (- x);
}.

Module NumDomain_isArchimedean.
Notation Build R := (NumDomain_hasTruncn.Build R).
End NumDomain_isArchimedean.

HB.builders Context R of NumDomain_hasTruncn R.

Fact trunc_itv x : 0 <= x -> (trunc x)%:R <= x < (trunc x).+1%:R.
Proof. by move=> x_ge0; move: (truncP x); rewrite x_ge0. Qed.

Definition floor (x : R) : int :=
  if 0 <= x then Posz (trunc x)
  else if x < 0 then - Posz (trunc (- x) + ~~ int_num x) else 0.

Fact floorP x :
  if x \is Rreal then (floor x)%:~R <= x < (floor x + 1)%:~R else floor x == 0.
Proof.
rewrite /floor intrE !natrE negb_or realE.
case: (comparableP x 0) (@trunc_itv x) => //=;
  try by rewrite -PoszD addn1 -pmulrn => _ ->.
move=> x_lt0 _; move: (truncP x); rewrite lt_geF // => /eqP ->.
rewrite gt_eqF //=; move: x_lt0.
rewrite [_ + 1]addrC -opprB !intrN lerNl ltrNr andbC -oppr_gt0.
move: {x}(- x) => x x_gt0; rewrite PoszD -addrA -PoszD.
have ->: Posz ((trunc x)%:R != x) - 1 = - Posz ((trunc x)%:R == x) by case: eqP.
have := trunc_itv (ltW x_gt0); rewrite le_eqVlt.
case: eqVneq => /=; last first.
  by rewrite subr0 addn1 -!pmulrn => _ /andP[-> /ltW ->].
by rewrite intrB mulr1z addn0 -!pmulrn => -> _; rewrite gtrBl lexx andbT.
Qed.

Fact truncE x : trunc x = if floor x is Posz n then n else 0.
Proof.
rewrite /floor.
case: (comparableP x 0) (truncP x) => [+ /eqP ->| |_ /eqP ->|] //=.
by case: (_ + _)%N.
Qed.

Fact trunc_def x n : n%:R <= x < n.+1%:R -> trunc x = n.
Proof.
case/andP=> lemx ltxm1; apply/eqP; rewrite eqn_leq -ltnS -[(n <= _)%N]ltnS.
have/trunc_itv/andP[lefx ltxf1]: 0 <= x by apply: le_trans lemx; apply: ler0n.
by rewrite -!(ltr_nat R) 2?(@le_lt_trans _ _ x).
Qed.

Fact natrK : cancel (GRing.natmul 1) trunc.
Proof. by move=> m; apply: trunc_def; rewrite ler_nat ltr_nat ltnS leqnn. Qed.

Fact intrP x : reflect (exists n, x = n%:~R) (int_num x).
Proof.
rewrite intrE !natrE; apply: (iffP idP) => [|[n ->]]; last first.
  by case: n => n; rewrite ?NegzE ?opprK natrK eqxx // orbT.
rewrite -eqr_oppLR !pmulrn -intrN.
by move=> /orP[] /eqP<-; [exists (trunc x) | exists (- Posz (trunc (- x)))].
Qed.

Fact natrP x : reflect (exists n, x = n%:R) (nat_num x).
Proof.
rewrite natrE.
by apply: (iffP eqP) => [<-|[n ->]]; [exists (trunc x) | rewrite natrK].
Qed.

HB.instance Definition _ :=
  @NumDomain_hasFloorCeilTruncn.Build R floor _ trunc int_num nat_num
    floorP (fun=> erefl) truncE intrP natrP.

HB.end.

HB.factory Record NumDomain_bounded_isArchimedean R of Num.NumDomain R := {
  archi_bound_subproof : Num.archimedean_axiom R
}.

HB.builders Context R of NumDomain_bounded_isArchimedean R.
  Implicit Type x : R.

  Definition bound x := sval (sigW (archi_bound_subproof x)).

  Lemma boundP x : 0 <= x -> x < (bound x)%:R.
  Proof. by move/ger0_norm=> {1}<-; rewrite /bound; case: (sigW _). Qed.

  Fact truncn_subproof x : {m | 0 <= x -> m%:R <= x < m.+1%:R }.
  Proof.
  have [Rx | _] := boolP (0 <= x); last by exists 0%N.
  have/ex_minnP[n lt_x_n1 min_n]: exists n, x < n.+1%:R.
    by exists (bound x); rewrite (lt_trans (boundP Rx)) ?ltr_nat.
  exists n => _; rewrite {}lt_x_n1 andbT; case: n min_n => //= n min_n.
  rewrite real_leNgt ?rpred_nat ?ger0_real //; apply/negP => /min_n.
  by rewrite ltnn.
  Qed.

  Definition truncn x := if 0 <= x then sval (truncn_subproof x) else 0%N.

  Lemma truncnP x :
    if 0 <= x then (truncn x)%:R <= x < (truncn x).+1%:R else truncn x == 0%N.
  Proof.
  rewrite /truncn; case: truncn_subproof => // n hn.
  by case: ifP => x_ge0; rewrite ?(ifT _ _ x_ge0) ?(ifF _ _ x_ge0) // hn.
  Qed.

  HB.instance Definition _ := NumDomain_hasTruncn.Build R
    truncnP (fun => erefl) (fun => erefl).
HB.end.

Module Exports. HB.reexport. End Exports.

(* Not to pollute the local namespace, we define Num.nat and Num.int here. *)
Notation nat := nat_num.
Notation int := int_num.

#[deprecated(since="mathcomp 2.3.0", note="Use Num.ArchiRealDomain instead.")]
Notation ArchiDomain T := (ArchiRealDomain T).
Module ArchiDomain.
#[deprecated(since="mathcomp 2.3.0",
  note="Use Num.ArchiRealDomain.type instead.")]
Notation type := ArchiRealDomain.type.
#[deprecated(since="mathcomp 2.3.0",
  note="Use Num.ArchiRealDomain.copy instead.")]
Notation copy T C := (ArchiRealDomain.copy T C).
#[deprecated(since="mathcomp 2.3.0",
  note="Use Num.ArchiRealDomain.on instead.")]
Notation on T := (ArchiRealDomain.on T).
End ArchiDomain.
#[deprecated(since="mathcomp 2.3.0", note="Use Num.ArchiRealField instead.")]
Notation ArchiField T := (ArchiRealField T).
Module ArchiField.
#[deprecated(since="mathcomp 2.3.0",
  note="Use Num.ArchiRealField.type instead.")]
Notation type := ArchiRealField.type.
#[deprecated(since="mathcomp 2.3.0",
  note="Use Num.ArchiRealField.copy instead.")]
Notation copy T C := (ArchiRealField.copy T C).
#[deprecated(since="mathcomp 2.3.0", note="Use Num.ArchiRealField.on instead.")]
Notation on T := (ArchiRealField.on T).
End ArchiField.

#[deprecated(since="mathcomp 2.3.0", note="Use real_floorDzr instead.")]
Notation floorD := real_floorDzr.
#[deprecated(since="mathcomp 2.3.0", note="Use real_ceilDzr instead.")]
Notation ceilD := real_ceilDzr.
#[deprecated(since="mathcomp 2.3.0", note="Use real_ceilDzr instead.")]
Notation real_ceilD := real_ceilDzr.

End Num.

Export Num.Exports.

#[deprecated(since="mathcomp 2.3.0", note="Use archiRealDomainType instead.")]
Notation archiDomainType := archiRealDomainType (only parsing).
#[deprecated(since="mathcomp 2.3.0", note="Use archiRealFieldType instead.")]
Notation archiFieldType := archiRealFieldType (only parsing).
