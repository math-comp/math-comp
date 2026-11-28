(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype bigop finset fingroup nmodule preorder.
From mathcomp Require Import porder lattice total_order total_order_instances.
From mathcomp Require Import interval rings_modules_and_algebras divalg poly.
From mathcomp Require Import orderedzmod orderedring.

(******************************************************************************)
(*                    Number structures (numdomain.v)                         *)
(*                                                                            *)
(* NB: See CONTRIBUTING.md for an introduction to HB concepts and commands.   *)
(*                                                                            *)
(* NB: The header of ssrnum.v explains how to use the files in this directory.*)
(*                                                                            *)
(* This file defines the following number structures:                         *)
(*                                                                            *)
(*  semiNormedZmodType == Zmodule with a semi-norm                            *)
(*                        The HB class is called SemiNormedZmodule.           *)
(*      normedZmodType == Zmodule with a norm                                 *)
(*                        The HB class is called NormedZmodule.               *)
(* subNormedZmodType S == join of normedZmodType M and subType (S : pred M)   *)
(*                        such that val preserves the norm                    *)
(*                        The HB class is called SubNormedZmodule.            *)
(*       numDomainType == Integral domain with an order and a norm            *)
(*                        The HB class is called NumDomain.                   *)
(*      realDomainType == Num domain where all elements are positive or       *)
(*                        negative                                            *)
(*                        The HB class is called RealDomain.                  *)
(*                                                                            *)
(* Over these structures, we have the following operations:                   *)
(*             `|x| == norm of x                                              *)
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

Import Order.Theory GRing.Theory.
Import orderedzmod.Num orderedring.Num.

Module Num.

HB.mixin Record Zmodule_isSemiNormed (R : POrderZmodule.type) M
         & GRing.Zmodule M := {
  norm : M -> R;
  ler_normD : forall x y, norm (x + y) <= norm x + norm y;
  normrMn : forall x n, norm (x *+ n) = norm x *+ n;
  normrN : forall x, norm (- x) = norm x;
}.

#[short(type="semiNormedZmodType")]
HB.structure Definition SemiNormedZmodule (R : porderZmodType) :=
  { M of Zmodule_isSemiNormed R M & GRing.Zmodule M }.

HB.mixin Record SemiNormedZmodule_isPositiveDefinite
    (R : POrderZmodule.type) M & @SemiNormedZmodule R M := {
  normr0_eq0 : forall x : M, norm x = 0 -> x = 0;
}.

#[short(type="normedZmodType")]
HB.structure Definition NormedZmodule (R : porderZmodType) :=
  { M of SemiNormedZmodule_isPositiveDefinite R M & SemiNormedZmodule R M }.
Arguments norm {R M} x : rename.

HB.mixin Record Zmodule_isSubNormed (R : porderZmodType) (M : normedZmodType R)
   (S : pred M) U & SubType M S U & NormedZmodule R U := {
  norm_valE : forall x : U, norm ((val : U -> M) x) = norm x
}.

#[short(type="subNormedZmodType")]
HB.structure Definition SubNormedZmodule (R : porderZmodType)
    (M : normedZmodType R) (S : pred M) :=
  { U of SubChoice M S U & Num.NormedZmodule R U & GRing.SubZmodule M S U
       & Zmodule_isSubNormed R M S U }.

HB.factory Record Zmodule_isNormed (R : porderZmodType) M
         & GRing.Zmodule M := {
  norm : M -> R;
  ler_normD : forall x y, norm (x + y) <= norm x + norm y;
  normr0_eq0 : forall x, norm x = 0 -> x = 0;
  normrMn : forall x n, norm (x *+ n) = norm x *+ n;
  normrN : forall x, norm (- x) = norm x;
}.
HB.builders Context (R : POrderZmodule.type) M & Zmodule_isNormed R M.
  HB.instance Definition _ :=
    Zmodule_isSemiNormed.Build R M ler_normD normrMn normrN.
  HB.instance Definition _ :=
    SemiNormedZmodule_isPositiveDefinite.Build R M normr0_eq0.
HB.end.

Module NormedZmoduleExports.
Bind Scope ring_scope with NormedZmodule.sort.
(* Notation "[ 'normedZmodType' R 'of' T 'for' cT ]" :=
  (@clone _ (Phant R) T cT _ idfun)
  (format "[ 'normedZmodType'  R  'of'  T  'for'  cT ]") :
  form_scope.
Notation "[ 'normedZmodType' R 'of' T ]" := (@clone _ (Phant R) T _ _ id)
  (format "[ 'normedZmodType'  R  'of'  T ]") : form_scope. *)
End NormedZmoduleExports.
HB.export NormedZmoduleExports.

HB.structure Definition POrderSemiNormedZmodule (R : porderZmodType) :=
  { M of POrderZmodule M & Zmodule_isSemiNormed R M}.

HB.structure Definition POrderNormedZmodule (R : porderZmodType) :=
  { M of POrderZmodule M & Zmodule_isNormed R M}.

HB.structure Definition POrderedSemiNormedZmodule (R : porderZmodType) :=
  { M of POrderedZmodule M & Zmodule_isSemiNormed R M}.

HB.structure Definition POrderedNormedZmodule (R : porderZmodType) :=
  { M of POrderedZmodule M & Zmodule_isNormed R M}.

HB.mixin Record NumZmod_isNumRing R & GRing.NzRing R & POrderZmodule R
  & NormedZmodule (POrderZmodule.clone R _) R := {
 addr_gt0 : forall x y : R, 0 < x -> 0 < y -> 0 < (x + y);
 ger_leVge : forall x y : R, 0 <= x -> 0 <= y -> (x <= y) || (y <= x);
 normrM : {morph (norm : R -> R) : x y / x * y};
 ler_def : forall x y : R, (x <= y) = (norm (y - x) == (y - x));
}.

#[short(type="numDomainType")]
HB.structure Definition NumDomain := { R of
  NumPOrderedIntegralDomain R &
  NormedZmodule (POrderZmodule.clone R _) R &
  NumZmod_isNumRing R
}.
Arguments addr_gt0 {_} [x y] : rename.
Arguments ger_leVge {_} [x y] : rename.

HB.factory Record isNumRing R & GRing.NzRing R & POrderZmodule R
  & GRing.IntegralDomain R
  & NormedZmodule (POrderZmodule.clone R _) R := {
 addr_gt0 : forall x y : R, 0 < x -> 0 < y -> 0 < (x + y);
 ger_leVge : forall x y : R, 0 <= x -> 0 <= y -> (x <= y) || (y <= x);
 normrM : {morph (norm : R -> R) : x y / x * y};
 ler_def : forall x y : R, (x <= y) = (norm (y - x) == (y - x));
}.
HB.builders Context R & isNumRing R.

Fact ler_wD2l (x : R) : {homo +%R x : y z / y <= z}.
Proof. by move=> y z; rewrite !ler_def ![_ + z]addrC addrKA. Qed.

HB.instance Definition _ := Add_isHomo.Build R ler_wD2l.

Fact real_nmod_closed : nmod_closed (@Num.real R).
Proof.
split=> [|x y Rx Ry]; first by rewrite realE lexx.
without loss{Rx} x_ge0: x y Ry / 0 <= x.
  case/orP: Rx => [? | x_le0]; first exact.
  by rewrite -rpredN opprD; apply; rewrite ?rpredN ?oppr_ge0.
case/orP: Ry => [y_ge0 | y_le0]; first by rewrite realE -nnegrE rpredD.
by rewrite realE -[y]opprK orbC -oppr_ge0 opprB !subr_ge0 ger_leVge ?oppr_ge0.
Qed.
HB.instance Definition _ := GRing.isAddClosed.Build R Num.real
  real_nmod_closed.

Fact comparabler_trans : transitive (Num.comparable : rel R).
Proof.
move=> y x z; rewrite !comparablerE => xBy_real yBz_real.
by have := rpredD xBy_real yBz_real; rewrite addrA addrNK.
Qed.

HB.instance Definition _ :=
  POrderedZmodule_hasTransCmp.Build R comparabler_trans.

Fact ler01 : 0 <= 1 :> R.
Proof.
have n1_nz: norm (1 : R) != 0.
  by apply: contraNneq (@oner_neq0 R) => /normr0_eq0->.
by rewrite ler_def subr0 -(inj_eq (mulfI n1_nz)) -normrM !mulr1.
Qed.

Fact mulr_ge0 (x y : R) : 0 <= x -> 0 <= y -> 0 <= x * y.
Proof. by rewrite !ler_def !subr0 normrM => /eqP-> /eqP->. Qed.

HB.instance Definition _ := Ring_isPOrdered.Build R ler01 mulr_ge0.

Fact mulr_gt0 (x y : R) : 0 < x -> 0 < y -> 0 < x * y.
Proof.
rewrite !lt_def => /andP[x0 x_ge0] /andP[y0 y_ge0].
by rewrite mulr_ge0 ?mulf_neq0.
Qed.

HB.instance Definition _ := POrderRing_isStrictPOrdered.Build R mulr_gt0.

Let realMr (x y : R) : x != 0 -> x \is real -> (x * y \is real) = (y \is real).
Proof.
rewrite !realE !ler_def !subr0 !add0r !normrN normrM => x0 /orP[] /eqP->.
- by rewrite -mulrN !(inj_eq (mulfI x0)).
- by rewrite mulNr eqr_oppLR eqr_opp -mulrN !(inj_eq (mulfI x0)) orbC.
Qed.

Let realrM (x y : R) : y != 0 -> y \is real -> (x * y \is real) = (x \is real).
Proof. by rewrite mulrC; exact: realMr. Qed.

HB.instance Definition _ := Ring_hasNumMul.Build R realMr realrM.

HB.instance Definition _ :=
  NumZmod_isNumRing.Build R addr_gt0 ger_leVge normrM ler_def.
HB.end.

Module NumDomainExports.
Bind Scope ring_scope with NumDomain.sort.
End NumDomainExports.
HB.export NumDomainExports.

#[short(type="realDomainType")]
HB.structure Definition RealDomain :=
  { R of Order.Total ring_display R & NumDomain R }.

Module RealDomainExports.
Bind Scope ring_scope with RealDomain.sort.
End RealDomainExports.
HB.export RealDomainExports.

Module Export Def.

Export Num.Def.

Notation normr := norm.
Notation "`| x |" := (norm x) : ring_scope.

End Def.

(* (Exported) symbolic syntax. *)
Module Export Syntax.

Notation "`| x |" := (norm x) : ring_scope.

End Syntax.

Section ExtensionAxioms.

Variable R : numDomainType.

Definition real_axiom : Prop := forall x : R, x \is real.

Definition archimedean_axiom : Prop := forall x : R, exists ub, `|x| < ub%:R.

Definition real_closed_axiom : Prop :=
  forall (p : {poly R}) (a b : R),
    a <= b -> p.[a] <= 0 <= p.[b] -> exists2 x, a <= x <= b & root p x.

End ExtensionAxioms.

(* The rest of the numbers interface hierarchy. *)

Module Export Theory.

Export Num.Theory.

Section NumIntegralDomainTheory.

Variable R : numDomainType.
Implicit Types (V : semiNormedZmodType R) (x y z t : R).
Implicit Types (W : normedZmodType R).

(* Lemmas from the signature (reexported). *)

Definition ler_normD V (x y : V) : `|x + y| <= `|x| + `|y| :=
  ler_normD x y.
Definition addr_gt0 x y : 0 < x -> 0 < y -> 0 < x + y := @addr_gt0 R x y.
Definition normr0_eq0 W (x : W) : `|x| = 0 -> x = 0 := @normr0_eq0 R W x.
Definition ger_leVge x y : 0 <= x -> 0 <= y -> (x <= y) || (y <= x) :=
  @ger_leVge R x y.
Definition normrM : {morph norm : x y / (x : R) * y} := @normrM R.
Definition ler_def x y : (x <= y) = (`|y - x| == y - x) := ler_def x y.
Definition normrMn V (x : V) n : `|x *+ n| = `|x| *+ n := normrMn x n.
Definition normrN V (x : V) : `|- x| = `|x| := normrN x.

Lemma ger0_def x : (0 <= x) = (`|x| == x).
Proof. by rewrite ler_def subr0. Qed.
Lemma normr_idP {x} : reflect (`|x| = x) (0 <= x).
Proof. by rewrite ger0_def; apply: eqP. Qed.
Lemma ger0_norm x : 0 <= x -> `|x| = x. Proof. exact: normr_idP. Qed.
Lemma normr1 : `|1 : R| = 1. Proof. exact: ger0_norm. Qed.
Lemma normr_nat n : `|n%:R : R| = n%:R. Proof. exact: ger0_norm. Qed.

Lemma normr_prod I r (P : pred I) (F : I -> R) :
  `|\prod_(i <- r | P i) F i| = \prod_(i <- r | P i) `|F i|.
Proof. exact: (big_morph norm normrM normr1). Qed.

Lemma normrX n x : `|x ^+ n| = `|x| ^+ n.
Proof. by rewrite -(card_ord n) -!prodr_const normr_prod. Qed.

Lemma normr_unit : {homo (@norm _ (* R *) R) : x / x \is a GRing.unit}.
Proof.
move=> x /= /unitrP [y [yx xy]]; apply/unitrP; exists `|y|.
by rewrite -!normrM xy yx normr1.
Qed.

Lemma normrV : {in GRing.unit, {morph (@norm _ (* R *) R) : x / x ^-1}}.
Proof.
move=> x ux; apply: (mulrI (normr_unit ux)).
by rewrite -normrM !divrr ?normr1 ?normr_unit.
Qed.

Lemma normrN1 : `|-1 : R| = 1.
Proof.
have: `|-1 : R| ^+ 2 == 1 by rewrite -normrX -signr_odd normr1.
rewrite sqrf_eq1 => /orP[/eqP //|]; rewrite -ger0_def le0r oppr_eq0 oner_eq0.
by move/(addr_gt0 ltr01); rewrite subrr ltxx.
Qed.

Section SemiNormedZmoduleTheory.

Variable V : semiNormedZmodType R.
Implicit Types (v w : V).

Lemma normr0 : `|0 : V| = 0.
Proof. by rewrite -(mulr0n 0) normrMn mulr0n. Qed.

Lemma distrC v w : `|v - w| = `|w - v|.
Proof. by rewrite -opprB normrN. Qed.

Lemma normr_id v : `| `|v| | = `|v|.
Proof.
have nz2: 2 != 0 :> R by rewrite pnatr_eq0.
apply: (mulfI nz2); rewrite -{1}normr_nat -normrM mulr_natl mulr2n ger0_norm //.
by rewrite -{2}normrN -normr0 -(subrr v) ler_normD.
Qed.

Lemma normr_ge0 v : 0 <= `|v|. Proof. by rewrite ger0_def normr_id. Qed.

Lemma normr_lt0 v : (`|v| < 0) = false.
Proof. by rewrite le_gtF// normr_ge0. Qed.

Lemma gtr0_norm_neq0 v : `|v| > 0 -> (v != 0).
Proof. by apply: contra_ltN => /eqP->; rewrite normr0. Qed.

Lemma gtr0_norm_eq0F v : `|v| > 0 -> (v == 0) = false.
Proof. by move=> /gtr0_norm_neq0/negPf->. Qed.

End SemiNormedZmoduleTheory.

Section NormedZmoduleTheory.

Variable V : normedZmodType R.
Implicit Types (v w : V).

Lemma normr0P v : reflect (`|v| = 0) (v == 0).
Proof. by apply: (iffP eqP)=> [->|/normr0_eq0 //]; apply: normr0. Qed.

Definition normr_eq0 v := sameP (`|v| =P 0) (normr0P v).

Lemma normr_le0 v : (`|v| <= 0) = (v == 0).
Proof. by rewrite -normr_eq0 eq_le normr_ge0 andbT. Qed.

Lemma normr_gt0 v : (`|v| > 0) = (v != 0).
Proof. by rewrite lt_def normr_eq0 normr_ge0 andbT. Qed.

End NormedZmoduleTheory.

Definition normrE := (normr_id, normr0, normr1, normrN1, normr_ge0, normr_eq0,
  normr_lt0, normr_le0, normr_gt0, normrN).

Lemma ler0_def x : (x <= 0) = (`|x| == - x).
Proof. by rewrite ler_def sub0r normrN. Qed.

Lemma ler0_norm x : x <= 0 -> `|x| = - x.
Proof. by move=> x_le0; rewrite -[r in _ = r]ger0_norm ?normrN ?oppr_ge0. Qed.

Definition gtr0_norm x (hx : 0 < x) := ger0_norm (ltW hx).
Definition ltr0_norm x (hx : x < 0) := ler0_norm (ltW hx).

Lemma ger0_le_norm :
  {in nneg &, {mono (@normr _ R) : x y / x <= y}}.
Proof. by move=> x y; rewrite !nnegrE => x0 y0; rewrite !ger0_norm. Qed.

Lemma gtr0_le_norm :
  {in pos &, {mono (@normr _ R) : x y / x <= y}}.
Proof. by move=> x y; rewrite !posrE => /ltW x0 /ltW y0; exact: ger0_le_norm. Qed.

Lemma ler0_ge_norm :
  {in npos &, {mono (@normr _ R) : x y / x <= y >-> x >= y}}.
Proof.
move=> x y; rewrite !nposrE => x0 y0.
by rewrite !ler0_norm// -[LHS]subr_ge0 opprK addrC subr_ge0.
Qed.

Lemma ltr0_ge_norm :
  {in neg &, {mono (@normr _ R) : x y / x <= y >-> x >= y}}.
Proof. by move=> x y; rewrite !negrE => /ltW x0 /ltW y0; exact: ler0_ge_norm. Qed.

End NumIntegralDomainTheory.

#[deprecated(since="mathcomp 2.4.0",use=pchar_num)]
Notation char_num := pchar_num (only parsing).

Arguments normr_idP {R x}.
Arguments normr0P {R V v}.
#[global] Hint Extern 0 (is_true (0 <= norm _)) => apply: normr_ge0 : core.

Lemma normr_nneg (R : numDomainType) (x : R) : `|x| \is Num.nneg.
Proof. by rewrite qualifE /=. Qed.
#[global] Hint Resolve normr_nneg : core.

Section NumDomainOperationTheory.

Variable R : numDomainType.
Implicit Types x y z t : R.

(* dichotomy and trichotomy *)

Variant ler_xor_gt (x y : R) : R -> R -> R -> R -> R -> R ->
    bool -> bool -> Set :=
  | LerNotGt of x <= y : ler_xor_gt x y x x y y (y - x) (y - x) true false
  | GtrNotLe of y < x  : ler_xor_gt x y y y x x (x - y) (x - y) false true.

Variant ltr_xor_ge (x y : R) : R -> R -> R -> R -> R -> R ->
    bool -> bool -> Set :=
  | LtrNotGe of x < y  : ltr_xor_ge x y x x y y (y - x) (y - x) false true
  | GerNotLt of y <= x : ltr_xor_ge x y y y x x (x - y) (x - y) true false.

Variant comparer x y : R -> R -> R -> R -> R -> R ->
    bool -> bool -> bool -> bool -> bool -> bool -> Set :=
  | ComparerLt of x < y : comparer x y x x y y (y - x) (y - x)
    false false false true false true
  | ComparerGt of x > y : comparer x y y y x x (x - y) (x - y)
    false false true false true false
  | ComparerEq of x = y : comparer x y x x x x 0 0
    true true true true false false.

Lemma real_leP x y : x \is real -> y \is real ->
  ler_xor_gt x y (min y x) (min x y) (max y x) (max x y)
                 `|x - y| `|y - x| (x <= y) (y < x).
Proof.
move=> xR yR; case: (comparable_leP (real_leVge xR yR)) => xy.
- by rewrite [`|x - y|]distrC !ger0_norm ?subr_cp0 //; constructor.
- by rewrite [`|y - x|]distrC !gtr0_norm ?subr_cp0 //; constructor.
Qed.

Lemma real_ltP x y : x \is real -> y \is real ->
  ltr_xor_ge x y (min y x) (min x y) (max y x) (max x y)
             `|x - y| `|y - x| (y <= x) (x < y).
Proof. by move=> xR yR; case: real_leP=> //; constructor. Qed.

Lemma real_ltgtP x y : x \is real -> y \is real ->
  comparer x y (min y x) (min x y) (max y x) (max x y) `|x - y| `|y - x|
               (y == x) (x == y) (x >= y) (x <= y) (x > y) (x < y).
Proof.
move=> xR yR; case: (comparable_ltgtP (real_leVge yR xR)) => [?|?|->].
- by rewrite [`|y - x|]distrC !gtr0_norm ?subr_gt0//; constructor.
- by rewrite [`|x - y|]distrC !gtr0_norm ?subr_gt0//; constructor.
- by rewrite subrr normr0; constructor.
Qed.

Variant ger0_xor_lt0 (x : R) : R -> R -> R -> R -> R ->
    bool -> bool -> Set :=
  | Ger0NotLt0 of 0 <= x : ger0_xor_lt0 x 0 0 x x x false true
  | Ltr0NotGe0 of x < 0  : ger0_xor_lt0 x x x 0 0 (- x) true false.

Variant ler0_xor_gt0 (x : R) : R -> R -> R -> R -> R ->
   bool -> bool -> Set :=
  | Ler0NotLe0 of x <= 0 : ler0_xor_gt0 x x x 0 0 (- x) false true
  | Gtr0NotGt0 of 0 < x  : ler0_xor_gt0 x 0 0 x x x true false.

Variant comparer0 x : R -> R -> R -> R -> R ->
    bool -> bool -> bool -> bool -> bool -> bool -> Set :=
  | ComparerGt0 of 0 < x : comparer0 x 0 0 x x x false false false true false true
  | ComparerLt0 of x < 0 : comparer0 x x x 0 0 (- x) false false true false true false
  | ComparerEq0 of x = 0 : comparer0 x 0 0 0 0 0 true true true true false false.

Lemma real_ge0P x : x \is real -> ger0_xor_lt0 x
   (min 0 x) (min x 0) (max 0 x) (max x 0)
  `|x| (x < 0) (0 <= x).
Proof.
move=> hx; rewrite -[X in `|X|]subr0; case: real_leP;
by rewrite ?subr0 ?sub0r //; constructor.
Qed.

Lemma real_le0P x : x \is real -> ler0_xor_gt0 x
  (min 0 x) (min x 0) (max 0 x) (max x 0)
  `|x| (0 < x) (x <= 0).
Proof.
move=> hx; rewrite -[X in `|X|]subr0; case: real_ltP;
by rewrite ?subr0 ?sub0r //; constructor.
Qed.

Lemma real_ltgt0P x : x \is real ->
  comparer0 x (min 0 x) (min x 0) (max 0 x) (max x 0)
            `|x| (0 == x) (x == 0) (x <= 0) (0 <= x) (x < 0) (x > 0).
Proof.
move=> hx; rewrite -[X in `|X|]subr0; case: (@real_ltgtP 0 x);
by rewrite ?subr0 ?sub0r //; constructor.
Qed.

Lemma real_distr_max_min :
  {in real &, forall x y, `|x - y| = max x y - min x y}.
Proof. by move=> x y x_real y_real; case: real_leP. Qed.

Lemma minr_pMr x y z : 0 <= x -> x * min y z = min (x * y) (x * z).
Proof.
have [|x_gt0||->]// := comparableP x; last by rewrite !mul0r minxx.
by rewrite !(fun_if, if_arg) lter_pM2l//; case: (y < z).
Qed.

Lemma real_maxrN x : x \is real -> max x (- x) = `|x|.
Proof.
move=> x_real; rewrite /max.
by case: real_ge0P => // [/ge0_cp [] | /lt0_cp []];
   case: (@real_leP (- x) x); rewrite ?realN.
Qed.

Lemma real_maxNr x : x \is real -> max (- x) x = `|x|.
Proof.
by move=> x_real; rewrite comparable_maxC ?real_maxrN ?real_comparable ?realN.
Qed.

Lemma real_minrN x : x \is real -> min x (- x) = - `|x|.
Proof.
by move=> x_real; rewrite -[LHS]opprK real_oppr_min ?opprK ?real_maxNr ?realN.
Qed.

Lemma real_minNr x : x \is real ->  min (- x) x = - `|x|.
Proof.
by move=> x_real; rewrite -[LHS]opprK real_oppr_min ?opprK ?real_maxrN ?realN.
Qed.

(* norm *)

Lemma real_ler_norm x : x \is real -> x <= `|x|.
Proof.
by case/real_ge0P=> hx //; rewrite (le_trans (ltW hx)) // oppr_ge0 ltW.
Qed.

(* norm + add *)

Section NormedZmoduleTheory.

Variable V : semiNormedZmodType R.
Implicit Types (u v w : V).

Lemma normr_real v : `|v| \is real. Proof. by apply/ger0_real. Qed.
Hint Resolve normr_real : core.

Lemma ler_norm_sum I r (G : I -> V) (P : pred I):
  `|\sum_(i <- r | P i) G i| <= \sum_(i <- r | P i) `|G i|.
Proof.
elim/big_rec2: _ => [|i y x _]; first by rewrite normr0.
by rewrite -(lerD2l `|G i|); apply: le_trans; apply: ler_normD.
Qed.

Lemma ler_normB v w : `|v - w| <= `|v| + `|w|.
Proof. by rewrite (le_trans (ler_normD _ _)) ?normrN. Qed.

Lemma ler_distD u v w : `|v - w| <= `|v - u| + `|u - w|.
Proof. by rewrite (le_trans _ (ler_normD _ _)) // addrA addrNK. Qed.

Lemma lerB_normD v w : `|v| - `|w| <= `|v + w|.
Proof.
by rewrite -{1}[v](addrK w) lterBDl (le_trans (ler_normD _ _))// addrC normrN.
Qed.

Lemma lerB_dist v w : `|v| - `|w| <= `|v - w|.
Proof. by rewrite -[`|w|]normrN lerB_normD. Qed.

Lemma ler_dist_dist v w : `| `|v| - `|w| | <= `|v - w|.
Proof.
have [||_|_] // := @real_leP `|v| `|w|; last by rewrite lerB_dist.
by rewrite distrC lerB_dist.
Qed.

Lemma ler_dist_normD v w : `| `|v| - `|w| | <= `|v + w|.
Proof. by rewrite -[w]opprK normrN ler_dist_dist. Qed.

Lemma ler_nnorml v x : x < 0 -> (`|v| <= x) = false.
Proof. by move=> h; rewrite lt_geF //; apply/(lt_le_trans h). Qed.

Lemma ltr_nnorml v x : x <= 0 -> (`|v| < x) = false.
Proof. by move=> h; rewrite le_gtF //; apply/(le_trans h). Qed.

Definition lter_nnormr := (ler_nnorml, ltr_nnorml).

End NormedZmoduleTheory.

Hint Extern 0 (is_true (norm _ \is real)) => apply: normr_real : core.

Lemma real_ler_norml x y : x \is real -> (`|x| <= y) = (- y <= x <= y).
Proof.
move=> xR; wlog x_ge0 : x xR / 0 <= x => [hwlog|].
  move: (xR) => /(@real_leVge _ 0) /orP [|/hwlog->|hx] //.
  by rewrite -[x]opprK normrN lerN2 andbC lerNl hwlog ?realN ?oppr_ge0.
rewrite ger0_norm //; have [le_xy|] := boolP (x <= y); last by rewrite andbF.
by rewrite (le_trans _ x_ge0) // oppr_le0 (le_trans x_ge0).
Qed.

Lemma real_ler_normlP x y :
  x \is real -> reflect ((-x <= y) * (x <= y)) (`|x| <= y).
Proof.
by move=> Rx; rewrite real_ler_norml // lerNl; apply: (iffP andP) => [] [].
Qed.
Arguments real_ler_normlP {x y}.

Lemma real_eqr_norml x y :
  x \is real -> (`|x| == y) = ((x == y) || (x == -y)) && (0 <= y).
Proof.
move=> Rx.
apply/idP/idP=> [|/andP[/pred2P[]-> /ger0_norm/eqP]]; rewrite ?normrE //.
case: real_le0P => // hx; rewrite 1?eqr_oppLR => /eqP exy.
  by move: hx; rewrite exy ?oppr_le0 eqxx orbT //.
by move: hx=> /ltW; rewrite exy eqxx.
Qed.

Lemma real_eqr_norm2 x y :
  x \is real -> y \is real -> (`|x| == `|y|) = (x == y) || (x == -y).
Proof.
move=> Rx Ry; rewrite real_eqr_norml // normrE andbT.
by case: real_le0P; rewrite // opprK orbC.
Qed.

Lemma real_ltr_norml x y : x \is real -> (`|x| < y) = (- y < x < y).
Proof.
move=> Rx; wlog x_ge0 : x Rx / 0 <= x => [hwlog|].
  move: (Rx) => /(@real_leVge _ 0) /orP [|/hwlog->|hx] //.
  by rewrite -[x]opprK normrN ltrN2 andbC ltrNl hwlog ?realN ?oppr_ge0.
rewrite ger0_norm //; have [le_xy|] := boolP (x < y); last by rewrite andbF.
by rewrite (lt_le_trans _ x_ge0) // oppr_lt0 (le_lt_trans x_ge0).
Qed.

Definition real_lter_norml := (real_ler_norml, real_ltr_norml).

Lemma real_ltr_normlP x y :
  x \is real -> reflect ((-x < y) * (x < y)) (`|x| < y).
Proof.
by move=> Rx; rewrite real_ltr_norml // ltrNl; apply: (iffP (@andP _ _)); case.
Qed.
Arguments real_ltr_normlP {x y}.

Lemma real_ler_normr x y : y \is real -> (x <= `|y|) = (x <= y) || (x <= - y).
Proof.
move=> Ry.
have [xR|xNR] := boolP (x \is real); last by rewrite ?Nreal_leF ?realN.
rewrite real_leNgt ?real_ltr_norml // negb_and -?real_leNgt ?realN //.
by rewrite orbC lerNr.
Qed.

Lemma real_ltr_normr x y : y \is real -> (x < `|y|) = (x < y) || (x < - y).
Proof.
move=> Ry.
have [xR|xNR] := boolP (x \is real); last by rewrite ?Nreal_ltF ?realN.
rewrite real_ltNge ?real_ler_norml // negb_and -?real_ltNge ?realN //.
by rewrite orbC ltrNr.
Qed.

Definition real_lter_normr := (real_ler_normr, real_ltr_normr).

Lemma real_ltr_normlW x y : x \is real -> `|x| < y -> x < y.
Proof. by move=> ?; case/real_ltr_normlP. Qed.

Lemma real_ltrNnormlW x y : x \is real -> `|x| < y -> - y < x.
Proof. by move=> ?; case/real_ltr_normlP => //; rewrite ltrNl. Qed.

Lemma real_ler_normlW x y : x \is real -> `|x| <= y -> x <= y.
Proof. by move=> ?; case/real_ler_normlP. Qed.

Lemma real_lerNnormlW x y : x \is real -> `|x| <= y -> - y <= x.
Proof. by move=> ?; case/real_ler_normlP => //; rewrite lerNl. Qed.

Lemma real_ler_distl x y e :
  x - y \is real -> (`|x - y| <= e) = (y - e <= x <= y + e).
Proof. by move=> Rxy; rewrite real_lter_norml // !lterBDl. Qed.

Lemma real_ltr_distl x y e :
  x - y \is real -> (`|x - y| < e) = (y - e < x < y + e).
Proof. by move=> Rxy; rewrite real_lter_norml // !lterBDl. Qed.

Definition real_lter_distl := (real_ler_distl, real_ltr_distl).

Lemma real_ltr_distlDr x y e : x - y \is real -> `|x - y| < e -> x < y + e.
Proof. by move=> ?; rewrite real_ltr_distl // => /andP[]. Qed.

Lemma real_ler_distlDr x y e : x - y \is real -> `|x - y| <= e -> x <= y + e.
Proof. by move=> ?; rewrite real_ler_distl // => /andP[]. Qed.

Lemma real_ltr_distlCDr x y e : x - y \is real -> `|x - y| < e -> y < x + e.
Proof. by rewrite realBC (distrC x) => ? /real_ltr_distlDr; apply. Qed.

Lemma real_ler_distlCDr x y e : x - y \is real -> `|x - y| <= e -> y <= x + e.
Proof. by rewrite realBC distrC => ? /real_ler_distlDr; apply. Qed.

Lemma real_ltr_distlBl x y e : x - y \is real -> `|x - y| < e -> x - e < y.
Proof. by move/real_ltr_distlDr; rewrite ltrBlDr; apply. Qed.

Lemma real_ler_distlBl x y e : x - y \is real -> `|x - y| <= e -> x - e <= y.
Proof. by move/real_ler_distlDr; rewrite lerBlDr; apply. Qed.

Lemma real_ltr_distlCBl x y e : x - y \is real -> `|x - y| < e -> y - e < x.
Proof. by rewrite realBC distrC => ? /real_ltr_distlBl; apply. Qed.

Lemma real_ler_distlCBl x y e : x - y \is real -> `|x - y| <= e -> y - e <= x.
Proof. by rewrite realBC distrC => ? /real_ler_distlBl; apply. Qed.

#[deprecated(since="mathcomp 2.3.0", use=ger0_def)]
Lemma eqr_norm_id x : (`|x| == x) = (0 <= x). Proof. by rewrite ger0_def. Qed.

#[deprecated(since="mathcomp 2.3.0", use=ler0_def)]
Lemma eqr_normN x : (`|x| == - x) = (x <= 0). Proof. by rewrite ler0_def. Qed.

Definition eqr_norm_idVN := =^~ (ger0_def, ler0_def).

Lemma realEsqr x : (x \is real) = (0 <= x ^+ 2).
Proof. by rewrite ger0_def normrX eqf_sqr -ger0_def -ler0_def. Qed.

Lemma real_normK x : x \is real -> `|x| ^+ 2 = x ^+ 2.
Proof. by move=> Rx; rewrite -normrX ger0_norm -?realEsqr. Qed.

(* Binary sign ((-1) ^+ s). *)

Lemma normr_sign s : `|(-1) ^+ s : R| = 1.
Proof. by rewrite normrX normrN1 expr1n. Qed.

Lemma normrMsign s x : `|(-1) ^+ s * x| = `|x|.
Proof. by rewrite normrM normr_sign mul1r. Qed.

(* sign and norm *)

Lemma realEsign x : x \is real -> x = (-1) ^+ (x < 0)%R * `|x|.
Proof. by case/real_ge0P; rewrite (mul1r, mulN1r) ?opprK. Qed.

Lemma realNEsign x : x \is real -> - x = (-1) ^+ (0 < x)%R * `|x|.
Proof. by move=> Rx; rewrite -normrN -oppr_lt0 -realEsign ?rpredN. Qed.

Lemma real_normrEsign (x : R) (xR : x \is real) : `|x| = (-1) ^+ (x < 0)%R * x.
Proof. by rewrite {3}[x]realEsign // signrMK. Qed.

#[deprecated(since="mathcomp 2.3.0", use=realEsign)]
Lemma real_mulr_sign_norm x : x \is real -> (-1) ^+ (x < 0)%R * `|x| = x.
Proof. by move/realEsign. Qed.

Lemma real_mulr_Nsign_norm x : x \is real -> (-1) ^+ (0 < x)%R * `|x| = - x.
Proof. by move/realNEsign. Qed.

Lemma realEsg x : x \is real -> x = sgr x * `|x|.
Proof.
move=> xR; have [-> | ] := eqVneq x 0; first by rewrite normr0 mulr0.
by move=> /neqr0_sign <-; rewrite -realEsign.
Qed.

Lemma normr_sg x : `|sg x| = (x != 0)%:R.
Proof. by rewrite sgr_def -mulr_natr normrMsign normr_nat. Qed.

Lemma sgr_norm x : sg `|x| = (x != 0)%:R.
Proof. by rewrite /sg le_gtF // normr_eq0 mulrb if_neg. Qed.

(* leif/lteif with norm *)

Lemma real_leif_norm x : x \is real -> x <= `|x| ?= iff (0 <= x).
Proof.
by move=> xR; rewrite ger0_def eq_sym; apply: leif_eq; rewrite real_ler_norm.
Qed.

Lemma lteif_nnormr C x y : y < 0 ?<= if ~~ C -> (`|x| < y ?<= if C) = false.
Proof. by case: C => ?; rewrite /= lter_nnormr. Qed.

Lemma real_lteif_norml C x y :
  x \is Num.real ->
  (`|x| < y ?<= if C) = ((- y < x ?<= if C) && (x < y ?<= if C)).
Proof. by case: C => ?; rewrite /= real_lter_norml. Qed.

Lemma real_lteif_normr C x y :
  y \is Num.real ->
  (x < `|y| ?<= if C) = ((x < y ?<= if C) || (x < - y ?<= if C)).
Proof. by case: C => ?; rewrite /= real_lter_normr. Qed.

Lemma real_lteif_distl C x y e :
  x - y \is real ->
  (`|x - y| < e ?<= if C) = (y - e < x ?<= if C) && (x < y + e ?<= if C).
Proof. by case: C => /= ?; rewrite real_lter_distl. Qed.

(* Polynomial bound. *)

Implicit Type p : {poly R}.

Lemma poly_disk_bound p b : {ub | forall x, `|x| <= b -> `|p.[x]| <= ub}.
Proof.
exists (\sum_(j < size p) `|p`_j| * b ^+ j) => x le_x_b.
rewrite horner_coef (le_trans (ler_norm_sum _ _ _)) ?ler_sum // => j _.
rewrite normrM normrX ler_wpM2l ?lerXn2r ?unfold_in //=.
exact: le_trans (normr_ge0 x) le_x_b.
Qed.

End NumDomainOperationTheory.

#[global] Hint Resolve normr_real : core.

Arguments real_ler_normlP {R x y}.
Arguments real_ltr_normlP {R x y}.

Section RealDomainTheory.

Variable R : realDomainType.
Implicit Types x y z t : R.

Lemma lerP x y : ler_xor_gt x y (min y x) (min x y) (max y x) (max x y)
                                `|x - y| `|y - x| (x <= y) (y < x).
Proof. exact: real_leP. Qed.

Lemma ltrP x y : ltr_xor_ge x y (min y x) (min x y) (max y x) (max x y)
                                `|x - y| `|y - x| (y <= x) (x < y).
Proof. exact: real_ltP. Qed.

Lemma ltrgtP x y :
   comparer x y  (min y x) (min x y) (max y x) (max x y)
                 `|x - y| `|y - x| (y == x) (x == y)
                 (x >= y) (x <= y) (x > y) (x < y) .
Proof. exact: real_ltgtP. Qed.

Lemma ger0P x : ger0_xor_lt0 x (min 0 x) (min x 0) (max 0 x) (max x 0)
                                `|x| (x < 0) (0 <= x).
Proof. exact: real_ge0P. Qed.

Lemma ler0P x : ler0_xor_gt0 x (min 0 x) (min x 0) (max 0 x) (max x 0)
                                `|x| (0 < x) (x <= 0).
Proof. exact: real_le0P. Qed.

Lemma ltrgt0P x : comparer0 x (min 0 x) (min x 0) (max 0 x) (max x 0)
  `|x| (0 == x) (x == 0) (x <= 0) (0 <= x) (x < 0) (x > 0).
Proof. exact: real_ltgt0P. Qed.

(* sign & norm *)

Lemma mulr_sign_norm x : (-1) ^+ (x < 0)%R * `|x| = x.
Proof. by rewrite -realEsign. Qed.

Lemma mulr_Nsign_norm x : (-1) ^+ (0 < x)%R * `|x| = - x.
Proof. by rewrite real_mulr_Nsign_norm. Qed.

Lemma numEsign x : x = (-1) ^+ (x < 0)%R * `|x|.
Proof. by rewrite -realEsign. Qed.

Lemma numNEsign x : -x = (-1) ^+ (0 < x)%R * `|x|.
Proof. by rewrite -realNEsign. Qed.

Lemma normrEsign x : `|x| = (-1) ^+ (x < 0)%R * x.
Proof. by rewrite -real_normrEsign. Qed.

End RealDomainTheory.

#[global] Hint Resolve num_real : core.

Section RealDomainOperations.

Notation "[ 'arg' 'min_' ( i < i0 | P ) F ]" :=
    (Order.arg_min (disp := ring_display) i0 (fun i => P%B) (fun i => F)) :
   ring_scope.

Notation "[ 'arg' 'min_' ( i < i0 'in' A ) F ]" :=
  [arg min_(i < i0 | i \in A) F] : ring_scope.

Notation "[ 'arg' 'min_' ( i < i0 ) F ]" := [arg min_(i < i0 | true) F] :
  ring_scope.

Notation "[ 'arg' 'max_' ( i > i0 | P ) F ]" :=
   (Order.arg_max (disp := ring_display) i0 (fun i => P%B) (fun i => F)) :
  ring_scope.

Notation "[ 'arg' 'max_' ( i > i0 'in' A ) F ]" :=
    [arg max_(i > i0 | i \in A) F] : ring_scope.

Notation "[ 'arg' 'max_' ( i > i0 ) F ]" := [arg max_(i > i0 | true) F] :
  ring_scope.

(* sgr section *)

Variable R : realDomainType.
Implicit Types x y z t : R.
Let numR_real := @num_real R.
Hint Resolve numR_real : core.

Variant sgr_val x : R -> bool -> bool -> bool -> bool -> bool -> bool
  -> bool -> bool -> bool -> bool -> bool -> bool -> R -> Set :=
  | SgrNull of x = 0 : sgr_val x 0 true true true true false false
    true false false true false false 0
  | SgrPos of x > 0 : sgr_val x x false false true false false true
    false false true false false true 1
  | SgrNeg of x < 0 : sgr_val x (- x) false true false false true false
    false true false false true false (-1).

Lemma sgrP x :
  sgr_val x `|x| (0 == x) (x <= 0) (0 <= x) (x == 0) (x < 0) (0 < x)
                 (0 == sg x) (-1 == sg x) (1 == sg x)
                 (sg x == 0)  (sg x == -1) (sg x == 1) (sg x).
Proof.
by rewrite ![_ == sg _]eq_sym !sgr_cp0 /sg; case: ltrgt0P; constructor.
Qed.

Lemma normrEsg x : `|x| = sg x * x.
Proof. by case: sgrP; rewrite ?(mul0r, mul1r, mulN1r). Qed.

Lemma numEsg x : x = sg x * `|x|.
Proof. by case: sgrP; rewrite !(mul1r, mul0r, mulrNN). Qed.

#[deprecated(since="mathcomp 2.3.0", use=numEsg)]
Lemma mulr_sg_norm x : sg x * `|x| = x. Proof. by rewrite -numEsg. Qed.

(* norm section *)

Lemma ler_norm x : (x <= `|x|).
Proof. exact: real_ler_norm. Qed.

Lemma ler_norml x y : (`|x| <= y) = (- y <= x <= y).
Proof. exact: real_ler_norml. Qed.

Lemma ler_normlP x y : reflect ((- x <= y) * (x <= y)) (`|x| <= y).
Proof. exact: real_ler_normlP. Qed.
Arguments ler_normlP {x y}.

Lemma eqr_norml x y : (`|x| == y) = ((x == y) || (x == -y)) && (0 <= y).
Proof. exact: real_eqr_norml. Qed.

Lemma eqr_norm2 x y : (`|x| == `|y|) = (x == y) || (x == -y).
Proof. exact: real_eqr_norm2. Qed.

Lemma ltr_norml x y : (`|x| < y) = (- y < x < y).
Proof. exact: real_ltr_norml. Qed.

Definition lter_norml := (ler_norml, ltr_norml).

Lemma ltr_normlP x y : reflect ((-x < y) * (x < y)) (`|x| < y).
Proof. exact: real_ltr_normlP. Qed.
Arguments ltr_normlP {x y}.

Lemma ltr_normlW x y : `|x| < y -> x < y. Proof. exact: real_ltr_normlW. Qed.

Lemma ltrNnormlW x y : `|x| < y -> - y < x. Proof. exact: real_ltrNnormlW. Qed.

Lemma ler_normlW x y : `|x| <= y -> x <= y. Proof. exact: real_ler_normlW. Qed.

Lemma lerNnormlW x y : `|x| <= y -> - y <= x. Proof. exact: real_lerNnormlW. Qed.

Lemma ler_normr x y : (x <= `|y|) = (x <= y) || (x <= - y).
Proof. exact: real_ler_normr. Qed.

Lemma ltr_normr x y : (x < `|y|) = (x < y) || (x < - y).
Proof. exact: real_ltr_normr. Qed.

Definition lter_normr := (ler_normr, ltr_normr).

Lemma ler_distl x y e : (`|x - y| <= e) = (y - e <= x <= y + e).
Proof. exact: real_ler_distl. Qed.

Lemma ltr_distl x y e : (`|x - y| < e) = (y - e < x < y + e).
Proof. exact: real_ltr_distl. Qed.

Definition lter_distl := (ler_distl, ltr_distl).

Lemma ltr_distlC x y e : (`|x - y| < e) = (x - e < y < x + e).
Proof. by rewrite distrC ltr_distl. Qed.

Lemma ler_distlC x y e : (`|x - y| <= e) = (x - e <= y <= x + e).
Proof. by rewrite distrC ler_distl. Qed.

Definition lter_distlC := (ler_distlC, ltr_distlC).

Lemma ltr_distlDr x y e : `|x - y| < e -> x < y + e.
Proof. exact: real_ltr_distlDr. Qed.

Lemma ler_distlDr x y e : `|x - y| <= e -> x <= y + e.
Proof. exact: real_ler_distlDr. Qed.

Lemma ltr_distlCDr x y e : `|x - y| < e -> y < x + e.
Proof. exact: real_ltr_distlCDr. Qed.

Lemma ler_distlCDr x y e : `|x - y| <= e -> y <= x + e.
Proof. exact: real_ler_distlCDr. Qed.

Lemma ltr_distlBl x y e : `|x - y| < e -> x - e < y.
Proof. exact: real_ltr_distlBl. Qed.

Lemma ler_distlBl x y e : `|x - y| <= e -> x - e <= y.
Proof. exact: real_ler_distlBl. Qed.

Lemma ltr_distlCBl x y e : `|x - y| < e -> y - e < x.
Proof. exact: real_ltr_distlCBl. Qed.

Lemma ler_distlCBl x y e : `|x - y| <= e -> y - e <= x.
Proof. exact: real_ler_distlCBl. Qed.

(* lteif *)

Lemma lteif_norml C x y :
  (`|x| < y ?<= if C) = (- y < x ?<= if C) && (x < y ?<= if C).
Proof. by case: C; rewrite /= lter_norml. Qed.

Lemma lteif_normr C x y :
  (x < `|y| ?<= if C) = (x < y ?<= if C) || (x < - y ?<= if C).
Proof. by case: C; rewrite /= lter_normr. Qed.

Lemma lteif_distl C x y e :
  (`|x - y| < e ?<= if C) = (y - e < x ?<= if C) && (x < y + e ?<= if C).
Proof. by case: C; rewrite /= lter_distl. Qed.

Lemma sqr_norm_eq1 x : (x ^+ 2 == 1) = (`|x| == 1).
Proof. by rewrite sqrf_eq1 eqr_norml ler01 andbT. Qed.

Section MinMax.

Lemma distr_max_min x y : `|x - y| = max x y - min x y.
Proof. exact: real_distr_max_min. Qed.

Lemma maxrN x : max x (- x) = `|x|.   Proof. exact: real_maxrN. Qed.
Lemma maxNr x : max (- x) x = `|x|.   Proof. exact: real_maxNr. Qed.
Lemma minrN x : min x (- x) = - `|x|. Proof. exact: real_minrN. Qed.
Lemma minNr x : min (- x) x = - `|x|. Proof. exact: real_minNr. Qed.

End MinMax.

Section PolyBounds.

Variable p : {poly R}.

Lemma poly_itv_bound a b : {ub | forall x, a <= x <= b -> `|p.[x]| <= ub}.
Proof.
have [ub le_p_ub] := poly_disk_bound p (Num.max `|a| `|b|).
exists ub => x /andP[le_a_x le_x_b]; rewrite le_p_ub // le_max !ler_normr.
by have [_|_] := ler0P x; rewrite ?lerN2 ?le_a_x ?le_x_b orbT.
Qed.

Lemma monic_Cauchy_bound : p \is monic -> {b | forall x, x >= b -> p.[x] > 0}.
Proof.
move/monicP=> mon_p; pose n := (size p - 2)%N.
have [p_le1 | p_gt1] := leqP (size p) 1.
  exists 0 => x _; rewrite (size1_polyC p_le1) hornerC.
  by rewrite -[p`_0]lead_coefC -size1_polyC // mon_p ltr01.
pose lb := \sum_(j < n.+1) `|p`_j|; exists (lb + 1) => x le_ub_x.
have x_ge1: 1 <= x; last have x_gt0 := lt_le_trans ltr01 x_ge1.
  by rewrite -(lerD2l lb) ler_wpDl ?sumr_ge0 // => j _.
rewrite horner_coef -(subnK p_gt1) -/n addnS big_ord_recr /= addn1.
rewrite [in p`__]subnSK // subn1 -lead_coefE mon_p mul1r -ltrBlDl sub0r.
apply: le_lt_trans (_ : lb * x ^+ n < _); last first.
  by rewrite exprS ltr_pM2r ?exprn_gt0// -(ltrD2r 1) ltr_pwDr.
rewrite -sumrN mulr_suml ler_sum // => j _; apply: le_trans (ler_norm _) _.
rewrite normrN normrM ler_wpM2l // normrX.
by rewrite ger0_norm ?(ltW x_gt0) // ler_weXn2l ?leq_ord.
Qed.

End PolyBounds.

End RealDomainOperations.
End Theory.

HB.factory Record IntegralDomain_isNumRing R & GRing.IntegralDomain R := {
  Rle : rel R;
  Rlt : rel R;
  norm : R -> R;
  normD     : forall x y, Rle (norm (x + y)) (norm x + norm y);
  addr_gt0  : forall x y, Rlt 0 x -> Rlt 0 y -> Rlt 0 (x + y);
  norm_eq0  : forall x, norm x = 0 -> x = 0;
  ger_total : forall x y, Rle 0 x -> Rle 0 y -> Rle x y || Rle y x;
  normM     : {morph norm : x y / x * y};
  le_def    : forall x y, (Rle x y) = (norm (y - x) == y - x);
  lt_def    : forall x y, (Rlt x y) = (y != x) && (Rle x y)
}.

HB.builders Context R & IntegralDomain_isNumRing R.
  Local Notation "x <= y" := (Rle x y) : ring_scope.
  Local Notation "x < y" := (Rlt x y) : ring_scope.
  Local Notation "`| x |" := (norm x) : ring_scope.

  Lemma ltrr x : (x < x) = false. Proof. by rewrite lt_def eqxx. Qed.

  Lemma ge0_def x : (0 <= x) = (`|x| == x).
  Proof. by rewrite le_def subr0. Qed.

  Lemma subr_ge0 x y : (0 <= x - y) = (y <= x).
  Proof. by rewrite ge0_def -le_def. Qed.

  Lemma subr_gt0 x y : (0 < y - x) = (x < y).
  Proof. by rewrite !lt_def subr_eq0 subr_ge0. Qed.

  Lemma lt_trans : transitive Rlt.
  Proof.
  move=> y x z le_xy le_yz.
  by rewrite -subr_gt0 -(subrK y z) -addrA addr_gt0 // subr_gt0.
  Qed.

  Lemma le01 : 0 <= 1.
  Proof.
  have n1_nz: `|1| != 0 :> R by apply: contraNneq (@oner_neq0 R) => /norm_eq0->.
  by rewrite ge0_def -(inj_eq (mulfI n1_nz)) -normM !mulr1.
  Qed.

  Lemma lt01 : 0 < 1.
  Proof. by rewrite lt_def oner_neq0 le01. Qed.

  Lemma ltW x y : x < y -> x <= y. Proof. by rewrite lt_def => /andP[]. Qed.

  Lemma lerr x : x <= x.
  Proof.
  have n2: `|2| == 2 :> R by rewrite -ge0_def ltW ?addr_gt0 ?lt01.
  rewrite le_def subrr -(inj_eq (addrI `|0|)) addr0 -mulr2n -mulr_natr.
  by rewrite -(eqP n2) -normM mul0r.
  Qed.

  Lemma le_def' x y : (x <= y) = (x == y) || (x < y).
  Proof. by rewrite lt_def; case: eqVneq => //= ->; rewrite lerr. Qed.

  Lemma le_trans : transitive Rle.
  Proof.
  by move=> y x z; rewrite !le_def' => /predU1P [->|hxy] // /predU1P [<-|hyz];
    rewrite ?hxy ?(lt_trans hxy hyz) orbT.
  Qed.

  Lemma normrMn x n : `|x *+ n| = `|x| *+ n.
  Proof.
  rewrite -mulr_natr -[RHS]mulr_natr normM.
  congr (_ * _); apply/eqP; rewrite -ge0_def.
  elim: n => [|n ih]; [exact: lerr | apply: (le_trans ih)].
  by rewrite le_def -natrB // subSnn -[_%:R]subr0 -le_def mulr1n le01.
  Qed.

  Lemma normrN1 : `|-1| = 1 :> R.
  Proof.
  have: `|-1| ^+ 2 == 1 :> R
    by rewrite expr2 /= -normM mulrNN mul1r -[1]subr0 -le_def le01.
  rewrite sqrf_eq1 => /predU1P [] //; rewrite -[-1]subr0 -le_def.
  have ->: (0 <= -1) = (-1 == 0 :> R) || (0 < -1)
    by rewrite lt_def; case: eqP => // ->; rewrite lerr.
  by rewrite oppr_eq0 oner_eq0 => /(addr_gt0 lt01); rewrite subrr ltrr.
  Qed.

  Lemma normrN x : `|- x| = `|x|.
  Proof. by rewrite -mulN1r normM -[RHS]mul1r normrN1. Qed.

  HB.instance Definition _ :=
    Order.LtLe_isPOrder.Build ring_display R le_def' ltrr lt_trans.

  HB.instance Definition _ :=
    @Zmodule_isNormed.Build _ R norm normD norm_eq0 normrMn normrN.

  HB.instance Definition _ :=
    isNumRing.Build R addr_gt0 ger_total normM le_def.
HB.end.

HB.factory Record NumDomain_isReal R & NumDomain R := {
  real : real_axiom R
}.

HB.builders Context R & NumDomain_isReal R.
  Lemma le_total : Order.POrder_isTotal ring_display R.
  Proof.
  constructor=> x y; move: (real (x - y)).
  by rewrite unfold_in /= !ler_def subr0 add0r opprB orbC.
  Qed.

  HB.instance Definition _ := le_total.
HB.end.

HB.factory Record IntegralDomain_isLeReal R & GRing.IntegralDomain R := {
  Rle : rel R;
  Rlt : rel R;
  norm : R -> R;
  le0_add   : forall x y, Rle 0 x -> Rle 0 y -> Rle 0 (x + y);
  le0_mul   : forall x y, Rle 0 x -> Rle 0 y -> Rle 0 (x * y);
  le0_anti  : forall x, Rle 0 x -> Rle x 0 -> x = 0;
  sub_ge0   : forall x y, Rle 0 (y - x) = Rle x y;
  le0_total : forall x, Rle 0 x || Rle x 0;
  normN     : forall x, norm (- x) = norm x;
  ge0_norm  : forall x, Rle 0 x -> norm x = x;
  lt_def    : forall x y, Rlt x y = (y != x) && Rle x y;
}.

HB.builders Context R & IntegralDomain_isLeReal R.
  Local Notation le := Rle.
  Local Notation lt := Rlt.

  Local Notation "x <= y" := (le x y) : ring_scope.
  Local Notation "x < y" := (lt x y) : ring_scope.
  Local Notation "`| x |" := (norm x) : ring_scope.

  Let le0N x : (0 <= - x) = (x <= 0). Proof. by rewrite -sub0r sub_ge0. Qed.
  Let leN_total x : 0 <= x \/ 0 <= - x.
  Proof. by apply/orP; rewrite le0N le0_total. Qed.

  Let le00 : 0 <= 0. Proof. by have:= le0_total 0; rewrite orbb. Qed.

  Fact lt0_add x y : 0 < x -> 0 < y -> 0 < x + y.
  Proof.
  rewrite !lt_def => /andP [x_neq0 l0x] /andP [y_neq0 l0y]; rewrite le0_add //.
  rewrite andbT addr_eq0; apply: contraNneq x_neq0 => hxy.
  by rewrite [x](@le0_anti) // hxy -le0N opprK.
  Qed.

  Fact eq0_norm x : `|x| = 0 -> x = 0.
  Proof.
  case: (leN_total x) => /ge0_norm => [-> // | Dnx nx0].
  by rewrite -[x]opprK -Dnx normN nx0 oppr0.
  Qed.

  Fact le_def x y : (x <= y) = (`|y - x| == y - x).
  Proof.
  wlog ->: x y / x = 0 by move/(_ 0 (y - x)); rewrite subr0 sub_ge0 => ->.
  rewrite {x}subr0; apply/idP/eqP=> [/ge0_norm// | Dy].
  by have [//| ny_ge0] := leN_total y; rewrite -Dy -normN ge0_norm.
  Qed.

  Fact normM : {morph norm : x y / x * y}.
  Proof.
  move=> x y /=; wlog x_ge0 : x / 0 <= x.
    by move=> IHx; case: (leN_total x) => /IHx//; rewrite mulNr !normN.
  wlog y_ge0 : y / 0 <= y; last by rewrite ?ge0_norm ?le0_mul.
  by move=> IHy; case: (leN_total y) => /IHy//; rewrite mulrN !normN.
  Qed.

  Fact le_normD x y : `|x + y| <= `|x| + `|y|.
  Proof.
  wlog x_ge0 : x y / 0 <= x.
    by move=> IH; case: (leN_total x) => /IH// /(_ (- y)); rewrite -opprD !normN.
  rewrite -sub_ge0 ge0_norm //; have [y_ge0 | ny_ge0] := leN_total y.
    by rewrite !ge0_norm ?subrr ?le0_add.
  rewrite -normN ge0_norm //; have [hxy|hxy] := leN_total (x + y).
    by rewrite ge0_norm // [x - y]addrC addrKA le0_add.
  by rewrite -normN ge0_norm // opprK addrCA addrNK le0_add.
  Qed.

  Fact le_total : total le.
  Proof. by move=> x y; rewrite -sub_ge0 -opprB le0N orbC -sub_ge0 le0_total. Qed.

  HB.instance Definition _ := IntegralDomain_isNumRing.Build R
    le_normD lt0_add eq0_norm (in2W le_total) normM le_def lt_def.

  HB.instance Definition _ := Order.POrder_isTotal.Build ring_display R
    le_total.
HB.end.

HB.factory Record IntegralDomain_isLtReal R & GRing.IntegralDomain R := {
  Rlt : rel R;
  Rle : rel R;
  norm : R -> R;
  lt0_add   : forall x y, Rlt 0 x -> Rlt 0 y -> Rlt 0 (x + y);
  lt0_mul   : forall x y, Rlt 0 x -> Rlt 0 y -> Rlt 0 (x * y);
  lt0_ngt0  : forall x,  Rlt 0 x -> ~~ (Rlt x 0);
  sub_gt0   : forall x y, Rlt 0 (y - x) = Rlt x y;
  lt0_total : forall x, x != 0 -> Rlt 0 x || Rlt x 0;
  normN     : forall x, norm (- x) = norm x;
  ge0_norm  : forall x, Rle 0 x -> norm x = x;
  le_def    : forall x y, Rle x y = (x == y) || Rlt x y;
}.

HB.builders Context R & IntegralDomain_isLtReal R.
  Local Notation le := Rle.
  Local Notation lt := Rlt.

  Local Notation "x < y" := (lt x y) : ring_scope.
  Local Notation "x <= y" := (le x y) : ring_scope.
  Local Notation "`| x |" := (norm x) : ring_scope.

  Fact lt0N x : (- x < 0) = (0 < x).
  Proof. by rewrite -sub_gt0 add0r opprK. Qed.
  Let leN_total x : 0 <= x \/ 0 <= - x.
  Proof.
  rewrite !le_def [_ == - x]eq_sym oppr_eq0 -[0 < - x]lt0N opprK.
  apply/orP; case: (eqVneq x) => //=; exact: lt0_total.
  Qed.

  Let le00 : (0 <= 0). Proof. by rewrite le_def eqxx. Qed.

  Fact sub_ge0 x y : (0 <= y - x) = (x <= y).
  Proof. by rewrite !le_def eq_sym subr_eq0 eq_sym sub_gt0. Qed.

  Fact le0_add x y : 0 <= x -> 0 <= y -> 0 <= x + y.
  Proof.
  rewrite !le_def => /predU1P [<-|x_gt0]; first by rewrite add0r.
  by case/predU1P=> [<-|y_gt0]; rewrite ?addr0 ?x_gt0 ?lt0_add // orbT.
  Qed.

  Fact le0_mul x y : 0 <= x -> 0 <= y -> 0 <= x * y.
  Proof.
  rewrite !le_def => /predU1P [<-|x_gt0]; first by rewrite mul0r eqxx.
  by case/predU1P=> [<-|y_gt0]; rewrite ?mulr0 ?eqxx ?lt0_mul // orbT.
  Qed.

  Fact normM : {morph norm : x y / x * y}.
  Proof.
  move=> x y /=; wlog x_ge0 : x / 0 <= x.
    by move=> IHx; case: (leN_total x) => /IHx//; rewrite mulNr !normN.
  wlog y_ge0 : y / 0 <= y; last by rewrite ?ge0_norm ?le0_mul.
  by move=> IHy; case: (leN_total y) => /IHy//; rewrite mulrN !normN.
  Qed.

  Fact le_normD x y : `|x + y| <= `|x| + `|y|.
  Proof.
  wlog x_ge0 : x y / 0 <= x.
    by move=> IH; case: (leN_total x) => /IH// /(_ (- y)); rewrite -opprD !normN.
  rewrite -sub_ge0 ge0_norm //; have [y_ge0 | ny_ge0] := leN_total y.
    by rewrite !ge0_norm ?subrr ?le0_add.
  rewrite -normN ge0_norm //; have [hxy|hxy] := leN_total (x + y).
    by rewrite ge0_norm // [x - y]addrC addrKA le0_add.
  by rewrite -normN ge0_norm // opprK addrCA addrNK le0_add.
  Qed.

  Fact eq0_norm x : `|x| = 0 -> x = 0.
  Proof.
  case: (leN_total x) => /ge0_norm => [-> // | Dnx nx0].
  by rewrite -[x]opprK -Dnx normN nx0 oppr0.
  Qed.

  Fact le_def' x y : (x <= y) = (`|y - x| == y - x).
  Proof.
  wlog ->: x y / x = 0 by move/(_ 0 (y - x)); rewrite subr0 sub_ge0 => ->.
  rewrite {x}subr0; apply/idP/eqP=> [/ge0_norm// | Dy].
  by have [//| ny_ge0] := leN_total y; rewrite -Dy -normN ge0_norm.
  Qed.

  Fact lt_def x y : (x < y) = (y != x) && (x <= y).
  Proof.
  rewrite le_def; case: eqVneq => //= ->; rewrite -sub_gt0 subrr.
  by apply/idP=> lt00; case/negP: (lt0_ngt0 lt00).
  Qed.

  Fact le_total : total le.
  Proof.
  move=> x y; rewrite !le_def; have [->|] //= := eqVneq; rewrite -subr_eq0.
  by move/lt0_total; rewrite -(sub_gt0 (x - y)) sub0r opprB !sub_gt0 orbC.
  Qed.

  HB.instance Definition _ := IntegralDomain_isNumRing.Build R
    le_normD lt0_add eq0_norm (in2W le_total) normM le_def' lt_def.

  HB.instance Definition _ := Order.POrder_isTotal.Build ring_display R
    le_total.
HB.end.

Module Exports. HB.reexport. End Exports.
End Num.
Export Num.Exports Num.Syntax.
