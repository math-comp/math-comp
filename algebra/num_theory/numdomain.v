(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import ssrAC div fintype path bigop order finset fingroup.
From mathcomp Require Import ssralg poly orderedzmod.

(******************************************************************************)
(*                            Number structures                               *)
(*                                                                            *)
(* NB: See CONTRIBUTING.md for an introduction to HB concepts and commands.   *)
(*                                                                            *)
(* This file defines some classes to manipulate number structures, i.e,       *)
(* structures with an order and a norm. To use this file, insert              *)
(* "Import Num.Theory." before your scripts. You can also "Import Num.Def."   *)
(* to enjoy shorter notations (e.g., minr instead of Num.min, lerif instead   *)
(* of Num.leif, etc.).                                                        *)
(*                                                                            *)
(* This file defines the following number structures:                         *)
(*                                                                            *)
(*  porderZmodType == join of Order.POrder and GRing.Zmodule                  *)
(*                    The HB class is called POrderedZmodule.                 *)
(*  semiNormedZmodType == Zmodule with a semi-norm                            *)
(*                        The HB class is called SemiNormedZmodule.           *)
(*  normedZmodType == Zmodule with a norm                                     *)
(*                    The HB class is called NormedZmodule.                   *)
(*   numDomainType == Integral domain with an order and a norm                *)
(*                    The HB class is called NumDomain.                       *)
(*                                                                            *)
(* The ordering symbols and notations (<, <=, >, >=, _ <= _ ?= iff _,         *)
(* _ < _ ?<= if _, >=<, and ><) and lattice operations (meet and join)        *)
(* defined in order.v are redefined for the ring_display in the ring_scope    *)
(* (%R). 0-ary ordering symbols for the ring_display have the suffix "%R",    *)
(* e.g., <%R. All the other ordering notations are the same as order.v.       *)
(*                                                                            *)
(* Over these structures, we have the following operations:                   *)
(*             `|x| == norm of x                                              *)
(*         Num.sg x == sign of x: equal to 0 iff x = 0, to 1 iff x > 0, and   *)
(*                     to -1 in all other cases (including x < 0)             *)
(*  x \is a Num.pos <=> x is positive (:= x > 0)                              *)
(*  x \is a Num.neg <=> x is negative (:= x < 0)                              *)
(* x \is a Num.nneg <=> x is positive or 0 (:= x >= 0)                        *)
(* x \is a Num.npos <=> x is negative or 0 (:= x <= 0)                        *)
(* x \is a Num.real <=> x is real (:= x >= 0 or x < 0)                        *)
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

Reserved Notation "n .-root" (at level 2, format "n .-root").
Reserved Notation "'i" (at level 0).
Reserved Notation "'Re z" (at level 10, z at level 8).
Reserved Notation "'Im z" (at level 10, z at level 8).

Local Open Scope order_scope.
Local Open Scope ring_scope.

Import Order.TTheory GRing.Theory.
Import orderedzmod.Num.

Module Num.

(* 
HB.mixin Record Zmodule_isSemiPseudoNormed (R : POrderedZmodule.type) M
         of GRing.Zmodule M := {
  enorm : M -> \bar R;
  ler_normD : forall x y, norm (x + y) <= norm x + norm y;
  normrMn : forall x n, norm (x *+ n) = norm x *+ n;
  normrN : forall x, norm (- x) = norm x;
}. *)

HB.mixin Record Zmodule_isSemiNormed (R : POrderZmodule.type) M
         of GRing.Zmodule M := {
  norm : M -> R;
  ler_normD : forall x y, norm (x + y) <= norm x + norm y;
  normrMn : forall x n, norm (x *+ n) = norm x *+ n;
  normrN : forall x, norm (- x) = norm x;
}.

#[short(type="semiNormedZmodType")]
HB.structure Definition SemiNormedZmodule (R : porderZmodType) :=
  { M of Zmodule_isSemiNormed R M & GRing.Zmodule M }.

(* HB.factory Record Zmodule_isSemiNormed (R : POrderedZmodule.type) M
         of GRing.Zmodule M := {
  norm : M -> R;
  ler_normD : forall x y, norm (x + y) <= norm x + norm y;
  normrMn : forall x n, norm (x *+ n) = norm x *+ n;
  normrN : forall x, norm (- x) = norm x;
}.

HB.builders Context R M of Zmodule_isSemiNormed R M.


Fact real_addr_closed : addr_closed (@real R).
Proof.
split=> [|x y Rx Ry]; first by rewrite realE lexx.
without loss{Rx} x_ge0: x y Ry / 0 <= x.
  case/orP: Rx => [? | x_le0]; first exact.
  by rewrite -rpredN opprD; apply; rewrite ?rpredN ?oppr_ge0.
case/orP: Ry => [y_ge0 | y_le0]; first by rewrite realE -nnegrE rpredD.
rewrite realE -[y]opprK orbC -oppr_ge0 opprB !subr_ge0.
rewrite ger_leVge.
rewrite ?oppr_ge0.
Qed. *)
(* 
HB.instance Definition _ := GRing.isAddClosed.Build R Rreal_pred
  real_addr_closed.
 

Lemma  comparabler_trans : transitive (comparable : rel R).
Proof.
move=> y x z; rewrite !comparablerE => xBy_real yBz_real.

have := rpredD xBy_real yBz_real; rewrite addrA addrNK.
Qed. *)

(* HB.end. *)


HB.mixin Record SemiNormedZmodule_isPositiveDefinite
    (R : POrderZmodule.type) M of @SemiNormedZmodule R M := {
  normr0_eq0 : forall x : M, norm x = 0 -> x = 0;
}.

#[short(type="normedZmodType")]
HB.structure Definition NormedZmodule (R : porderZmodType) :=
  { M of SemiNormedZmodule_isPositiveDefinite R M & SemiNormedZmodule R M }.
Arguments norm {R M} x : rename.

HB.factory Record Zmodule_isNormed (R : porderZmodType) M
         of GRing.Zmodule M := {
  norm : M -> R;
  ler_normD : forall x y, norm (x + y) <= norm x + norm y;
  normr0_eq0 : forall x, norm x = 0 -> x = 0;
  normrMn : forall x n, norm (x *+ n) = norm x *+ n;
  normrN : forall x, norm (- x) = norm x;
}.
HB.builders Context (R : POrderZmodule.type) M of Zmodule_isNormed R M.
  HB.instance Definition _ :=
    Zmodule_isSemiNormed.Build R M ler_normD normrMn normrN.
  HB.instance Definition _ :=
    SemiNormedZmodule_isPositiveDefinite.Build R M normr0_eq0.
HB.end.

Module NormedZmoduleExports.
Bind Scope ring_scope with NormedZmodule.sort.
(* Notation "[ 'normedZmodType' R 'of' T 'for' cT ]" :=
  (@clone _ (Phant R) T cT _ idfun)
  (at level 0, format "[ 'normedZmodType'  R  'of'  T  'for'  cT ]") :
  form_scope.
Notation "[ 'normedZmodType' R 'of' T ]" := (@clone _ (Phant R) T _ _ id)
  (at level 0, format "[ 'normedZmodType'  R  'of'  T ]") : form_scope. *)
End NormedZmoduleExports.
HB.export NormedZmoduleExports.

HB.mixin Record NumZmod_isNumRing R of GRing.NzRing R & POrderZmodule R
  & NormedZmodule (POrderZmodule.clone R _) R := {
 addr_gt0 : forall x y : R, 0 < x -> 0 < y -> 0 < (x + y);
 ger_leVge : forall x y : R, 0 <= x -> 0 <= y -> (x <= y) || (y <= x);
 normrM : {morph (norm : R -> R) : x y / x * y};
 ler_def : forall x y : R, (x <= y) = (norm (y - x) == (y - x));
}.

#[short(type="numDomainType")]
HB.structure Definition NumDomain := { R of
     GRing.IntegralDomain R &
     NumZmodule R &
     NormedZmodule (POrderedZmodule.clone R _) R &
     NumZmod_isNumRing R
  }.
Arguments addr_gt0 {_} [x y] : rename.
Arguments ger_leVge {_} [x y] : rename.

HB.factory Record isNumRing R of GRing.NzRing R & POrderZmodule R
  & GRing.IntegralDomain R
  & NormedZmodule (POrderZmodule.clone R _) R := {
 addr_gt0 : forall x y : R, 0 < x -> 0 < y -> 0 < (x + y);
 ger_leVge : forall x y : R, 0 <= x -> 0 <= y -> (x <= y) || (y <= x);
 normrM : {morph (norm : R -> R) : x y / x * y};
 ler_def : forall x y : R, (x <= y) = (norm (y - x) == (y - x));
}.
HB.builders Context R of isNumRing R.

Fact lerD2l (x : R) : {mono +%R x : y z / y <= z}.
Proof. by move=> y z; rewrite !ler_def ![_ + z]addrC addrKA. Qed.

HB.instance Definition _ := Add_isMono.Build R lerD2l.

Fact real_addr_closed : addr_closed (@Num.real R).
Proof.
split=> [|x y Rx Ry]; first by rewrite realE lexx.
without loss{Rx} x_ge0: x y Ry / 0 <= x.
  case/orP: Rx => [? | x_le0]; first exact.
  by rewrite -rpredN opprD; apply; rewrite ?rpredN ?oppr_ge0.
case/orP: Ry => [y_ge0 | y_le0]; first by rewrite realE -nnegrE rpredD.
by rewrite realE -[y]opprK orbC -oppr_ge0 opprB !subr_ge0 ger_leVge ?oppr_ge0.
Qed.

HB.instance Definition _ := GRing.isAddClosed.Build R Num.real
  real_addr_closed.
 
Fact comparabler_trans : transitive (Num.comparable : rel R).
Proof.
move=> y x z; rewrite !comparablerE => xBy_real yBz_real.
by have := rpredD xBy_real yBz_real; rewrite addrA addrNK.
Qed.

HB.instance Definition _ :=
  POrderedZmodule_hasTransCmp.Build R comparabler_trans.

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

Notation normr := norm.
Notation "`| x |" := (norm x) : ring_scope.

Section NumDomainDef.
Context {R : numDomainType}.

Definition sgr (x : R) : R := if x == 0 then 0 else if x < 0 then -1 else 1.

End NumDomainDef.

End Def.

Notation sg := sgr.

(* (Exported) symbolic syntax. *)
Module Export Syntax.

Notation "`| x |" := (norm x) : ring_scope.

Export Order.POCoercions.

End Syntax.

Section ExtensionAxioms.

Variable R : numDomainType.

Definition real_axiom : Prop := forall x : R, x \is Num.real.

Definition archimedean_axiom : Prop := forall x : R, exists ub, `|x| < ub%:R.

Definition real_closed_axiom : Prop :=
  forall (p : {poly R}) (a b : R),
    a <= b -> p.[a] <= 0 <= p.[b] -> exists2 x, a <= x <= b & root p x.

End ExtensionAxioms.

(* The rest of the numbers interface hierarchy. *)

(* The elementary theory needed to support the definition of the derived      *)
(* operations for the extensions described above.                             *)
Module Import Internals.

Section NumDomain.
Variable R : numDomainType.
Implicit Types x y : R.

(* Basic consequences (just enough to get predicate closure properties). *)

Lemma ger0_def x : (0 <= x) = (`|x| == x).
Proof. by rewrite ler_def subr0. Qed.

Lemma ler01 : 0 <= 1 :> R.
Proof.
have n1_nz: `|1 : R| != 0 by apply: contraNneq (@oner_neq0 R) => /normr0_eq0->.
by rewrite ger0_def -(inj_eq (mulfI n1_nz)) -normrM !mulr1.
Qed.

Lemma ltr01 : 0 < 1 :> R. Proof. by rewrite lt_def oner_neq0 ler01. Qed.

Definition lter01 := (ler01, ltr01).

Lemma pmulr_rgt0 x y : 0 < x -> (0 < x * y) = (0 < y).
Proof.
rewrite !lt_def !ger0_def normrM mulf_eq0 negb_or => /andP[x_neq0 /eqP->].
by rewrite x_neq0 (inj_eq (mulfI x_neq0)).
Qed.

(* Closure properties of the real predicates. *)

Fact pos_divr_closed : divr_closed (@Num.pos R).
Proof.
split=> [|x y x_gt0 y_gt0]; rewrite posrE ?ltr01 //.
have [Uy|/invr_out->] := boolP (y \is a GRing.unit); last by rewrite pmulr_rgt0.
by rewrite -(pmulr_rgt0 _ y_gt0) mulrC divrK.
Qed.
#[export]
HB.instance Definition _ := GRing.isDivClosed.Build R Rpos_pred
  pos_divr_closed.

Fact nneg_divr_closed : divr_closed (@Num.nneg R).
Proof.
split=> [|x y]; rewrite !nnegrE ?ler01 ?le0r // -!posrE.
case/predU1P=> [-> _ | x_gt0]; first by rewrite mul0r eqxx.
by case/predU1P=> [-> | y_gt0]; rewrite ?invr0 ?mulr0 ?eqxx // orbC rpred_div.
Qed.
#[export]
HB.instance Definition _ := GRing.isDivClosed.Build R Rnneg_pred
  nneg_divr_closed.


Fact real_divr_closed : divr_closed (@Num.real R).
Proof.
split=> [|x y Rx Ry]; first by rewrite realE ler01.
without loss{Rx} x_ge0: x / 0 <= x.
  case/orP: Rx => [? | x_le0]; first exact.
  by rewrite -rpredN -mulNr; apply; rewrite ?oppr_ge0.
without loss{Ry} y_ge0: y / 0 <= y; last by rewrite realE -nnegrE rpred_div.
case/orP: Ry => [? | y_le0]; first exact.
by rewrite -rpredN -mulrN -invrN; apply; rewrite ?oppr_ge0.
Qed.
#[export]
HB.instance Definition _ := GRing.isDivClosed.Build R Rreal_pred
  real_divr_closed.

End NumDomain.

Lemma num_real (R : realDomainType) (x : R) : x \is Num.real.
Proof. exact: le_total. Qed.

Module Exports. HB.reexport. End Exports.

End Internals.

Module PredInstances.

Export Internals.Exports.

End PredInstances.

Module Export Theory.

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


(* General properties of <= and < *)

Lemma pmulr_rgt0 x y : 0 < x -> (0 < x * y) = (0 < y).
Proof. exact: pmulr_rgt0. Qed.

Lemma pmulr_rge0 x y : 0 < x -> (0 <= x * y) = (0 <= y).
Proof. by move=> x_gt0; rewrite !le0r mulf_eq0 pmulr_rgt0 // gt_eqF. Qed.

(* Integer comparisons and characteristic 0. *)
Lemma ler01 : 0 <= 1 :> R. Proof. exact: ler01. Qed.
Lemma ltr01 : 0 < 1 :> R. Proof. exact: ltr01. Qed.
Definition lter01 := lter01.
Lemma ler0n n : 0 <= n%:R :> R. Proof. by rewrite -nnegrE rpred_nat. Qed.
Hint Extern 0 (is_true (@Order.le ring_display _ _ _)) =>
  (apply: ler01) : core.
Hint Extern 0 (is_true (@Order.lt ring_display _ _ _)) =>
  (apply: ltr01) : core.
Hint Extern 0 (is_true (@Order.le ring_display _ _ _)) =>
  (apply: ler0n) : core.
Lemma ltr0Sn n : 0 < n.+1%:R :> R.
Proof. by elim: n => // n; apply: addr_gt0. Qed.
Lemma ltr0n n : (0 < n%:R :> R) = (0 < n)%N.
Proof. by case: n => //= n; apply: ltr0Sn. Qed.
Hint Extern 0 (is_true (@Order.lt ring_display _ _ _)) =>
  (apply: ltr0Sn) : core.

Lemma pnatr_eq0 n : (n%:R == 0 :> R) = (n == 0)%N.
Proof. by case: n => [|n]; rewrite ?mulr0n ?eqxx // gt_eqF. Qed.

Lemma char_num : [char R] =i pred0.
Proof. by case=> // p /=; rewrite !inE pnatr_eq0 andbF. Qed.

(* Properties of the norm. *)

Lemma ger0_def x : (0 <= x) = (`|x| == x). Proof. exact: ger0_def. Qed.
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

Lemma prod_real I (P : pred I) (F : I -> R) (s : seq I) :
  {in P, forall i, F i \is Num.real} -> \prod_(i <- s | P i) F i \is Num.real.
Proof. by apply/big_real; [apply: rpredM | apply: rpred1]. Qed.

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

Lemma normr_lt0 v : `|v| < 0 = false.
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

Lemma normr_le0 v : `|v| <= 0 = (v == 0).
Proof. by rewrite -normr_eq0 eq_le normr_ge0 andbT. Qed.

Lemma normr_gt0 v : `|v| > 0 = (v != 0).
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
  {in Num.nneg &, {mono (@normr _ R) : x y / x <= y}}.
Proof. by move=> x y; rewrite !nnegrE => x0 y0; rewrite !ger0_norm. Qed.

Lemma gtr0_le_norm :
  {in Num.pos &, {mono (@normr _ R) : x y / x <= y}}.
Proof. by move=> x y; rewrite !posrE => /ltW x0 /ltW y0; exact: ger0_le_norm. Qed.

Lemma ler0_ge_norm :
  {in Num.npos &, {mono (@normr _ R) : x y / x <= y >-> x >= y}}.
Proof.
move=> x y; rewrite !nposrE => x0 y0.
by rewrite !ler0_norm// -[LHS]subr_ge0 opprK addrC subr_ge0.
Qed.

Lemma ltr0_ge_norm :
  {in Num.neg &, {mono (@normr _ R) : x y / x <= y >-> x >= y}}.
Proof. by move=> x y; rewrite !negrE => /ltW x0 /ltW y0; exact: ler0_ge_norm. Qed.

End NumIntegralDomainTheory.

Arguments ler01 {R}.
Arguments ltr01 {R}.
Arguments normr_idP {R x}.
Arguments normr0P {R V v}.
#[global] Hint Extern 0 (is_true (@Order.le ring_display _ _ _)) =>
  (apply: ler01) : core.
#[global] Hint Extern 0 (is_true (@Order.lt ring_display _ _ _)) =>
  (apply: ltr01) : core.
#[global] Hint Extern 0 (is_true (@Order.le ring_display _ _ _)) =>
  (apply: ler0n) : core.
#[global] Hint Extern 0 (is_true (@Order.lt ring_display _ _ _)) =>
  (apply: ltr0Sn) : core.
#[global] Hint Extern 0 (is_true (0 <= norm _)) => apply: normr_ge0 : core.

Lemma normr_nneg (R : numDomainType) (x : R) : `|x| \is Num.nneg.
Proof. by rewrite qualifE /=. Qed.
#[global] Hint Resolve normr_nneg : core.

Section NumDomainOperationTheory.

Variable R : numDomainType.
Implicit Types x y z t : R.

(* Properties of the real subset. *)

Lemma real1 : 1 \is @Num.real R. Proof. exact: rpred1. Qed.
Lemma realn n : n%:R \is @Num.real R. Proof. exact: rpred_nat. Qed.
#[local] Hint Resolve real1 : core.


Lemma ger1_real x : 1 <= x -> x \is Num.real. Proof. by move=> /ger_real->. Qed.
Lemma ler1_real x : x <= 1 -> x \is Num.real. Proof. by move=> /ler_real->. Qed.


(* mulr and ler/ltr *)

Lemma ler_pM2l x : 0 < x -> {mono *%R x : x y / x <= y}.
Proof.
by move=> x_gt0 y z /=; rewrite -subr_ge0 -mulrBr pmulr_rge0 // subr_ge0.
Qed.

Lemma ltr_pM2l x : 0 < x -> {mono *%R x : x y / x < y}.
Proof. by move=> x_gt0; apply: leW_mono (ler_pM2l _). Qed.

Definition lter_pM2l := (ler_pM2l, ltr_pM2l).

Lemma ler_pM2r x : 0 < x -> {mono *%R^~ x : x y / x <= y}.
Proof. by move=> x_gt0 y z /=; rewrite ![_ * x]mulrC ler_pM2l. Qed.

Lemma ltr_pM2r x : 0 < x -> {mono *%R^~ x : x y / x < y}.
Proof. by move=> x_gt0; apply: leW_mono (ler_pM2r _). Qed.

Definition lter_pM2r := (ler_pM2r, ltr_pM2r).

Lemma ler_nM2l x : x < 0 -> {mono *%R x : x y /~ x <= y}.
Proof. by move=> x_lt0 y z /=; rewrite -lerN2 -!mulNr ler_pM2l ?oppr_gt0. Qed.

Lemma ltr_nM2l x : x < 0 -> {mono *%R x : x y /~ x < y}.
Proof. by move=> x_lt0; apply: leW_nmono (ler_nM2l _). Qed.

Definition lter_nM2l := (ler_nM2l, ltr_nM2l).

Lemma ler_nM2r x : x < 0 -> {mono *%R^~ x : x y /~ x <= y}.
Proof. by move=> x_lt0 y z /=; rewrite ![_ * x]mulrC ler_nM2l. Qed.

Lemma ltr_nM2r x : x < 0 -> {mono *%R^~ x : x y /~ x < y}.
Proof. by move=> x_lt0; apply: leW_nmono (ler_nM2r _). Qed.

Definition lter_nM2r := (ler_nM2r, ltr_nM2r).

Lemma ler_wpM2l x : 0 <= x -> {homo *%R x : y z / y <= z}.
Proof.
by rewrite le0r => /orP[/eqP-> y z | /ler_pM2l/mono2W//]; rewrite !mul0r.
Qed.

Lemma ler_wpM2r x : 0 <= x -> {homo *%R^~ x : y z / y <= z}.
Proof. by move=> x_ge0 y z leyz; rewrite ![_ * x]mulrC ler_wpM2l. Qed.

Lemma ler_wnM2l x : x <= 0 -> {homo *%R x : y z /~ y <= z}.
 by move=> x_le0 y z leyz; rewrite -![x * _]mulrNN ler_wpM2l ?lterNE. Qed.

Lemma ler_wnM2r x : x <= 0 -> {homo *%R^~ x : y z /~ y <= z}.
Proof. by move=> x_le0 y z leyz; rewrite -![_ * x]mulrNN ler_wpM2r ?lterNE. Qed.

(* Binary forms, for backchaining. *)

Lemma ler_pM x1 y1 x2 y2 :
  0 <= x1 -> 0 <= x2 -> x1 <= y1 -> x2 <= y2 -> x1 * x2 <= y1 * y2.
Proof.
move=> x1ge0 x2ge0 le_xy1 le_xy2; have y1ge0 := le_trans x1ge0 le_xy1.
exact: le_trans (ler_wpM2r x2ge0 le_xy1) (ler_wpM2l y1ge0 le_xy2).
Qed.

Lemma ltr_pM x1 y1 x2 y2 :
  0 <= x1 -> 0 <= x2 -> x1 < y1 -> x2 < y2 -> x1 * x2 < y1 * y2.
Proof.
move=> x1ge0 x2ge0 lt_xy1 lt_xy2; have y1gt0 := le_lt_trans x1ge0 lt_xy1.
by rewrite (le_lt_trans (ler_wpM2r x2ge0 (ltW lt_xy1))) ?ltr_pM2l.
Qed.

(* complement for x *+ n and <= or < *)

Lemma ler_pMn2r n : (0 < n)%N -> {mono (@GRing.natmul R)^~ n : x y / x <= y}.
Proof.
by case: n => // n _ x y /=; rewrite -mulr_natl -[y *+ _]mulr_natl ler_pM2l.
Qed.

Lemma ltr_pMn2r n : (0 < n)%N -> {mono (@GRing.natmul R)^~ n : x y / x < y}.
Proof. by move/ler_pMn2r/leW_mono. Qed.

Lemma pmulrnI n : (0 < n)%N -> injective ((@GRing.natmul R)^~ n).
Proof. by move/ler_pMn2r/inc_inj. Qed.

Lemma eqr_pMn2r n : (0 < n)%N -> {mono (@GRing.natmul R)^~ n : x y / x == y}.
Proof. by move/pmulrnI/inj_eq. Qed.

Lemma pmulrn_lgt0 x n : (0 < n)%N -> (0 < x *+ n) = (0 < x).
Proof. by move=> n_gt0; rewrite -(mul0rn _ n) ltr_pMn2r // mul0rn. Qed.

Lemma pmulrn_llt0 x n : (0 < n)%N -> (x *+ n < 0) = (x < 0).
Proof. by move=> n_gt0; rewrite -(mul0rn _ n) ltr_pMn2r // mul0rn. Qed.

Lemma pmulrn_lge0 x n : (0 < n)%N -> (0 <= x *+ n) = (0 <= x).
Proof. by move=> n_gt0; rewrite -(mul0rn _ n) ler_pMn2r // mul0rn. Qed.

Lemma pmulrn_lle0 x n : (0 < n)%N -> (x *+ n <= 0) = (x <= 0).
Proof. by move=> n_gt0; rewrite -(mul0rn _ n) ler_pMn2r // mul0rn. Qed.

Lemma ltr_wMn2r x y n : x < y -> (x *+ n < y *+ n) = (0 < n)%N.
Proof. by move=> ltxy; case: n=> // n; rewrite ltr_pMn2r. Qed.

Lemma lerMn2r n x y : (x *+ n <= y *+ n) = ((n == 0) || (x <= y)).
Proof. by case: n => [|n]; rewrite ?lexx ?eqxx // ler_pMn2r. Qed.

Lemma ltrMn2r n x y : (x *+ n < y *+ n) = ((0 < n)%N && (x < y)).
Proof. by case: n => [|n]; rewrite ?lexx ?eqxx // ltr_pMn2r. Qed.

Lemma eqrMn2r n x y : (x *+ n == y *+ n) = (n == 0)%N || (x == y).
Proof. by rewrite !(@eq_le _ R) !lerMn2r -orb_andr. Qed.

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

Lemma ler_wpMn2l x :
  0 <= x -> {homo (@GRing.natmul R x) : m n / (m <= n)%N >-> m <= n}.
Proof. by move=> xge0 m n /subnK <-; rewrite mulrnDr ler_wpDl ?mulrn_wge0. Qed.

Lemma ler_wnMn2l x :
  x <= 0 -> {homo (@GRing.natmul R x) : m n / (n <= m)%N >-> m <= n}.
Proof.
by move=> xle0 m n hmn /=; rewrite -lerN2 -!mulNrn ler_wpMn2l // oppr_cp0.
Qed.

Lemma mulrn_wgt0 x n : 0 < x -> 0 < x *+ n = (0 < n)%N.
Proof. by case: n => // n hx; rewrite pmulrn_lgt0. Qed.

Lemma mulrn_wlt0 x n : x < 0 -> x *+ n < 0 = (0 < n)%N.
Proof. by case: n => // n hx; rewrite pmulrn_llt0. Qed.

Lemma ler_pMn2l x :
  0 < x -> {mono (@GRing.natmul R x) : m n / (m <= n)%N >-> m <= n}.
Proof.
move=> x_gt0 m n /=; case: leqP => hmn; first by rewrite ler_wpMn2l // ltW.
by rewrite -(subnK (ltnW hmn)) mulrnDr gerDr lt_geF // mulrn_wgt0 // subn_gt0.
Qed.

Lemma ltr_pMn2l x :
  0 < x -> {mono (@GRing.natmul R x) : m n / (m < n)%N >-> m < n}.
Proof. by move=> x_gt0; apply: leW_mono (ler_pMn2l _). Qed.

Lemma ler_nMn2l x :
  x < 0 -> {mono (@GRing.natmul R x) : m n / (n <= m)%N >-> m <= n}.
Proof. by move=> xlt0 m n /=; rewrite -lerN2 -!mulNrn ler_pMn2l// oppr_gt0. Qed.

Lemma ltr_nMn2l x :
  x < 0 -> {mono (@GRing.natmul R x) : m n / (n < m)%N >-> m < n}.
Proof. by move=> x_lt0; apply: leW_nmono (ler_nMn2l _). Qed.

Lemma ler_nat m n : (m%:R <= n%:R :> R) = (m <= n)%N.
Proof. by rewrite ler_pMn2l. Qed.

Lemma ltr_nat m n : (m%:R < n%:R :> R) = (m < n)%N.
Proof. by rewrite ltr_pMn2l. Qed.

Lemma eqr_nat m n : (m%:R == n%:R :> R) = (m == n)%N.
Proof. by rewrite (inj_eq (mulrIn _)) ?oner_eq0. Qed.

Lemma pnatr_eq1 n : (n%:R == 1 :> R) = (n == 1)%N.
Proof. exact: eqr_nat 1. Qed.

Lemma lern0 n : (n%:R <= 0 :> R) = (n == 0).
Proof. by rewrite -[0]/0%:R ler_nat leqn0. Qed.

Lemma ltrn0 n : (n%:R < 0 :> R) = false.
Proof. by rewrite -[0]/0%:R ltr_nat ltn0. Qed.

Lemma ler1n n : 1 <= n%:R :> R = (1 <= n)%N. Proof. by rewrite -ler_nat. Qed.
Lemma ltr1n n : 1 < n%:R :> R = (1 < n)%N. Proof. by rewrite -ltr_nat. Qed.
Lemma lern1 n : n%:R <= 1 :> R = (n <= 1)%N. Proof. by rewrite -ler_nat. Qed.
Lemma ltrn1 n : n%:R < 1 :> R = (n < 1)%N. Proof. by rewrite -ltr_nat. Qed.

Lemma ltrN10 : -1 < 0 :> R. Proof. by rewrite oppr_lt0. Qed.
Lemma lerN10 : -1 <= 0 :> R. Proof. by rewrite oppr_le0. Qed.
Lemma ltr10 : 1 < 0 :> R = false. Proof. by rewrite le_gtF. Qed.
Lemma ler10 : 1 <= 0 :> R = false. Proof. by rewrite lt_geF. Qed.
Lemma ltr0N1 : 0 < -1 :> R = false. Proof. by rewrite le_gtF // lerN10. Qed.
Lemma ler0N1 : 0 <= -1 :> R = false. Proof. by rewrite lt_geF // ltrN10. Qed.

#[deprecated(since="mathcomp 2.4.0", note="use `mulrn_wgt0` instead")]
Lemma pmulrn_rgt0 x n : 0 < x -> 0 < x *+ n = (0 < n)%N.
Proof. exact: mulrn_wgt0. Qed.

Lemma pmulrn_rlt0 x n : 0 < x -> x *+ n < 0 = false.
Proof. by move=> x_gt0; rewrite -(mulr0n x) ltr_pMn2l. Qed.

Lemma pmulrn_rge0 x n : 0 < x -> 0 <= x *+ n.
Proof. by move=> x_gt0; rewrite -(mulr0n x) ler_pMn2l. Qed.

Lemma pmulrn_rle0 x n : 0 < x -> x *+ n <= 0 = (n == 0)%N.
Proof. by move=> x_gt0; rewrite -(mulr0n x) ler_pMn2l ?leqn0. Qed.

Lemma nmulrn_rgt0 x n : x < 0 -> 0 < x *+ n = false.
Proof. by move=> x_lt0; rewrite -(mulr0n x) ltr_nMn2l. Qed.

Lemma nmulrn_rge0 x n : x < 0 -> 0 <= x *+ n = (n == 0)%N.
Proof. by move=> x_lt0; rewrite -(mulr0n x) ler_nMn2l ?leqn0. Qed.

Lemma nmulrn_rle0 x n : x < 0 -> x *+ n <= 0.
Proof. by move=> x_lt0; rewrite -(mulr0n x) ler_nMn2l. Qed.

(* (x * y) compared to 0 *)
(* Remark : pmulr_rgt0 and pmulr_rge0 are defined above *)

(* x positive and y right *)
Lemma pmulr_rlt0 x y : 0 < x -> (x * y < 0) = (y < 0).
Proof.
by move=> x_gt0; rewrite -[LHS]oppr_gt0 -mulrN pmulr_rgt0 // oppr_gt0.
Qed.

Lemma pmulr_rle0 x y : 0 < x -> (x * y <= 0) = (y <= 0).
Proof.
by move=> x_gt0; rewrite -[LHS]oppr_ge0 -mulrN pmulr_rge0 // oppr_ge0.
Qed.

(* x positive and y left *)
Lemma pmulr_lgt0 x y : 0 < x -> (0 < y * x) = (0 < y).
Proof. by move=> x_gt0; rewrite mulrC pmulr_rgt0. Qed.

Lemma pmulr_lge0 x y : 0 < x -> (0 <= y * x) = (0 <= y).
Proof. by move=> x_gt0; rewrite mulrC pmulr_rge0. Qed.

Lemma pmulr_llt0 x y : 0 < x -> (y * x < 0) = (y < 0).
Proof. by move=> x_gt0; rewrite mulrC pmulr_rlt0. Qed.

Lemma pmulr_lle0 x y : 0 < x -> (y * x <= 0) = (y <= 0).
Proof. by move=> x_gt0; rewrite mulrC pmulr_rle0. Qed.

(* x negative and y right *)
Lemma nmulr_rgt0 x y : x < 0 -> (0 < x * y) = (y < 0).
Proof. by move=> x_lt0; rewrite -mulrNN pmulr_rgt0 lterNE. Qed.

Lemma nmulr_rge0 x y : x < 0 -> (0 <= x * y) = (y <= 0).
Proof. by move=> x_lt0; rewrite -mulrNN pmulr_rge0 lterNE. Qed.

Lemma nmulr_rlt0 x y : x < 0 -> (x * y < 0) = (0 < y).
Proof. by move=> x_lt0; rewrite -mulrNN pmulr_rlt0 lterNE. Qed.

Lemma nmulr_rle0 x y : x < 0 -> (x * y <= 0) = (0 <= y).
Proof. by move=> x_lt0; rewrite -mulrNN pmulr_rle0 lterNE. Qed.

(* x negative and y left *)
Lemma nmulr_lgt0 x y : x < 0 -> (0 < y * x) = (y < 0).
Proof. by move=> x_lt0; rewrite mulrC nmulr_rgt0. Qed.

Lemma nmulr_lge0 x y : x < 0 -> (0 <= y * x) = (y <= 0).
Proof. by move=> x_lt0; rewrite mulrC nmulr_rge0. Qed.

Lemma nmulr_llt0 x y : x < 0 -> (y * x < 0) = (0 < y).
Proof. by move=> x_lt0; rewrite mulrC nmulr_rlt0. Qed.

Lemma nmulr_lle0 x y : x < 0 -> (y * x <= 0) = (0 <= y).
Proof. by move=> x_lt0; rewrite mulrC nmulr_rle0. Qed.

(* weak and symmetric lemmas *)
Lemma mulr_ge0 x y : 0 <= x -> 0 <= y -> 0 <= x * y.
Proof. by move=> x_ge0 y_ge0; rewrite -(mulr0 x) ler_wpM2l. Qed.

Lemma mulr_le0 x y : x <= 0 -> y <= 0 -> 0 <= x * y.
Proof. by move=> x_le0 y_le0; rewrite -(mulr0 x) ler_wnM2l. Qed.

Lemma mulr_ge0_le0 x y : 0 <= x -> y <= 0 -> x * y <= 0.
Proof. by move=> x_le0 y_le0; rewrite -(mulr0 x) ler_wpM2l. Qed.

Lemma mulr_le0_ge0 x y : x <= 0 -> 0 <= y -> x * y <= 0.
Proof. by move=> x_le0 y_le0; rewrite -(mulr0 x) ler_wnM2l. Qed.

(* mulr_gt0 with only one case *)

Lemma mulr_gt0 x y : 0 < x -> 0 < y -> 0 < x * y.
Proof. by move=> x_gt0 y_gt0; rewrite pmulr_rgt0. Qed.

(* and reverse direction *)

Lemma mulr_ge0_gt0 x y : 0 <= x -> 0 <= y -> (0 < x * y) = (0 < x) && (0 < y).
Proof.
rewrite le_eqVlt => /predU1P[<-|x0]; first by rewrite mul0r ltxx.
rewrite le_eqVlt => /predU1P[<-|y0]; first by rewrite mulr0 ltxx andbC.
by apply/idP/andP=> [|_]; rewrite pmulr_rgt0.
Qed.

(* Iterated products *)

Lemma prodr_ge0 I r (P : pred I) (E : I -> R) :
  (forall i, P i -> 0 <= E i) -> 0 <= \prod_(i <- r | P i) E i.
Proof. by move=> Ege0; rewrite -nnegrE rpred_prod. Qed.

Lemma prodr_gt0 I r (P : pred I) (E : I -> R) :
  (forall i, P i -> 0 < E i) -> 0 < \prod_(i <- r | P i) E i.
Proof. by move=> Ege0; rewrite -posrE rpred_prod. Qed.

Lemma ler_prod I r (P : pred I) (E1 E2 : I -> R) :
    (forall i, P i -> 0 <= E1 i <= E2 i) ->
  \prod_(i <- r | P i) E1 i <= \prod_(i <- r | P i) E2 i.
Proof.
move=> leE12; elim/(big_load (fun x => 0 <= x)): _.
elim/big_rec2: _ => // i x2 x1 /leE12/andP[le0Ei leEi12] [x1ge0 le_x12].
by rewrite mulr_ge0 // ler_pM.
Qed.

Lemma ltr_prod I r (P : pred I) (E1 E2 : I -> R) :
    has P r -> (forall i, P i -> 0 <= E1 i < E2 i) ->
  \prod_(i <- r | P i) E1 i < \prod_(i <- r | P i) E2 i.
Proof.
elim: r => //= i r IHr; rewrite !big_cons; case: ifP => {IHr}// Pi _ ltE12.
have /andP[le0E1i ltE12i] := ltE12 i Pi; set E2r := \prod_(j <- r | P j) E2 j.
apply: le_lt_trans (_ : E1 i * E2r < E2 i * E2r).
  by rewrite ler_wpM2l ?ler_prod // => j /ltE12/andP[-> /ltW].
by rewrite ltr_pM2r ?prodr_gt0 // => j /ltE12/andP[le0E1j /le_lt_trans->].
Qed.

Lemma ltr_prod_nat (E1 E2 : nat -> R) (n m : nat) :
   (m < n)%N -> (forall i, (m <= i < n)%N -> 0 <= E1 i < E2 i) ->
  \prod_(m <= i < n) E1 i < \prod_(m <= i < n) E2 i.
Proof.
move=> lt_mn ltE12; rewrite !big_nat ltr_prod {ltE12}//.
by apply/hasP; exists m; rewrite ?mem_index_iota leqnn.
Qed.

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

Lemma real_ltNge : {in real &, forall x y, (x < y) = ~~ (y <= x)}.
Proof. by move=> x y xR yR /=; case: real_leP. Qed.

Lemma real_leNgt : {in real &, forall x y, (x <= y) = ~~ (y < x)}.
Proof. by move=> x y xR yR /=; case: real_leP. Qed.

Lemma real_ltgtP x y : x \is real -> y \is real ->
  comparer x y (min y x) (min x y) (max y x) (max x y) `|x - y| `|y - x|
               (y == x) (x == y) (x >= y) (x <= y) (x > y) (x < y).
Proof.
move=> xR yR; case: zmod_ltgtP => // [?|?|->].
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

(* real of mul *)

Lemma realMr x y : x != 0 -> x \is real -> (x * y \is real) = (y \is real).
Proof.
move=> x_neq0 xR; case: real_ltgtP x_neq0 => // hx _; rewrite !realE.
  by rewrite nmulr_rge0 // nmulr_rle0 // orbC.
by rewrite pmulr_rge0 // pmulr_rle0 // orbC.
Qed.

Lemma realrM x y : y != 0 -> y \is real -> (x * y \is real) = (x \is real).
Proof. by move=> y_neq0 yR; rewrite mulrC realMr. Qed.

Lemma realM : {in real &, forall x y, x * y \is real}.
Proof. exact: rpredM. Qed.

Lemma realrMn x n : (n != 0)%N -> (x *+ n \is real) = (x \is real).
Proof. by move=> n_neq0; rewrite -mulr_natl realMr ?realn ?pnatr_eq0. Qed.

(* ler/ltr and multiplication between a positive/negative *)

Lemma ger_pMl x y : 0 < y -> (x * y <= y) = (x <= 1).
Proof. by move=> hy; rewrite -{2}[y]mul1r ler_pM2r. Qed.

Lemma gtr_pMl x y : 0 < y -> (x * y < y) = (x < 1).
Proof. by move=> hy; rewrite -{2}[y]mul1r ltr_pM2r. Qed.

Lemma ger_pMr x y : 0 < y -> (y * x <= y) = (x <= 1).
Proof. by move=> hy; rewrite -{2}[y]mulr1 ler_pM2l. Qed.

Lemma gtr_pMr x y : 0 < y -> (y * x < y) = (x < 1).
Proof. by move=> hy; rewrite -{2}[y]mulr1 ltr_pM2l. Qed.

Lemma ler_pMl x y : 0 < y -> (y <= x * y) = (1 <= x).
Proof. by move=> hy; rewrite -{1}[y]mul1r ler_pM2r. Qed.

Lemma ltr_pMl x y : 0 < y -> (y < x * y) = (1 < x).
Proof. by move=> hy; rewrite -{1}[y]mul1r ltr_pM2r. Qed.

Lemma ler_pMr x y : 0 < y -> (y <= y * x) = (1 <= x).
Proof. by move=> hy; rewrite -{1}[y]mulr1 ler_pM2l. Qed.

Lemma ltr_pMr x y : 0 < y -> (y < y * x) = (1 < x).
Proof. by move=> hy; rewrite -{1}[y]mulr1 ltr_pM2l. Qed.

Lemma ger_nMl x y : y < 0 -> (x * y <= y) = (1 <= x).
Proof. by move=> hy; rewrite -{2}[y]mul1r ler_nM2r. Qed.

Lemma gtr_nMl x y : y < 0 -> (x * y < y) = (1 < x).
Proof. by move=> hy; rewrite -{2}[y]mul1r ltr_nM2r. Qed.

Lemma ger_nMr x y : y < 0 -> (y * x <= y) = (1 <= x).
Proof. by move=> hy; rewrite -{2}[y]mulr1 ler_nM2l. Qed.

Lemma gtr_nMr x y : y < 0 -> (y * x < y) = (1 < x).
Proof. by move=> hy; rewrite -{2}[y]mulr1 ltr_nM2l. Qed.

Lemma ler_nMl x y : y < 0 -> (y <= x * y) = (x <= 1).
Proof. by move=> hy; rewrite -{1}[y]mul1r ler_nM2r. Qed.

Lemma ltr_nMl x y : y < 0 -> (y < x * y) = (x < 1).
Proof. by move=> hy; rewrite -{1}[y]mul1r ltr_nM2r. Qed.

Lemma ler_nMr x y : y < 0 -> (y <= y * x) = (x <= 1).
Proof. by move=> hy; rewrite -{1}[y]mulr1 ler_nM2l. Qed.

Lemma ltr_nMr x y : y < 0 -> (y < y * x) = (x < 1).
Proof. by move=> hy; rewrite -{1}[y]mulr1 ltr_nM2l. Qed.

(* ler/ltr and multiplication between a positive/negative
   and a exterior (1 <= _) or interior (0 <= _ <= 1) *)

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

Lemma mulr_ilt1 x y : 0 <= x -> 0 <= y -> x < 1 -> y < 1 -> x * y < 1.
Proof. by move=> *; rewrite (@le_lt_trans _ _ y) ?ler_piMl // ltW. Qed.

Definition mulr_ilte1 := (mulr_ile1, mulr_ilt1).

Lemma mulr_ege1 x y : 1 <= x -> 1 <= y -> 1 <= x * y.
Proof.
by move=> le1x le1y; rewrite (@le_trans _ _ y) ?ler_peMl // (le_trans ler01).
Qed.

Lemma mulr_egt1 x y : 1 < x -> 1 < y -> 1 < x * y.
Proof.
by move=> le1x lt1y; rewrite (@lt_trans _ _ y) // ltr_pMl // (lt_trans ltr01).
Qed.
Definition mulr_egte1 := (mulr_ege1, mulr_egt1).
Definition mulr_cp1 := (mulr_ilte1, mulr_egte1).

(* ler and ^-1 *)

Lemma invr_gt0 x : (0 < x^-1) = (0 < x).
Proof.
have [ux | nux] := boolP (x \is a GRing.unit); last by rewrite invr_out.
by apply/idP/idP=> /ltr_pM2r <-; rewrite mul0r (mulrV, mulVr) ?ltr01.
Qed.

Lemma invr_ge0 x : (0 <= x^-1) = (0 <= x).
Proof. by rewrite !le0r invr_gt0 invr_eq0. Qed.

Lemma invr_lt0 x : (x^-1 < 0) = (x < 0).
Proof. by rewrite -oppr_cp0 -invrN invr_gt0 oppr_cp0. Qed.

Lemma invr_le0 x : (x^-1 <= 0) = (x <= 0).
Proof. by rewrite -oppr_cp0 -invrN invr_ge0 oppr_cp0. Qed.

Definition invr_gte0 := (invr_ge0, invr_gt0).
Definition invr_lte0 := (invr_le0, invr_lt0).

Lemma divr_ge0 x y : 0 <= x -> 0 <= y -> 0 <= x / y.
Proof. by move=> x_ge0 y_ge0; rewrite mulr_ge0 ?invr_ge0. Qed.

Lemma divr_gt0 x y : 0 < x -> 0 < y -> 0 < x / y.
Proof. by move=> x_gt0 y_gt0; rewrite pmulr_rgt0 ?invr_gt0. Qed.

Lemma realV : {mono (@GRing.inv R) : x / x \is real}.
Proof. exact: rpredV. Qed.

(* ler and exprn *)
Lemma exprn_ge0 n x : 0 <= x -> 0 <= x ^+ n.
Proof. by move=> xge0; rewrite -nnegrE rpredX. Qed.

Lemma realX n : {in real, forall x, x ^+ n \is real}.
Proof. exact: rpredX. Qed.

Lemma exprn_gt0 n x : 0 < x -> 0 < x ^+ n.
Proof.
by rewrite !lt0r expf_eq0 => /andP[/negPf-> /exprn_ge0->]; rewrite andbF.
Qed.

Definition exprn_gte0 := (exprn_ge0, exprn_gt0).

Lemma exprn_ile1 n x : 0 <= x -> x <= 1 -> x ^+ n <= 1.
Proof.
move=> xge0 xle1; elim: n=> [|*]; rewrite ?expr0 // exprS.
by rewrite mulr_ile1 ?exprn_ge0.
Qed.

Lemma exprn_ilt1 n x : 0 <= x -> x < 1 -> x ^+ n < 1 = (n != 0).
Proof.
move=> xge0 xlt1.
case: n; [by rewrite eqxx ltxx | elim=> [|n ihn]; first by rewrite expr1].
by rewrite exprS mulr_ilt1 // exprn_ge0.
Qed.

Definition exprn_ilte1 := (exprn_ile1, exprn_ilt1).

Lemma exprn_ege1 n x : 1 <= x -> 1 <= x ^+ n.
Proof.
by move=> x_ge1; elim: n=> [|n ihn]; rewrite ?expr0 // exprS mulr_ege1.
Qed.

Lemma exprn_egt1 n x : 1 < x -> 1 < x ^+ n = (n != 0).
Proof.
move=> xgt1; case: n; first by rewrite eqxx ltxx.
by elim=> [|n ihn]; rewrite ?expr1// exprS mulr_egt1 // exprn_ge0.
Qed.

Definition exprn_egte1 := (exprn_ege1, exprn_egt1).
Definition exprn_cp1 := (exprn_ilte1, exprn_egte1).

Lemma ler_iXnr x n : (0 < n)%N -> 0 <= x -> x <= 1 -> x ^+ n <= x.
Proof. by case: n => n // *; rewrite exprS ler_piMr // exprn_ile1. Qed.

Lemma ltr_iXnr x n : 0 < x -> x < 1 -> (x ^+ n < x) = (1 < n)%N.
Proof.
case: n=> [|[|n]] //; first by rewrite expr0 => _ /lt_gtF ->.
by move=> x0 x1; rewrite exprS gtr_pMr // ?exprn_ilt1 // ltW.
Qed.

Definition lter_iXnr := (ler_iXnr, ltr_iXnr).

Lemma ler_eXnr x n : (0 < n)%N -> 1 <= x -> x <= x ^+ n.
Proof.
case: n => // n _ x_ge1.
by rewrite exprS ler_peMr ?(le_trans _ x_ge1) // exprn_ege1.
Qed.

Lemma ltr_eXnr x n : 1 < x -> (x < x ^+ n) = (1 < n)%N.
Proof.
move=> x_ge1; case: n=> [|[|n]] //; first by rewrite expr0 lt_gtF.
by rewrite exprS ltr_pMr ?(lt_trans _ x_ge1) ?exprn_egt1.
Qed.

Definition lter_eXnr := (ler_eXnr, ltr_eXnr).
Definition lter_Xnr := (lter_iXnr, lter_eXnr).

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

Lemma ieexprn_weq1 x n : 0 <= x -> (x ^+ n == 1) = ((n == 0) || (x == 1)).
Proof.
move=> xle0; case: n => [|n]; first by rewrite expr0 eqxx.
case: (@real_ltgtP x 1); do ?by rewrite ?ger0_real.
+ by move=> x_lt1; rewrite 1?lt_eqF // exprn_ilt1.
+ by move=> x_lt1; rewrite 1?gt_eqF // exprn_egt1.
by move->; rewrite expr1n eqxx.
Qed.

Lemma ieexprIn x : 0 < x -> x != 1 -> injective (GRing.exp x).
Proof.
move=> x_gt0 x_neq1 m n; without loss /subnK <-: m n / (n <= m)%N.
  by move=> IH eq_xmn; case/orP: (leq_total m n) => /IH->.
case: {m}(m - n)%N => // m /eqP/idPn[]; rewrite -[x ^+ n]mul1r exprD.
by rewrite (inj_eq (mulIf _)) ?ieexprn_weq1 ?ltW // expf_neq0 ?gt_eqF.
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

Lemma ltrXn2r n x y : 0 <= x -> x < y -> x ^+ n < y ^+ n = (n != 0).
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
case: n => // n _ x y; rewrite !qualifE /= =>  x_ge0 y_ge0.
have [-> | nzx] := eqVneq x 0; first by rewrite exprS mul0r exprn_ge0.
rewrite -subr_ge0 subrXX pmulr_lge0 ?subr_ge0 //= big_ord_recr /=.
rewrite subnn expr0 mul1r /= ltr_pwDr // ?exprn_gt0 ?lt0r ?nzx //.
by rewrite sumr_ge0 // => i _; rewrite mulr_ge0 ?exprn_ge0.
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

Lemma real_maxr_nMr x y z : x <= 0 -> y \is real -> z \is real ->
  x * max y z = min (x * y) (x * z).
Proof.
move=> x0 yr zr; rewrite -[_ * _]opprK -mulrN real_oppr_max// -mulNr.
by rewrite minr_pMr ?oppr_ge0// !(mulNr, mulrN, opprK).
Qed.

Lemma real_minr_nMr x y z :  x <= 0 -> y \is real -> z \is real ->
  x * min y z = max (x * y) (x * z).
Proof.
move=> x0 yr zr; rewrite -[_ * _]opprK -mulrN real_oppr_min// -mulNr.
by rewrite maxr_pMr ?oppr_ge0// !(mulNr, mulrN, opprK).
Qed.

Lemma minr_pMl x y z : 0 <= x -> min y z * x = min (y * x) (z * x).
Proof. by move=> *; rewrite mulrC minr_pMr // ![_ * x]mulrC. Qed.

Lemma maxr_pMl x y z : 0 <= x -> max y z * x = max (y * x) (z * x).
Proof. by move=> *; rewrite mulrC maxr_pMr // ![_ * x]mulrC. Qed.

Lemma real_minr_nMl x y z : x <= 0 -> y \is real -> z \is real ->
  min y z * x = max (y * x) (z * x).
Proof. by move=> *; rewrite mulrC real_minr_nMr // ![_ * x]mulrC. Qed.

Lemma real_maxr_nMl x y z : x <= 0 -> y \is real -> z \is real ->
  max y z * x = min (y * x) (z * x).
Proof. by move=> *; rewrite mulrC real_maxr_nMr // ![_ * x]mulrC. Qed.

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

Section RealDomainArgExtremum.

Context {I : finType} (i0 : I).
Context (P : pred I) (F : I -> R) (Pi0 : P i0).
Hypothesis F_real : {in P, forall i, F i \is real}.

Lemma real_arg_minP : extremum_spec <=%R P F [arg min_(i < i0 | P i) F i].
Proof.
by apply: comparable_arg_minP => // i j iP jP; rewrite real_comparable ?F_real.
Qed.

Lemma real_arg_maxP : extremum_spec >=%R P F [arg max_(i > i0 | P i) F i].
Proof.
by apply: comparable_arg_maxP => // i j iP jP; rewrite real_comparable ?F_real.
Qed.

End RealDomainArgExtremum.

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

Lemma ler_nnorml v x : x < 0 -> `|v| <= x = false.
Proof. by move=> h; rewrite lt_geF //; apply/(lt_le_trans h). Qed.

Lemma ltr_nnorml v x : x <= 0 -> `|v| < x = false.
Proof. by move=> h; rewrite le_gtF //; apply/(le_trans h). Qed.

Definition lter_nnormr := (ler_nnorml, ltr_nnorml).

End NormedZmoduleTheory.

Hint Extern 0 (is_true (norm _ \is real)) => apply: normr_real : core.

Lemma real_ler_norml x y : x \is real -> (`|x| <= y) = (- y <= x <= y).
Proof.
move=> xR; wlog x_ge0 : x xR / 0 <= x => [hwlog|].
  have /orP[/hwlog->|hx]// := real_leVge real0 xR.
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
move=> xR; wlog x_ge0 : x xR / 0 <= x => [hwlog|].
  have /orP[/hwlog->|hx]// := real_leVge real0 xR.
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

#[deprecated(since="mathcomp 2.3.0", note="use `ger0_def` instead")]
Lemma eqr_norm_id x : (`|x| == x) = (0 <= x). Proof. by rewrite ger0_def. Qed.

#[deprecated(since="mathcomp 2.3.0", note="use `ler0_def` instead")]
Lemma eqr_normN x : (`|x| == - x) = (x <= 0). Proof. by rewrite ler0_def. Qed.

Definition eqr_norm_idVN := =^~ (ger0_def, ler0_def).

Lemma real_exprn_even_ge0 n x : x \is real -> ~~ odd n -> 0 <= x ^+ n.
Proof.
move=> xR even_n; have [/exprn_ge0 -> //|x_lt0] := real_ge0P xR.
rewrite -[x]opprK -mulN1r exprMn -signr_odd (negPf even_n) expr0 mul1r.
by rewrite exprn_ge0 ?oppr_ge0 ?ltW.
Qed.

Lemma real_exprn_even_gt0 n x :
  x \is real -> ~~ odd n -> (0 < x ^+ n) = (n == 0)%N || (x != 0).
Proof.
move=> xR n_even; rewrite lt0r real_exprn_even_ge0 ?expf_eq0 //.
by rewrite andbT negb_and lt0n negbK.
Qed.

Lemma real_exprn_even_le0 n x :
  x \is real -> ~~ odd n -> (x ^+ n <= 0) = (n != 0) && (x == 0).
Proof.
move=> xR n_even; rewrite !real_leNgt ?rpred0 ?rpredX //.
by rewrite real_exprn_even_gt0 // negb_or negbK.
Qed.

Lemma real_exprn_even_lt0 n x :
  x \is real -> ~~ odd n -> (x ^+ n < 0) = false.
Proof. by move=> xR n_even; rewrite le_gtF // real_exprn_even_ge0. Qed.

Lemma real_exprn_odd_ge0 n x :
  x \is real -> odd n -> (0 <= x ^+ n) = (0 <= x).
Proof.
case/real_ge0P => [x_ge0|x_lt0] n_odd; first by rewrite exprn_ge0.
apply: negbTE; rewrite lt_geF //.
case: n n_odd => // n /= n_even; rewrite exprS pmulr_llt0 //.
by rewrite real_exprn_even_gt0 ?ler0_real ?ltW // (lt_eqF x_lt0) ?orbT.
Qed.

Lemma real_exprn_odd_gt0 n x : x \is real -> odd n -> (0 < x ^+ n) = (0 < x).
Proof.
by move=> xR n_odd; rewrite !lt0r expf_eq0 real_exprn_odd_ge0; case: n n_odd.
Qed.

Lemma real_exprn_odd_le0 n x : x \is real -> odd n -> (x ^+ n <= 0) = (x <= 0).
Proof.
by move=> xR n_odd; rewrite !real_leNgt ?rpred0 ?rpredX // real_exprn_odd_gt0.
Qed.

Lemma real_exprn_odd_lt0 n x : x \is real -> odd n -> (x ^+ n < 0) = (x < 0).
Proof.
by move=> xR n_odd; rewrite !real_ltNge ?rpred0 ?rpredX // real_exprn_odd_ge0.
Qed.

(* GG: Could this be a better definition of "real" ? *)
Lemma realEsqr x : (x \is real) = (0 <= x ^+ 2).
Proof. by rewrite ger0_def normrX eqf_sqr -ger0_def -ler0_def. Qed.

Lemma real_normK x : x \is real -> `|x| ^+ 2 = x ^+ 2.
Proof. by move=> Rx; rewrite -normrX ger0_norm -?realEsqr. Qed.

(* Binary sign ((-1) ^+ s). *)

Lemma normr_sign s : `|(-1) ^+ s : R| = 1.
Proof. by rewrite normrX normrN1 expr1n. Qed.

Lemma normrMsign s x : `|(-1) ^+ s * x| = `|x|.
Proof. by rewrite normrM normr_sign mul1r. Qed.

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

(* Ternary sign (sg). *)

Lemma sgr_def x : sg x = (-1) ^+ (x < 0)%R *+ (x != 0).
Proof. by rewrite /sg; do 2!case: ifP => //. Qed.

Lemma neqr0_sign x : x != 0 -> (-1) ^+ (x < 0)%R = sgr x.
Proof. by rewrite sgr_def  => ->. Qed.

Lemma gtr0_sg x : 0 < x -> sg x = 1.
Proof. by move=> x_gt0; rewrite /sg gt_eqF // lt_gtF. Qed.

Lemma ltr0_sg x : x < 0 -> sg x = -1.
Proof. by move=> x_lt0; rewrite /sg x_lt0 lt_eqF. Qed.

Lemma sgr0 : sg 0 = 0 :> R. Proof. by rewrite /sgr eqxx. Qed.
Lemma sgr1 : sg 1 = 1 :> R. Proof. by rewrite gtr0_sg // ltr01. Qed.
Lemma sgrN1 : sg (-1) = -1 :> R. Proof. by rewrite ltr0_sg // ltrN10. Qed.
Definition sgrE := (sgr0, sgr1, sgrN1).

Lemma sqr_sg x : sg x ^+ 2 = (x != 0)%:R.
Proof. by rewrite sgr_def exprMn_n sqrr_sign -mulnn mulnb andbb. Qed.

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
Proof. by rewrite -sqrf_eq0 sqr_sg pnatr_eq0; case: (x == 0). Qed.

Lemma sgr_odd n x : x != 0 -> (sg x) ^+ n = (sg x) ^+ (odd n).
Proof. by rewrite /sg; do 2!case: ifP => // _; rewrite ?expr1n ?signr_odd. Qed.

Lemma sgrMn x n : sg (x *+ n) = (n != 0)%:R * sg x.
Proof.
case: n => [|n]; first by rewrite mulr0n sgr0 mul0r.
by rewrite !sgr_def mulrn_eq0 mul1r pmulrn_llt0.
Qed.

Lemma sgr_nat n : sg n%:R = (n != 0)%:R :> R.
Proof. by rewrite sgrMn sgr1 mulr1. Qed.

Lemma sgr_id x : sg (sg x) = sg x.
Proof. by rewrite !(fun_if sg) !sgrE. Qed.

Lemma sgr_lt0 x : (sg x < 0) = (x < 0).
Proof.
rewrite /sg; case: eqP => [-> // | _].
by case: ifP => _; rewrite ?ltrN10 // lt_gtF.
Qed.

Lemma sgr_le0 x : (sgr x <= 0) = (x <= 0).
Proof. by rewrite !le_eqVlt sgr_eq0 sgr_lt0. Qed.

(* sign and norm *)

Lemma realEsign x : x \is real -> x = (-1) ^+ (x < 0)%R * `|x|.
Proof. by case/real_ge0P; rewrite (mul1r, mulN1r) ?opprK. Qed.

Lemma realNEsign x : x \is real -> - x = (-1) ^+ (0 < x)%R * `|x|.
Proof. by move=> Rx; rewrite -normrN -oppr_lt0 -realEsign ?rpredN. Qed.

Lemma real_normrEsign (x : R) (xR : x \is real) : `|x| = (-1) ^+ (x < 0)%R * x.
Proof. by rewrite {3}[x]realEsign // signrMK. Qed.

#[deprecated(since="mathcomp 2.3.0", note="use `realEsign` instead")]
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

(* leif *)

Lemma leif_nat_r m n C : (m%:R <= n%:R ?= iff C :> R) = (m <= n ?= iff C)%N.
Proof. by rewrite /leif !ler_nat eqr_nat. Qed.

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

Lemma real_leif_norm x : x \is real -> x <= `|x| ?= iff (0 <= x).
Proof.
by move=> xR; rewrite ger0_def eq_sym; apply: leif_eq; rewrite real_ler_norm.
Qed.

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

Lemma subr_lteifr0 C x y : (y - x < 0 ?<= if C) = (y < x ?<= if C).
Proof. by case: C => /=; rewrite subr_lte0. Qed.

Lemma subr_lteif0r C x y : (0 < y - x ?<= if C) = (x < y ?<= if C).
Proof. by case: C => /=; rewrite subr_gte0. Qed.

Definition subr_lteif0 := (subr_lteifr0, subr_lteif0r).

Lemma lteif01 C : 0 < 1 ?<= if C :> R.
Proof. by case: C; rewrite /= lter01. Qed.

Lemma lteif_pM2l C x : 0 < x -> {mono *%R x : y z / y < z ?<= if C}.
Proof. by case: C => ? ? ?; rewrite /= lter_pM2l. Qed.

Lemma lteif_pM2r C x : 0 < x -> {mono *%R^~ x : y z / y < z ?<= if C}.
Proof. by case: C => ? ? ?; rewrite /= lter_pM2r. Qed.

Lemma lteif_nM2l C x : x < 0 -> {mono *%R x : y z /~ y < z ?<= if C}.
Proof. by case: C => ? ? ?; rewrite /= lter_nM2l. Qed.

Lemma lteif_nM2r C x : x < 0 -> {mono *%R^~ x : y z /~ y < z ?<= if C}.
Proof. by case: C => ? ? ?; rewrite /= lter_nM2r. Qed.

Lemma lteif_nnormr C x y : y < 0 ?<= if ~~ C -> (`|x| < y ?<= if C) = false.
Proof. by case: C => ?; rewrite /= lter_nnormr. Qed.

Lemma real_lteifNE x y C : x \is Num.real -> y \is Num.real ->
  x < y ?<= if ~~ C = ~~ (y < x ?<= if C).
Proof. by move=> ? ?; rewrite comparable_lteifNE ?real_comparable. Qed.

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

(* Mean inequalities. *)

Lemma real_leif_mean_square_scaled x y :
  x \is real -> y \is real -> x * y *+ 2 <= x ^+ 2 + y ^+ 2 ?= iff (x == y).
Proof.
move=> Rx Ry; rewrite -[_ *+ 2]add0r -leifBRL addrAC -sqrrB -subr_eq0.
by rewrite -sqrf_eq0 eq_sym; apply: leif_eq; rewrite -realEsqr rpredB.
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
  rewrite !(bigD1 j A'j) /= addrCA eqxx !addrA subrK; congr (_ + _).
  by apply: eq_bigr => k /andP[_ /negPf->].
rewrite prodrMn_const exprMn_n -/n' ler_pMn2r ?expn_gt0; last by case: (n').
have ->: \prod_(k in A') E' k = E' j * pi.
  by rewrite (bigD1 j) //=; congr *%R; apply: eq_bigr => k /andP[_ /negPf->].
rewrite -(ler_pM2l mu_gt0) -exprS -Dn mulrA; apply: lt_le_trans.
rewrite ltr_pM2r //= eqxx -addrA mulrDr mulrC -ltrBlDl -mulrBl.
by rewrite mulrC ltr_pM2r ?subr_gt0.
Qed.

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
#[global] Hint Extern 0 (is_true (_%:R \is real)) => apply: realn : core.
#[global] Hint Extern 0 (is_true (1 \is real)) => apply: real1 : core.

Arguments ler_sqr {R} [x y].
Arguments ltr_sqr {R} [x y].
Arguments signr_inj {R} [x1 x2].
Arguments real_ler_normlP {R x y}.
Arguments real_ltr_normlP {R x y}.

Section FinGroup.

Import GroupScope.

Variables (R : numDomainType) (gT : finGroupType).
Implicit Types G : {group gT}.

Lemma natrG_gt0 G : #|G|%:R > 0 :> R.
Proof. by rewrite ltr0n cardG_gt0. Qed.

Lemma natrG_neq0 G : #|G|%:R != 0 :> R.
Proof. by rewrite gt_eqF // natrG_gt0. Qed.

Lemma natr_indexg_gt0 G B : #|G : B|%:R > 0 :> R.
Proof. by rewrite ltr0n indexg_gt0. Qed.

Lemma natr_indexg_neq0 G B : #|G : B|%:R != 0 :> R.
Proof. by rewrite gt_eqF // natr_indexg_gt0. Qed.

End FinGroup.


Section RealDomainTheory.

Variable R : realDomainType.
Implicit Types x y z t : R.

Lemma num_real x : x \is real. Proof. exact: num_real. Qed.
Hint Resolve num_real : core.

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

(* sign *)

Lemma mulr_lt0 x y :
  (x * y < 0) = [&& x != 0, y != 0 & (x < 0) (+) (y < 0)].
Proof.
have [x_gt0|x_lt0|->] /= := ltrgt0P x; last by rewrite mul0r.
  by rewrite pmulr_rlt0 //; case: ltrgt0P.
by rewrite nmulr_rlt0 //; case: ltrgt0P.
Qed.

Lemma neq0_mulr_lt0 x y :
  x != 0 -> y != 0 -> (x * y < 0) = (x < 0) (+) (y < 0).
Proof. by move=> x_neq0 y_neq0; rewrite mulr_lt0 x_neq0 y_neq0. Qed.

Lemma mulr_sign_lt0 (b : bool) x :
  ((-1) ^+ b * x < 0) = (x != 0) && (b (+) (x < 0)%R).
Proof. by rewrite mulr_lt0 signr_lt0 signr_eq0. Qed.

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

Lemma sgr_cp0 x :
  ((sg x == 1) = (0 < x)) *
  ((sg x == -1) = (x < 0)) *
  ((sg x == 0) = (x == 0)).
Proof.
rewrite -[1]/((-1) ^+ false) -signrN lt0r leNgt sgr_def.
case: (x =P 0) => [-> | _]; first by rewrite !(eq_sym 0) !signr_eq0 ltxx eqxx.
by rewrite !(inj_eq signr_inj) eqb_id eqbF_neg signr_eq0 //.
Qed.

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

#[deprecated(since="mathcomp 2.3.0", note="use `numEsg` instead")]
Lemma mulr_sg_norm x : sg x * `|x| = x. Proof. by rewrite -numEsg. Qed.

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

(* Special lemmas for squares. *)

Lemma sqr_ge0 x : 0 <= x ^+ 2. Proof. by rewrite exprn_even_ge0. Qed.

Lemma sqr_norm_eq1 x : (x ^+ 2 == 1) = (`|x| == 1).
Proof. by rewrite sqrf_eq1 eqr_norml ler01 andbT. Qed.

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

HB.factory Record IntegralDomain_isNumRing R of GRing.IntegralDomain R := {
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

HB.builders Context R of IntegralDomain_isNumRing R.
  Local Notation "x <= y" := (Rle x y) : ring_scope.
  Local Notation "x < y" := (Rlt x y) : ring_scope.
  Local Notation "`| x |" := (norm x) : ring_scope.

  Lemma ltrr x : x < x = false. Proof. by rewrite lt_def eqxx. Qed.

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
  have ->: 0 <= -1 = (-1 == 0 :> R) || (0 < -1)
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

HB.factory Record NumDomain_isReal R of NumDomain R := {
  real : real_axiom R
}.

HB.builders Context R of NumDomain_isReal R.
  Lemma le_total : Order.POrder_isTotal ring_display R.
  Proof.
  constructor=> x y; move: (real (x - y)).
  by rewrite unfold_in /= !ler_def subr0 add0r opprB orbC.
  Qed.

  HB.instance Definition _ := le_total.
HB.end.

HB.factory Record IntegralDomain_isLeReal R of GRing.IntegralDomain R := {
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

HB.builders Context R of IntegralDomain_isLeReal R.
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
    by rewrite ge0_norm // opprD addrCA -addrA addKr le0_add.
  by rewrite -normN ge0_norm // opprK addrCA addrNK le0_add.
  Qed.

  Fact le_total : total le.
  Proof. by move=> x y; rewrite -sub_ge0 -opprB le0N orbC -sub_ge0 le0_total. Qed.

  HB.instance Definition _ := IntegralDomain_isNumRing.Build R
    le_normD lt0_add eq0_norm (in2W le_total) normM le_def lt_def.

  HB.instance Definition _ := Order.POrder_isTotal.Build ring_display R
    le_total.
HB.end.

HB.factory Record IntegralDomain_isLtReal R of GRing.IntegralDomain R := {
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

HB.builders Context R of IntegralDomain_isLtReal R.
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
    by rewrite ge0_norm // opprD addrCA -addrA addKr le0_add.
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
Export Num.Exports Num.Syntax Num.PredInstances.
