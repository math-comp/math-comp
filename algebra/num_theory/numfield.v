(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import ssrAC div fintype path bigop order finset fingroup.
From mathcomp Require Import ssralg poly orderedzmod numdomain.

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
(*    numFieldType == Field with an order and a norm                          *)
(*                    The HB class is called NumField.                        *)
(* numClosedFieldType == Partially ordered Closed Field with conjugation      *)
(*                    The HB class is called ClosedField.                     *)
(*  realDomainType == Num domain where all elements are positive or negative  *)
(*                    The HB class is called RealDomain.                      *)
(*   realFieldType == Num Field where all elements are positive or negative   *)
(*                    The HB class is called RealField.                       *)
(*         rcfType == A Real Field with the real closed axiom                 *)
(*                    The HB class is called RealClosedField.                 *)
(*                                                                            *)
(*       Num.sqrt x == in a real-closed field, a positive square root of x if *)
(*                     x >= 0, or 0 otherwise                                 *)
(* For numeric algebraically closed fields we provide the generic definitions *)
(*         'i == the imaginary number (:= sqrtC (-1))                         *)
(*      'Re z == the real component of z                                      *)
(*      'Im z == the imaginary component of z                                 *)
(*        z^* == the complex conjugate of z (:= conjC z)                      *)
(*    sqrtC z == a nonnegative square root of z, i.e., 0 <= sqrt x if 0 <= x  *)
(*  n.-root z == more generally, for n > 0, an nth root of z, chosen with a   *)
(*               minimal non-negative argument for n > 1 (i.e., with a        *)
(*               maximal real part subject to a nonnegative imaginary part)   *)
(*               Note that n.-root (-1) is a primitive 2nth root of unity,    *)
(*               an thus not equal to -1 for n odd > 1 (this will be shown in *)
(*               file cyclotomic.v).                                          *)
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
(* Pdeg2.NumClosed : theory of the degree 2 polynomials on NumClosedField.    *)
(* Pdeg2.NumClosedMonic : theory of Pdeg2.NumClosed specialized to monic      *)
(*   polynomials.                                                             *)
(* Pdeg2.Real : theory of the degree 2 polynomials on RealField and rcfType.  *)
(* Pdeg2.RealMonic : theory of Pdeg2.Real specialized to monic polynomials.   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope order_scope.
Local Open Scope ring_scope.

Import Order.TTheory GRing.Theory.

Import orderedzmod.Num numdomain.Num.

Module Num.

#[short(type="numFieldType")]
HB.structure Definition NumField := { R of GRing.UnitRing_isField R &
     GRing.IntegralDomain R &
     POrderedZmodule R &
     NormedZmodule (POrderedZmodule.clone R _) R &
     isNumRing R }.

Module NumFieldExports.
Bind Scope ring_scope with NumField.sort.
End NumFieldExports.
HB.export NumFieldExports.

HB.mixin Record NumField_isImaginary R of NumField R := {
  imaginary : R;
  conj_op : {rmorphism R -> R};
  sqrCi : imaginary ^+ 2 = - 1;
  normCK : forall x, `|x| ^+ 2 = x * conj_op x;
}.

#[short(type="numClosedFieldType")]
HB.structure Definition ClosedField :=
  { R of NumField_isImaginary R & GRing.ClosedField R & NumField R }.

Module ClosedFieldExports.
Bind Scope ring_scope with ClosedField.sort.
End ClosedFieldExports.
HB.export ClosedFieldExports.

#[short(type="realFieldType")]
HB.structure Definition RealField :=
  { R of Order.Total ring_display R & NumField R }.

Module RealFieldExports.
Bind Scope ring_scope with RealField.sort.
End RealFieldExports.
HB.export RealFieldExports.

HB.mixin Record RealField_isClosed R of RealField R := {
  poly_ivt_subproof : real_closed_axiom R
}.

#[short(type="rcfType")]
HB.structure Definition RealClosedField :=
  { R of RealField_isClosed R & RealField R }.

Module RealClosedFieldExports.
Bind Scope ring_scope with RealClosedField.sort.
End RealClosedFieldExports.
HB.export RealClosedFieldExports.

Section RealClosed.
Variable R : rcfType.

Lemma poly_ivt : real_closed_axiom R. Proof. exact: poly_ivt_subproof. Qed.

Fact sqrtr_subproof (x : R) :
  exists2 y, 0 <= y & (if 0 <= x then y ^+ 2 == x else y == 0) : bool.
Proof.
case x_ge0: (0 <= x); last by exists 0.
have le0x1: 0 <= x + 1 by rewrite -nnegrE rpredD ?rpred1.
have [|y /andP[y_ge0 _]] := @poly_ivt ('X^2 - x%:P) _ _ le0x1.
  rewrite !hornerE -subr_ge0 add0r expr0n sub0r opprK x_ge0 sqrrD mulr1.
  by rewrite addrAC !addrA addrK -nnegrE !rpredD ?rpredX ?rpred1.
by rewrite rootE !hornerE subr_eq0; exists y.
Qed.

End RealClosed.

Module Import Def.

Definition sqrtr {R} x := s2val (sig2W (@sqrtr_subproof R x)).

End Def.

Notation sqrt := sqrtr.

Module Export Theory.
Section NumFieldTheory.

Variable F : numFieldType.
Implicit Types x y z t : F.

Lemma unitf_gt0 x : 0 < x -> x \is a GRing.unit.
Proof. by move=> hx; rewrite unitfE eq_sym lt_eqF. Qed.

Lemma unitf_lt0 x : x < 0 -> x \is a GRing.unit.
Proof. by move=> hx; rewrite unitfE lt_eqF. Qed.

Lemma lef_pV2 : {in pos &, {mono (@GRing.inv F) : x y /~ x <= y}}.
Proof. by move=> x y hx hy /=; rewrite ler_pV2 ?inE ?unitf_gt0. Qed.

Lemma lef_nV2 : {in neg &, {mono (@GRing.inv F) : x y /~ x <= y}}.
Proof. by move=> x y hx hy /=; rewrite ler_nV2 ?inE ?unitf_lt0. Qed.

Lemma ltf_pV2 : {in pos &, {mono (@GRing.inv F) : x y /~ x < y}}.
Proof. exact: leW_nmono_in lef_pV2. Qed.

Lemma ltf_nV2 : {in neg &, {mono (@GRing.inv F) : x y /~ x < y}}.
Proof. exact: leW_nmono_in lef_nV2. Qed.

Definition ltef_pV2 := (lef_pV2, ltf_pV2).
Definition ltef_nV2 := (lef_nV2, ltf_nV2).

Lemma invf_pgt : {in pos &, forall x y, (x < y^-1) = (y < x^-1)}.
Proof. by move=> x y *; rewrite -[x in LHS]invrK ltf_pV2// posrE invr_gt0. Qed.

Lemma invf_pge : {in pos &, forall x y, (x <= y^-1) = (y <= x^-1)}.
Proof. by move=> x y *; rewrite -[x in LHS]invrK lef_pV2// posrE invr_gt0. Qed.

Lemma invf_ngt : {in neg &, forall x y, (x < y^-1) = (y < x^-1)}.
Proof. by move=> x y *; rewrite -[x in LHS]invrK ltf_nV2// negrE invr_lt0. Qed.

Lemma invf_nge : {in neg &, forall x y, (x <= y^-1) = (y <= x^-1)}.
Proof. by move=> x y *; rewrite -[x in LHS]invrK lef_nV2// negrE invr_lt0. Qed.

Lemma invf_gt1 x : 0 < x -> (1 < x^-1) = (x < 1).
Proof. by move=> x0; rewrite invf_pgt ?invr1 ?posrE. Qed.

Lemma invf_ge1 x : 0 < x -> (1 <= x^-1) = (x <= 1).
Proof. by move=> x0; rewrite invf_pge ?invr1 ?posrE. Qed.

Definition invf_gte1 := (invf_ge1, invf_gt1).

Lemma invf_plt : {in pos &, forall x y, (x^-1 < y) = (y^-1 < x)}.
Proof. by move=> x y *; rewrite -[y in LHS]invrK ltf_pV2// posrE invr_gt0. Qed.

Lemma invf_ple : {in pos &, forall x y, (x^-1 <= y) = (y^-1 <= x)}.
Proof. by move=> x y *; rewrite -[y in LHS]invrK lef_pV2// posrE invr_gt0. Qed.

Lemma invf_nlt : {in neg &, forall x y, (x^-1 < y) = (y^-1 < x)}.
Proof. by move=> x y *; rewrite -[y in LHS]invrK ltf_nV2// negrE invr_lt0. Qed.

Lemma invf_nle : {in neg &, forall x y, (x^-1 <= y) = (y^-1 <= x)}.
Proof. by move=> x y *; rewrite -[y in LHS]invrK lef_nV2// negrE invr_lt0. Qed.

Lemma invf_le1 x : 0 < x -> (x^-1 <= 1) = (1 <= x).
Proof. by move=> x0; rewrite -invf_ple ?invr1 ?posrE. Qed.

Lemma invf_lt1 x : 0 < x -> (x^-1 < 1) = (1 < x).
Proof. by move=> x0; rewrite invf_plt ?invr1 ?posrE. Qed.

Definition invf_lte1 := (invf_le1, invf_lt1).
Definition invf_cp1 := (invf_gte1, invf_lte1).

(* These lemma are all combinations of mono(LR|RL) with ler_[pn]mul2[rl]. *)
Lemma ler_pdivlMr z x y : 0 < z -> (x <= y / z) = (x * z <= y).
Proof. by move=> z_gt0; rewrite -(@ler_pM2r _ z _ x) ?mulfVK ?gt_eqF. Qed.

Lemma ltr_pdivlMr z x y : 0 < z -> (x < y / z) = (x * z < y).
Proof. by move=> z_gt0; rewrite -(@ltr_pM2r _ z _ x) ?mulfVK ?gt_eqF. Qed.

Definition lter_pdivlMr := (ler_pdivlMr, ltr_pdivlMr).

Lemma ler_pdivrMr z x y : 0 < z -> (y / z <= x) = (y <= x * z).
Proof. by move=> z_gt0; rewrite -(@ler_pM2r _ z) ?mulfVK ?gt_eqF. Qed.

Lemma ltr_pdivrMr z x y : 0 < z -> (y / z < x) = (y < x * z).
Proof. by move=> z_gt0; rewrite -(@ltr_pM2r _ z) ?mulfVK ?gt_eqF. Qed.

Definition lter_pdivrMr := (ler_pdivrMr, ltr_pdivrMr).

Lemma ler_pdivlMl z x y : 0 < z -> (x <= z^-1 * y) = (z * x <= y).
Proof. by move=> z_gt0; rewrite mulrC ler_pdivlMr ?[z * _]mulrC. Qed.

Lemma ltr_pdivlMl z x y : 0 < z -> (x < z^-1 * y) = (z * x < y).
Proof. by move=> z_gt0; rewrite mulrC ltr_pdivlMr ?[z * _]mulrC. Qed.

Definition lter_pdivlMl := (ler_pdivlMl, ltr_pdivlMl).

Lemma ler_pdivrMl z x y : 0 < z -> (z^-1 * y <= x) = (y <= z * x).
Proof. by move=> z_gt0; rewrite mulrC ler_pdivrMr ?[z * _]mulrC. Qed.

Lemma ltr_pdivrMl z x y : 0 < z -> (z^-1 * y < x) = (y < z * x).
Proof. by move=> z_gt0; rewrite mulrC ltr_pdivrMr ?[z * _]mulrC. Qed.

Definition lter_pdivrMl := (ler_pdivrMl, ltr_pdivrMl).

Lemma ler_ndivlMr z x y : z < 0 -> (x <= y / z) = (y <= x * z).
Proof. by move=> z_lt0; rewrite -(@ler_nM2r _ z) ?mulfVK  ?lt_eqF. Qed.

Lemma ltr_ndivlMr z x y : z < 0 -> (x < y / z) = (y < x * z).
Proof. by move=> z_lt0; rewrite -(@ltr_nM2r _ z) ?mulfVK ?lt_eqF. Qed.

Definition lter_ndivlMr := (ler_ndivlMr, ltr_ndivlMr).

Lemma ler_ndivrMr z x y : z < 0 -> (y / z <= x) = (x * z <= y).
Proof. by move=> z_lt0; rewrite -(@ler_nM2r _ z) ?mulfVK ?lt_eqF. Qed.

Lemma ltr_ndivrMr z x y : z < 0 -> (y / z < x) = (x * z < y).
Proof. by move=> z_lt0; rewrite -(@ltr_nM2r _ z) ?mulfVK ?lt_eqF. Qed.

Definition lter_ndivrMr := (ler_ndivrMr, ltr_ndivrMr).

Lemma ler_ndivlMl z x y : z < 0 -> (x <= z^-1 * y) = (y <= z * x).
Proof. by move=> z_lt0; rewrite mulrC ler_ndivlMr ?[z * _]mulrC. Qed.

Lemma ltr_ndivlMl z x y : z < 0 -> (x < z^-1 * y) = (y < z * x).
Proof. by move=> z_lt0; rewrite mulrC ltr_ndivlMr ?[z * _]mulrC. Qed.

Definition lter_ndivlMl := (ler_ndivlMl, ltr_ndivlMl).

Lemma ler_ndivrMl z x y : z < 0 -> (z^-1 * y <= x) = (z * x <= y).
Proof. by move=> z_lt0; rewrite mulrC ler_ndivrMr ?[z * _]mulrC. Qed.

Lemma ltr_ndivrMl z x y : z < 0 -> (z^-1 * y < x) = (z * x < y).
Proof. by move=> z_lt0; rewrite mulrC ltr_ndivrMr ?[z * _]mulrC. Qed.

Definition lter_ndivrMl := (ler_ndivrMl, ltr_ndivrMl).

Lemma natf_div m d : (d %| m)%N -> (m %/ d)%:R = m%:R / d%:R :> F.
Proof. by apply: char0_natf_div; apply: (@char_num F). Qed.

Lemma normfV : {morph (norm : F -> F) : x / x ^-1}.
Proof.
move=> x /=; have [/normrV //|Nux] := boolP (x \is a GRing.unit).
by rewrite !invr_out // unitfE normr_eq0 -unitfE.
Qed.

Lemma normf_div : {morph (norm : F -> F) : x y / x / y}.
Proof. by move=> x y /=; rewrite normrM normfV. Qed.

Lemma invr_sg x : (sg x)^-1 = sgr x.
Proof. by rewrite !(fun_if GRing.inv) !(invr0, invrN, invr1). Qed.

Lemma sgrV x : sgr x^-1 = sgr x.
Proof. by rewrite /sgr invr_eq0 invr_lt0. Qed.

Lemma splitr x : x = x / 2%:R + x / 2%:R.
Proof. by rewrite -mulr2n -mulr_natr mulfVK //= pnatr_eq0. Qed.

(* lteif *)

Lemma lteif_pdivlMr C z x y :
  0 < z -> x < y / z ?<= if C = (x * z < y ?<= if C).
Proof. by case: C => ? /=; rewrite lter_pdivlMr. Qed.

Lemma lteif_pdivrMr C z x y :
  0 < z -> y / z < x ?<= if C = (y < x * z ?<= if C).
Proof. by case: C => ? /=; rewrite lter_pdivrMr. Qed.

Lemma lteif_pdivlMl C z x y :
  0 < z -> x < z^-1 * y ?<= if C = (z * x < y ?<= if C).
Proof. by case: C => ? /=; rewrite lter_pdivlMl. Qed.

Lemma lteif_pdivrMl C z x y :
  0 < z -> z^-1 * y < x ?<= if C = (y < z * x ?<= if C).
Proof. by case: C => ? /=; rewrite lter_pdivrMl. Qed.

Lemma lteif_ndivlMr C z x y :
  z < 0 -> x < y / z ?<= if C = (y < x * z ?<= if C).
Proof. by case: C => ? /=; rewrite lter_ndivlMr. Qed.

Lemma lteif_ndivrMr C z x y :
  z < 0 -> y / z < x ?<= if C = (x * z < y ?<= if C).
Proof. by case: C => ? /=; rewrite lter_ndivrMr. Qed.

Lemma lteif_ndivlMl C z x y :
  z < 0 -> x < z^-1 * y ?<= if C = (y < z * x ?<= if C).
Proof. by case: C => ? /=; rewrite lter_ndivlMl. Qed.

Lemma lteif_ndivrMl C z x y :
  z < 0 -> z^-1 * y < x ?<= if C = (z * x < y ?<= if C).
Proof. by case: C => ? /=; rewrite lter_ndivrMl. Qed.

(* Interval midpoint. *)

Local Notation mid x y := ((x + y) / 2).

Lemma midf_le x y : x <= y -> (x <= mid x y) * (mid x y <= y).
Proof.
move=> lexy; rewrite ler_pdivlMr ?ler_pdivrMr ?ltr0Sn //.
by rewrite !mulrDr !mulr1 !lerD2.
Qed.

Lemma midf_lt x y : x < y -> (x < mid x y) * (mid x y < y).
Proof.
move=> ltxy; rewrite ltr_pdivlMr ?ltr_pdivrMr ?ltr0Sn //.
by rewrite !mulrDr !mulr1 !ltrD2.
Qed.

Definition midf_lte := (midf_le, midf_lt).

Lemma ler_addgt0Pr x y : reflect (forall e, e > 0 -> x <= y + e) (x <= y).
Proof.
apply/(iffP idP)=> [lexy e e_gt0 | lexye]; first by rewrite ler_wpDr// ltW.
have [||ltyx]// := comparable_leP.
  rewrite (@comparabler_trans _ (y + 1))// /Order.comparable ?lexye ?ltr01//.
  by rewrite lerDl ler01 orbT.
have /midf_lt [_] := ltyx; rewrite le_gtF//.
rewrite -(@addrK _ y y) (addrAC _ _ x) -addrA 2!mulrDl -splitr lexye//.
by rewrite divr_gt0// ?ltr0n// subr_gt0.
Qed.

Lemma ler_addgt0Pl x y : reflect (forall e, e > 0 -> x <= e + y) (x <= y).
Proof.
by apply/(equivP (ler_addgt0Pr x y)); split=> lexy e /lexy; rewrite addrC.
Qed.

Lemma lt_le a b : (forall x, x < a -> x < b) -> a <= b.
Proof.
move=> ab; apply/ler_addgt0Pr => e e_gt0; rewrite -lerBDr ltW//.
by rewrite ab// ltrBlDr ltrDl.
Qed.

Lemma gt_ge a b : (forall x, b < x -> a < x) -> a <= b.
Proof.
by move=> ab; apply/ler_addgt0Pr => e e_gt0; rewrite ltW// ab// ltrDl.
Qed.

(* The AGM, unscaled but without the nth root. *)

Lemma real_leif_mean_square x y :
  x \is real -> y \is real -> x * y <= mid (x ^+ 2) (y ^+ 2) ?= iff (x == y).
Proof.
move=> Rx Ry; rewrite -(mono_leif (ler_pM2r (ltr_nat F 0 2))).
by rewrite divfK ?pnatr_eq0 // mulr_natr; apply: real_leif_mean_square_scaled.
Qed.

Lemma real_leif_AGM2 x y :
  x \is real -> y \is real -> x * y <= mid x y ^+ 2 ?= iff (x == y).
Proof.
move=> Rx Ry; rewrite -(mono_leif (ler_pM2r (ltr_nat F 0 4))).
rewrite mulr_natr (natrX F 2 2) -exprMn divfK ?pnatr_eq0 //.
exact: real_leif_AGM2_scaled.
Qed.

Lemma leif_AGM (I : finType) (A : {pred I}) (E : I -> F) :
    let n := #|A| in let mu := (\sum_(i in A) E i) / n%:R in
    {in A, forall i, 0 <= E i} ->
  \prod_(i in A) E i <= mu ^+ n
                     ?= iff [forall i in A, forall j in A, E i == E j].
Proof.
move=> n mu Ege0; have [n0 | n_gt0] := posnP n.
  by rewrite n0 -big_andE !(big_pred0 _ _ _ _ (card0_eq n0)); apply/leifP.
pose E' i := E i / n%:R.
have defE' i: E' i *+ n = E i by rewrite -mulr_natr divfK ?pnatr_eq0 -?lt0n.
have /leif_AGM_scaled (i): i \in A -> 0 <= E' i *+ n by rewrite defE' => /Ege0.
rewrite -/n -mulr_suml (eq_bigr _ (in1W defE')); congr (_ <= _ ?= iff _).
by do 2![apply: eq_forallb_in => ? _]; rewrite -(eqr_pMn2r n_gt0) !defE'.
Qed.

Implicit Type p : {poly F}.
Lemma Cauchy_root_bound p : p != 0 -> {b | forall x, root p x -> `|x| <= b}.
Proof.
move=> nz_p; set a := lead_coef p; set n := (size p).-1.
have [q Dp]: {q | forall x, x != 0 -> p.[x] = (a - q.[x^-1] / x) * x ^+ n}.
  exists (- \poly_(i < n) p`_(n - i.+1)) => x nz_x.
  rewrite hornerN mulNr opprK horner_poly mulrDl !mulr_suml addrC.
  rewrite horner_coef polySpred // big_ord_recr (reindex_inj rev_ord_inj) /=.
  rewrite -/n -lead_coefE; congr (_ + _); apply: eq_bigr=> i _.
  by rewrite exprB ?unitfE // -exprVn mulrA mulrAC exprSr mulrA.
have [b ub_q] := poly_disk_bound q 1; exists (b / `|a| + 1) => x px0.
have b_ge0: 0 <= b by rewrite (le_trans (normr_ge0 q.[1])) ?ub_q ?normr1.
have{b_ge0} ba_ge0: 0 <= b / `|a| by rewrite divr_ge0.
rewrite real_leNgt ?rpredD ?rpred1 ?ger0_real //.
apply: contraL px0 => lb_x; rewrite rootE.
have x_ge1: 1 <= `|x| by rewrite (le_trans _ (ltW lb_x)) // ler_wpDl.
have nz_x: x != 0 by rewrite -normr_gt0 (lt_le_trans ltr01).
rewrite {}Dp // mulf_neq0 ?expf_neq0 // subr_eq0 eq_sym.
have: (b / `|a|) < `|x| by rewrite (lt_trans _ lb_x) // ltr_pwDr ?ltr01.
apply: contraTneq => /(canRL (divfK nz_x))Dax.
rewrite ltr_pdivrMr ?normr_gt0 ?lead_coef_eq0 // mulrC -normrM -{}Dax.
by rewrite le_gtF // ub_q // normfV invf_le1 ?normr_gt0.
Qed.

Import GroupScope.

Lemma natf_indexg (gT : finGroupType) (G H : {group gT}) :
  H \subset G -> #|G : H|%:R = (#|G|%:R / #|H|%:R)%R :> F.
Proof. by move=> sHG; rewrite -divgS // natf_div ?cardSg. Qed.

End NumFieldTheory.

Section RealField.

Variables (F : realFieldType) (x y : F).

Lemma leif_mean_square : x * y <= (x ^+ 2 + y ^+ 2) / 2 ?= iff (x == y).
Proof. by apply: real_leif_mean_square; apply: num_real. Qed.

Lemma leif_AGM2 : x * y <= ((x + y) / 2)^+ 2 ?= iff (x == y).
Proof. by apply: real_leif_AGM2; apply: num_real. Qed.

End RealField.

Section RealClosedFieldTheory.

Variable R : rcfType.
Implicit Types a x y : R.

Lemma poly_ivt : real_closed_axiom R. Proof. exact: poly_ivt. Qed.

(* Square Root theory *)

Lemma sqrtr_ge0 a : 0 <= sqrt a.
Proof. by rewrite /sqrt; case: (sig2W _). Qed.
Hint Resolve sqrtr_ge0 : core.

Lemma sqr_sqrtr a : 0 <= a -> sqrt a ^+ 2 = a.
Proof.
by rewrite /sqrt => a_ge0; case: (sig2W _) => /= x _; rewrite a_ge0 => /eqP.
Qed.

Lemma ler0_sqrtr a : a <= 0 -> sqrt a = 0.
Proof.
rewrite /sqrtr; case: (sig2W _) => x /= _.
by have [//|_ /eqP//|->] := ltrgt0P a; rewrite mulf_eq0 orbb => /eqP.
Qed.

Lemma ltr0_sqrtr a : a < 0 -> sqrt a = 0.
Proof. by move=> /ltW; apply: ler0_sqrtr. Qed.

Variant sqrtr_spec a : R -> bool -> bool -> R -> Type :=
| IsNoSqrtr of a < 0 : sqrtr_spec a a false true 0
| IsSqrtr b of 0 <= b : sqrtr_spec a (b ^+ 2) true false b.

Lemma sqrtrP a : sqrtr_spec a a (0 <= a) (a < 0) (sqrt a).
Proof.
have [a_ge0|a_lt0] := ger0P a.
  by rewrite -{1 2}[a]sqr_sqrtr //; constructor.
by rewrite ltr0_sqrtr //; constructor.
Qed.

Lemma sqrtr_sqr a : sqrt (a ^+ 2) = `|a|.
Proof.
have /eqP : sqrt (a ^+ 2) ^+ 2 = `|a| ^+ 2.
  by rewrite -normrX ger0_norm ?sqr_sqrtr ?sqr_ge0.
rewrite eqf_sqr => /predU1P[-> //|ha].
have := sqrtr_ge0 (a ^+ 2); rewrite (eqP ha) oppr_ge0 normr_le0 => /eqP ->.
by rewrite normr0 oppr0.
Qed.

Lemma sqrtrM a b : 0 <= a -> sqrt (a * b) = sqrt a * sqrt b.
Proof.
case: (sqrtrP a) => // {}a a_ge0 _; case: (sqrtrP b) => [b_lt0 | {}b b_ge0].
  by rewrite mulr0 ler0_sqrtr // nmulr_lle0 ?mulr_ge0.
by rewrite mulrACA sqrtr_sqr ger0_norm ?mulr_ge0.
Qed.

Lemma sqrtr0 : sqrt 0 = 0 :> R.
Proof. by move: (sqrtr_sqr 0); rewrite exprS mul0r => ->; rewrite normr0. Qed.

Lemma sqrtr1 : sqrt 1 = 1 :> R.
Proof. by move: (sqrtr_sqr 1); rewrite expr1n => ->; rewrite normr1. Qed.

Lemma sqrtr_eq0 a : (sqrt a == 0) = (a <= 0).
Proof.
case: sqrtrP => [/ltW ->|b]; first by rewrite eqxx.
case: ltrgt0P => [b_gt0|//|->]; last by rewrite exprS mul0r lexx.
by rewrite lt_geF ?pmulr_rgt0.
Qed.

Lemma sqrtr_gt0 a : (0 < sqrt a) = (0 < a).
Proof. by rewrite lt0r sqrtr_ge0 sqrtr_eq0 -ltNge andbT. Qed.

Lemma eqr_sqrt a b : 0 <= a -> 0 <= b -> (sqrt a == sqrt b) = (a == b).
Proof.
move=> a_ge0 b_ge0; apply/eqP/eqP=> [HS|->] //.
by move: (sqr_sqrtr a_ge0); rewrite HS (sqr_sqrtr b_ge0).
Qed.

Lemma ler_wsqrtr : {homo @sqrt R : a b / a <= b}.
Proof.
move=> a b /= le_ab; case: (boolP (0 <= a))=> [pa|]; last first.
  by rewrite -ltNge; move/ltW; rewrite -sqrtr_eq0; move/eqP->.
rewrite -(@ler_pXn2r R 2) ?nnegrE ?sqrtr_ge0 //.
by rewrite !sqr_sqrtr // (le_trans pa).
Qed.

Lemma ler_psqrt : {in @nneg R &, {mono sqrt : a b / a <= b}}.
Proof.
apply: le_mono_in => x y x_gt0 y_gt0.
rewrite !lt_neqAle => /andP[neq_xy le_xy].
by rewrite ler_wsqrtr // eqr_sqrt // neq_xy.
Qed.

Lemma ler_sqrt a b : 0 <= b -> (sqrt a <= sqrt b) = (a <= b).
Proof.
move=> b_ge0; have [a_le0|a_gt0] := ler0P a; last first.
  by rewrite ler_psqrt // nnegrE ltW.
by rewrite ler0_sqrtr // sqrtr_ge0 (le_trans a_le0).
Qed.

Lemma ltr_sqrt a b : 0 < b -> (sqrt a < sqrt b) = (a < b).
Proof.
move=> b_gt0; have [a_le0|a_gt0] := ler0P a; last first.
  by rewrite (leW_mono_in ler_psqrt)//; apply: ltW.
by rewrite ler0_sqrtr // sqrtr_gt0 b_gt0 (le_lt_trans a_le0).
Qed.

Lemma sqrtrV x : 0 <= x -> sqrt (x^-1) = (sqrt x)^-1.
Proof.
case: ltrgt0P => // [x_gt0 _|->]; last by rewrite !(invr0, sqrtr0).
have sx_neq0 : sqrt x != 0 by rewrite sqrtr_eq0 -ltNge.
apply: (mulfI sx_neq0).
by rewrite -sqrtrM !(divff, ltW, sqrtr1) // lt0r_neq0.
Qed.

End RealClosedFieldTheory.

Notation "z ^*" := (conj_op z) (at level 2, format "z ^*") : ring_scope.
Notation "'i" := imaginary (at level 0) : ring_scope.

Section ClosedFieldTheory.

Variable C : numClosedFieldType.
Implicit Types a x y z : C.

Definition normCK : forall x, `|x| ^+ 2 = x * x^* := normCK.

Definition sqrCi : 'i ^+ 2 = -1 :> C := sqrCi.

Lemma mulCii : 'i * 'i = -1 :> C. Proof. exact: sqrCi. Qed.

Lemma conjCK : involutive (@conj_op C).
Proof.
have JE x : x^* = `|x|^+2 / x.
  have [->|x_neq0] := eqVneq x 0; first by rewrite rmorph0 invr0 mulr0.
  by apply: (canRL (mulfK _)) => //; rewrite mulrC -normCK.
move=> x; have [->|x_neq0] := eqVneq x 0; first by rewrite !rmorph0.
rewrite !JE normrM normfV exprMn normrX normr_id.
rewrite invfM exprVn (AC (2*2) (1*(2*3)*4))/= -invfM -exprMn.
by rewrite divff ?mul1r ?invrK // !expf_eq0 normr_eq0 //.
Qed.

Let Re2 z := z + z^*.
Definition nnegIm z := (0 <= 'i * (z^* - z)).
Definition argCle y z := nnegIm z ==> nnegIm y && (Re2 z <= Re2 y).

Variant rootC_spec n (x : C) : Type :=
  RootCspec (y : C) of if (n > 0)%N then y ^+ n = x else y = 0
                        & forall z, (n > 0)%N -> z ^+ n = x -> argCle y z.

Fact rootC_subproof n x : rootC_spec n x.
Proof.
have realRe2 u : Re2 u \is Num.real by
  rewrite realEsqr expr2 {2}/Re2 -{2}[u]conjCK addrC -rmorphD -normCK exprn_ge0.
have argCle_total : total argCle.
  move=> u v; rewrite /total /argCle.
  by do 2!case: (nnegIm _) => //; rewrite ?orbT //= real_leVge.
have argCle_trans : transitive argCle.
  move=> u v w /implyP geZuv /implyP geZvw; apply/implyP.
  by case/geZvw/andP=> /geZuv/andP[-> geRuv] /le_trans->.
pose p := 'X^n - (x *+ (n > 0))%:P; have [r0 Dp] := closed_field_poly_normal p.
have sz_p : size p = n.+1.
  rewrite size_polyDl ?size_polyXn // ltnS size_polyN size_polyC mulrn_eq0.
  by case: posnP => //; case: negP.
pose r := sort argCle r0; have r_arg: sorted argCle r by apply: sort_sorted.
have{} Dp: p = \prod_(z <- r) ('X - z%:P).
  rewrite Dp lead_coefE sz_p coefB coefXn coefC -mulrb -mulrnA mulnb lt0n andNb.
  by rewrite subr0 eqxx scale1r; apply/esym/perm_big; rewrite perm_sort.
have mem_rP z: (n > 0)%N -> reflect (z ^+ n = x) (z \in r).
  move=> n_gt0; rewrite -root_prod_XsubC -Dp rootE !hornerE n_gt0.
  by rewrite subr_eq0; apply: eqP.
exists r`_0 => [|z n_gt0 /(mem_rP z n_gt0) r_z].
  have sz_r: size r = n by apply: succn_inj; rewrite -sz_p Dp size_prod_XsubC.
  case: posnP => [n0 | n_gt0]; first by rewrite nth_default // sz_r n0.
  by apply/mem_rP=> //; rewrite mem_nth ?sz_r.
case: {Dp mem_rP}r r_z r_arg => // y r1 /[1!inE] /predU1P[-> _|r1z].
  by apply/implyP=> ->; rewrite lexx.
by move/(order_path_min argCle_trans)/allP->.
Qed.

Definition nthroot n x := let: RootCspec y _ _ := rootC_subproof n x in y.
Notation "n .-root" := (nthroot n) : ring_scope.
Notation sqrtC := 2.-root.

Fact Re_lock : unit. Proof. exact: tt. Qed.
Fact Im_lock : unit. Proof. exact: tt. Qed.
Definition Re z := locked_with Re_lock ((z + z^*) / 2%:R).
Definition Im z := locked_with Im_lock ('i * (z^* - z) / 2%:R).
Notation "'Re z" := (Re z) : ring_scope.
Notation "'Im z" := (Im z) : ring_scope.

Lemma ReE z : 'Re z = (z + z^*) / 2%:R. Proof. by rewrite ['Re _]unlock. Qed.
Lemma ImE z : 'Im z = 'i * (z^* - z) / 2%:R.
Proof. by rewrite ['Im _]unlock. Qed.

Let nz2 : 2 != 0 :> C. Proof. by rewrite pnatr_eq0. Qed.

Lemma normCKC x : `|x| ^+ 2 = x^* * x. Proof. by rewrite normCK mulrC. Qed.

Lemma mul_conjC_ge0 x : 0 <= x * x^*.
Proof. by rewrite -normCK exprn_ge0. Qed.

Lemma mul_conjC_gt0 x : (0 < x * x^* ) = (x != 0).
Proof.
have [->|x_neq0] := eqVneq; first by rewrite rmorph0 mulr0.
by rewrite -normCK exprn_gt0 ?normr_gt0.
Qed.

Lemma mul_conjC_eq0 x : (x * x^* == 0) = (x == 0).
Proof. by rewrite -normCK expf_eq0 normr_eq0. Qed.

Lemma conjC_ge0 x : (0 <= x^* ) = (0 <= x).
Proof.
wlog suffices: x / 0 <= x -> 0 <= x^*.
  by move=> IH; apply/idP/idP=> /IH; rewrite ?conjCK.
rewrite [in X in X -> _]le0r => /predU1P[-> | x_gt0]; first by rewrite rmorph0.
by rewrite -(pmulr_rge0 _ x_gt0) mul_conjC_ge0.
Qed.

Lemma conjC_nat n : (n%:R)^* = n%:R :> C. Proof. exact: rmorph_nat. Qed.
Lemma conjC0 : 0^* = 0 :> C. Proof. exact: rmorph0. Qed.
Lemma conjC1 : 1^* = 1 :> C. Proof. exact: rmorph1. Qed.
Lemma conjCN1 : (- 1)^* = - 1 :> C. Proof. exact: rmorphN1. Qed.
Lemma conjC_eq0 x : (x^* == 0) = (x == 0). Proof. exact: fmorph_eq0. Qed.

Lemma invC_norm x : x^-1 = `|x| ^- 2 * x^*.
Proof.
have [-> | nx_x] := eqVneq x 0; first by rewrite conjC0 mulr0 invr0.
by rewrite normCK invfM divfK ?conjC_eq0.
Qed.

(* Real number subset. *)

Lemma CrealE x : (x \is real) = (x^* == x).
Proof.
rewrite realEsqr ger0_def normrX normCK.
by have [-> | /mulfI/inj_eq-> //] := eqVneq x 0; rewrite rmorph0 !eqxx.
Qed.

Lemma CrealP {x} : reflect (x^* = x) (x \is real).
Proof. by rewrite CrealE; apply: eqP. Qed.

Lemma conj_Creal x : x \is real -> x^* = x.
Proof. by move/CrealP. Qed.

Lemma conj_normC z : `|z|^* = `|z|.
Proof. by rewrite conj_Creal ?normr_real. Qed.

Lemma CrealJ : {mono (@conj_op C) : x / x \is Num.real}.
Proof. by apply: (homo_mono1 conjCK) => x xreal; rewrite conj_Creal. Qed.

Lemma geC0_conj x : 0 <= x -> x^* = x.
Proof. by move=> /ger0_real/CrealP. Qed.

Lemma geC0_unit_exp x n : 0 <= x -> (x ^+ n.+1 == 1) = (x == 1).
Proof. by move=> x_ge0; rewrite pexpr_eq1. Qed.

(* Elementary properties of roots. *)

Ltac case_rootC := rewrite /nthroot; case: (rootC_subproof _ _).

Lemma root0C x : 0.-root x = 0. Proof. by case_rootC. Qed.

Lemma rootCK n : (n > 0)%N -> cancel n.-root (fun x => x ^+ n).
Proof. by case: n => //= n _ x; case_rootC. Qed.

Lemma root1C x : 1.-root x = x. Proof. exact: (@rootCK 1). Qed.

Lemma rootC0 n : n.-root 0 = 0.
Proof.
have [-> | n_gt0] := posnP n; first by rewrite root0C.
by have /eqP := rootCK n_gt0 0; rewrite expf_eq0 n_gt0 /= => /eqP.
Qed.

Lemma rootC_inj n : (n > 0)%N -> injective n.-root.
Proof. by move/rootCK/can_inj. Qed.

Lemma eqr_rootC n : (n > 0)%N -> {mono n.-root : x y / x == y}.
Proof. by move/rootC_inj/inj_eq. Qed.

Lemma rootC_eq0 n x : (n > 0)%N -> (n.-root x == 0) = (x == 0).
Proof. by move=> n_gt0; rewrite -{1}(rootC0 n) eqr_rootC. Qed.

(* Rectangular coordinates. *)

Lemma nonRealCi : ('i : C) \isn't real.
Proof. by rewrite realEsqr sqrCi oppr_ge0 lt_geF ?ltr01. Qed.

Lemma neq0Ci : 'i != 0 :> C. Proof. by apply: contraNneq nonRealCi => ->. Qed.

Lemma normCi : `|'i| = 1 :> C.
Proof. by apply/eqP; rewrite -(@pexpr_eq1 _ _ 2) // -normrX sqrCi normrN1. Qed.

Lemma invCi : 'i^-1 = - 'i :> C.
Proof. by rewrite -div1r -[1]opprK -sqrCi mulNr mulfK ?neq0Ci. Qed.

Lemma conjCi : 'i^* = - 'i :> C.
Proof. by rewrite -invCi invC_norm normCi expr1n invr1 mul1r. Qed.

Lemma Crect x : x = 'Re x + 'i * 'Im x.
Proof.
rewrite !(ReE, ImE) 2!mulrA mulCii mulN1r opprB -mulrDl.
by rewrite addrACA subrr addr0 mulrDl -splitr.
Qed.

Lemma eqCP x y : x = y <-> ('Re x = 'Re y) /\ ('Im x = 'Im y).
Proof. by split=> [->//|[eqRe eqIm]]; rewrite [x]Crect [y]Crect eqRe eqIm. Qed.

Lemma eqC x y : (x == y) = ('Re x == 'Re y) && ('Im x == 'Im y).
Proof. by apply/eqP/(andPP eqP eqP) => /eqCP. Qed.

Lemma Creal_Re x : 'Re x \is real.
Proof. by rewrite ReE CrealE fmorph_div rmorph_nat rmorphD /= conjCK addrC. Qed.

Lemma Creal_Im x : 'Im x \is real.
Proof.
rewrite ImE CrealE fmorph_div rmorph_nat rmorphM /= rmorphB conjCK.
by rewrite conjCi -opprB mulrNN.
Qed.
Hint Resolve Creal_Re Creal_Im : core.

Fact Re_is_additive : additive Re.
Proof. by move=> x y; rewrite !ReE rmorphB addrACA -opprD mulrBl. Qed.
#[export]
HB.instance Definition _ := GRing.isAdditive.Build C C Re Re_is_additive.

Fact Im_is_additive : additive Im.
Proof.
by move=> x y; rewrite !ImE rmorphB opprD addrACA -opprD mulrBr mulrBl.
Qed.
#[export]
HB.instance Definition _ := GRing.isAdditive.Build C C Im Im_is_additive.

Lemma Creal_ImP z : reflect ('Im z = 0) (z \is real).
Proof.
rewrite ImE CrealE -subr_eq0 -(can_eq (mulKf neq0Ci)) mulr0.
by rewrite -(can_eq (divfK nz2)) mul0r; apply: eqP.
Qed.

Lemma Creal_ReP z : reflect ('Re z = z) (z \in real).
Proof.
rewrite (sameP (Creal_ImP z) eqP) -(can_eq (mulKf neq0Ci)) mulr0.
by rewrite -(inj_eq (addrI ('Re z))) addr0 -Crect eq_sym; apply: eqP.
Qed.

Lemma ReMl : {in real, forall x, {morph Re : z / x * z}}.
Proof.
by move=> x Rx z /=; rewrite !ReE rmorphM /= (conj_Creal Rx) -mulrDr -mulrA.
Qed.

Lemma ReMr : {in real, forall x, {morph Re : z / z * x}}.
Proof. by move=> x Rx z /=; rewrite mulrC ReMl // mulrC. Qed.

Lemma ImMl : {in real, forall x, {morph Im : z / x * z}}.
Proof.
by move=> x Rx z; rewrite !ImE rmorphM /= (conj_Creal Rx) -mulrBr mulrCA !mulrA.
Qed.

Lemma ImMr : {in real, forall x, {morph Im : z / z * x}}.
Proof. by move=> x Rx z /=; rewrite mulrC ImMl // mulrC. Qed.

Lemma Re_i : 'Re 'i = 0. Proof. by rewrite ReE conjCi subrr mul0r. Qed.

Lemma Im_i : 'Im 'i = 1.
Proof.
rewrite ImE conjCi -opprD mulrN -mulr2n mulrnAr mulCii.
by rewrite mulNrn opprK divff.
Qed.

Lemma Re_conj z : 'Re z^* = 'Re z.
Proof. by rewrite !ReE addrC conjCK. Qed.

Lemma Im_conj z : 'Im z^* = - 'Im z.
Proof. by rewrite !ImE -mulNr -mulrN opprB conjCK. Qed.

Lemma Re_rect : {in real &, forall x y, 'Re (x + 'i * y) = x}.
Proof.
move=> x y Rx Ry; rewrite /= raddfD /= (Creal_ReP x Rx).
by rewrite ReMr // Re_i mul0r addr0.
Qed.

Lemma Im_rect : {in real &, forall x y, 'Im (x + 'i * y) = y}.
Proof.
move=> x y Rx Ry; rewrite /= raddfD /= (Creal_ImP x Rx) add0r.
by rewrite ImMr // Im_i mul1r.
Qed.

Lemma conjC_rect : {in real &, forall x y, (x + 'i * y)^* = x - 'i * y}.
Proof.
by move=> x y Rx Ry; rewrite /= rmorphD rmorphM /= conjCi mulNr !conj_Creal.
Qed.

Lemma addC_rect x1 y1 x2 y2 :
  (x1 + 'i * y1) + (x2 + 'i * y2) = x1 + x2 + 'i * (y1 + y2).
Proof. by rewrite addrACA -mulrDr. Qed.

Lemma oppC_rect x y : - (x + 'i * y)  = - x + 'i * (- y).
Proof. by rewrite mulrN -opprD. Qed.

Lemma subC_rect x1 y1 x2 y2 :
  (x1 + 'i * y1) - (x2 + 'i * y2) = x1 - x2 + 'i * (y1 - y2).
Proof. by rewrite oppC_rect addC_rect. Qed.

Lemma mulC_rect x1 y1 x2 y2 : (x1 + 'i * y1) * (x2 + 'i * y2) =
                              x1 * x2 - y1 * y2 + 'i * (x1 * y2 + x2 * y1).
Proof.
rewrite mulrDl !mulrDr (AC (2*2) (1*4*(2*3)))/= mulrACA.
by rewrite -expr2 sqrCi mulN1r -!mulrA [_ * ('i * _)]mulrCA [_ * y1]mulrC.
Qed.

Lemma ImM x y : 'Im (x * y) = 'Re x * 'Im y + 'Re y * 'Im x.
Proof.
rewrite [x in LHS]Crect [y in LHS]Crect mulC_rect.
by rewrite !(Im_rect, rpredB, rpredD, rpredM).
Qed.

Lemma ImMil x : 'Im ('i * x) = 'Re x.
Proof. by rewrite ImM Re_i Im_i mul0r mulr1 add0r. Qed.

Lemma ReMil x : 'Re ('i * x) = - 'Im x.
Proof. by rewrite -ImMil mulrA mulCii mulN1r raddfN. Qed.

Lemma ReMir x : 'Re (x * 'i) = - 'Im x. Proof. by rewrite mulrC ReMil. Qed.

Lemma ImMir x : 'Im (x * 'i) = 'Re x. Proof. by rewrite mulrC ImMil. Qed.

Lemma ReM x y : 'Re (x * y) = 'Re x * 'Re y - 'Im x * 'Im y.
Proof. by rewrite -ImMil mulrCA ImM ImMil ReMil mulNr ['Im _ * _]mulrC. Qed.

Lemma normC2_rect :
  {in real &, forall x y, `|x + 'i * y| ^+ 2 = x ^+ 2 + y ^+ 2}.
Proof.
move=> x y Rx Ry; rewrite /= normCK rmorphD rmorphM /= conjCi !conj_Creal //.
by rewrite mulrC mulNr -subr_sqr exprMn sqrCi mulN1r opprK.
Qed.

Lemma normC2_Re_Im z : `|z| ^+ 2 = 'Re z ^+ 2 + 'Im z ^+ 2.
Proof. by rewrite -normC2_rect -?Crect. Qed.

Lemma invC_Crect x y : (x + 'i * y)^-1  = (x^* - 'i * y^*) / `|x + 'i * y| ^+ 2.
Proof. by rewrite /= invC_norm mulrC !rmorphE rmorphM /= conjCi mulNr. Qed.

Lemma invC_rect :
  {in real &, forall x y, (x + 'i * y)^-1  = (x - 'i * y) / (x ^+ 2 + y ^+ 2)}.
Proof. by move=> x y Rx Ry; rewrite invC_Crect normC2_rect ?conj_Creal. Qed.

Lemma ImV x : 'Im x^-1 = - 'Im x / `|x| ^+ 2.
Proof.
rewrite [x in LHS]Crect invC_rect// ImMr ?(rpredV, rpredD, rpredX)//.
by rewrite -mulrN Im_rect ?rpredN// -normC2_rect// -Crect.
Qed.

Lemma ReV x : 'Re x^-1 = 'Re x / `|x| ^+ 2.
Proof.
rewrite [x in LHS]Crect invC_rect// ReMr ?(rpredV, rpredD, rpredX)//.
by rewrite -mulrN Re_rect ?rpredN// -normC2_rect// -Crect.
Qed.

Lemma rectC_mulr x y z : (x + 'i * y) * z = x * z + 'i * (y * z).
Proof. by rewrite mulrDl mulrA. Qed.

Lemma rectC_mull x y z : z * (x + 'i * y) = z * x + 'i * (z * y).
Proof. by rewrite mulrDr mulrCA. Qed.

Lemma divC_Crect x1 y1 x2 y2 :
  (x1 + 'i * y1) / (x2 + 'i * y2) =
  (x1 * x2^* + y1 * y2^* + 'i * (x2^* * y1 - x1 * y2^*)) /
    `|x2 + 'i * y2| ^+ 2.
Proof.
rewrite invC_Crect// -mulrN [_ / _]rectC_mulr mulC_rect !mulrA -mulrBl.
rewrite [_ * _ * y1]mulrAC -mulrDl mulrA -mulrDl !(mulrN, mulNr) opprK.
by rewrite [- _ + _]addrC.
Qed.

Lemma divC_rect x1 y1 x2 y2 :
     x1 \is real -> y1 \is real -> x2 \is real -> y2 \is real ->
  (x1 + 'i * y1) / (x2 + 'i * y2) =
  (x1 * x2 + y1 * y2 + 'i * (x2 * y1 - x1 * y2)) /
    (x2 ^+ 2 + y2 ^+ 2).
Proof. by move=> *; rewrite divC_Crect normC2_rect ?conj_Creal. Qed.

Lemma Im_div x y : 'Im (x / y) = ('Re y * 'Im x - 'Re x * 'Im y) / `|y| ^+ 2.
Proof. by rewrite ImM ImV ReV mulrA [X in _ + X]mulrAC -mulrDl mulrN addrC. Qed.

Lemma Re_div x y : 'Re (x / y) = ('Re x * 'Re y + 'Im x * 'Im y) / `|y| ^+ 2.
Proof. by rewrite ReM ImV ReV !mulrA -mulrBl mulrN opprK. Qed.

Lemma leif_normC_Re_Creal z : `|'Re z| <= `|z| ?= iff (z \is real).
Proof.
rewrite -(mono_in_leif ler_sqr); try by rewrite qualifE /=.
rewrite [`|'Re _| ^+ 2]normCK conj_Creal // normC2_Re_Im -expr2.
rewrite addrC -leifBLR subrr (sameP (Creal_ImP _) eqP) -sqrf_eq0 eq_sym.
by apply: leif_eq; rewrite -realEsqr.
Qed.

Lemma leif_Re_Creal z : 'Re z <= `|z| ?= iff (0 <= z).
Proof.
have ubRe: 'Re z <= `|'Re z| ?= iff (0 <= 'Re z).
  by rewrite ger0_def eq_sym; apply/leif_eq/real_ler_norm.
congr (_ <= _ ?= iff _): (leif_trans ubRe (leif_normC_Re_Creal z)).
apply/andP/idP=> [[zRge0 /Creal_ReP <- //] | z_ge0].
by have Rz := ger0_real z_ge0; rewrite (Creal_ReP _ _).
Qed.

(* Equality from polar coordinates, for the upper plane. *)
Lemma eqC_semipolar x y :
  `|x| = `|y| -> 'Re x = 'Re y -> 0 <= 'Im x * 'Im y -> x = y.
Proof.
move=> eq_norm eq_Re sign_Im.
rewrite [x]Crect [y]Crect eq_Re; congr (_ + 'i * _).
have /eqP := congr1 (fun z => z ^+ 2) eq_norm.
rewrite !normC2_Re_Im eq_Re (can_eq (addKr _)) eqf_sqr => /pred2P[] // eq_Im.
rewrite eq_Im mulNr -expr2 oppr_ge0 real_exprn_even_le0 //= in sign_Im.
by rewrite eq_Im (eqP sign_Im) oppr0.
Qed.

(* Nth roots. *)

Let argCleP y z :
  reflect (0 <= 'Im z -> 0 <= 'Im y /\ 'Re z <= 'Re y) (argCle y z).
Proof.
suffices dIm x: nnegIm x = (0 <= 'Im x).
  rewrite /argCle !dIm !(ImE, ReE) ler_pM2r ?invr_gt0 ?ltr0n //.
  by apply: (iffP implyP) => geZyz /geZyz/andP.
by rewrite (ImE x) pmulr_lge0 ?invr_gt0 ?ltr0n //; congr (0 <= _ * _).
Qed.

Lemma rootC_Re_max n x y :
  (n > 0)%N -> y ^+ n = x -> 0 <= 'Im y -> 'Re y <= 'Re (n.-root x).
Proof.
by move=> n_gt0 yn_x leI0y; case_rootC=> z /= _ /(_ y n_gt0 yn_x)/argCleP[].
Qed.

Let neg_unity_root n : (n > 1)%N -> exists2 w : C, w ^+ n = 1 & 'Re w < 0.
Proof.
move=> n_gt1; have [|w /eqP pw_0] := closed_rootP (\poly_(i < n) (1 : C)) _.
  by rewrite size_poly_eq ?oner_eq0 // -(subnKC n_gt1).
rewrite horner_poly (eq_bigr _ (fun _ _ => mul1r _)) in pw_0.
have wn1: w ^+ n = 1 by apply/eqP; rewrite -subr_eq0 subrX1 pw_0 mulr0.
suffices /existsP[i ltRwi0]: [exists i : 'I_n, 'Re (w ^+ i) < 0].
  by exists (w ^+ i) => //; rewrite exprAC wn1 expr1n.
apply: contra_eqT (congr1 Re pw_0) => /existsPn geRw0.
rewrite raddf_sum raddf0 /= (bigD1 (Ordinal (ltnW n_gt1))) //=.
rewrite (Creal_ReP _ _) ?rpred1 // gt_eqF ?ltr_wpDr ?ltr01 //=.
by apply: sumr_ge0 => i _; rewrite real_leNgt ?rpred0.
Qed.

Lemma Im_rootC_ge0 n x : (n > 1)%N -> 0 <= 'Im (n.-root x).
Proof.
set y := n.-root x => n_gt1; have n_gt0 := ltnW n_gt1.
apply: wlog_neg; rewrite -real_ltNge ?rpred0 // => ltIy0.
suffices [z zn_x leI0z]: exists2 z, z ^+ n = x & 'Im z >= 0.
  by rewrite /y; case_rootC => /= y1 _ /(_ z n_gt0 zn_x)/argCleP[].
have [w wn1 ltRw0] := neg_unity_root n_gt1.
wlog leRI0yw: w wn1 ltRw0 / 0 <= 'Re y * 'Im w.
  move=> IHw; have: 'Re y * 'Im w \is real by rewrite rpredM.
  case/real_ge0P=> [|/ltW leRIyw0]; first exact: IHw.
  apply: (IHw w^* ); rewrite ?Re_conj ?Im_conj ?mulrN ?oppr_ge0 //.
  by rewrite -rmorphXn wn1 rmorph1.
exists (w * y); first by rewrite exprMn wn1 mul1r rootCK.
rewrite [w]Crect [y]Crect mulC_rect.
by rewrite Im_rect ?rpredD ?rpredN 1?rpredM // addr_ge0 // ltW ?nmulr_rgt0.
Qed.

Lemma rootC_lt0 n x : (1 < n)%N -> (n.-root x < 0) = false.
Proof.
set y := n.-root x => n_gt1; have n_gt0 := ltnW n_gt1.
apply: negbTE; apply: wlog_neg => /negbNE lt0y; rewrite le_gtF //.
have Rx: x \is real by rewrite -[x](rootCK n_gt0) rpredX // ltr0_real.
have Re_y: 'Re y = y by apply/Creal_ReP; rewrite ltr0_real.
have [z zn_x leR0z]: exists2 z, z ^+ n = x & 'Re z >= 0.
  have [w wn1 ltRw0] := neg_unity_root n_gt1.
  exists (w * y); first by rewrite exprMn wn1 mul1r rootCK.
  by rewrite ReMr ?ltr0_real // ltW // nmulr_lgt0.
without loss leI0z: z zn_x leR0z / 'Im z >= 0.
  move=> IHz; have: 'Im z \is real by [].
  case/real_ge0P=> [|/ltW leIz0]; first exact: IHz.
  apply: (IHz z^* ); rewrite ?Re_conj ?Im_conj ?oppr_ge0 //.
  by rewrite -rmorphXn /= zn_x conj_Creal.
by apply: le_trans leR0z _; rewrite -Re_y ?rootC_Re_max ?ltr0_real.
Qed.

Lemma rootC_ge0 n x : (n > 0)%N -> (0 <= n.-root x) = (0 <= x).
Proof.
set y := n.-root x => n_gt0.
apply/idP/idP=> [/(exprn_ge0 n) | x_ge0]; first by rewrite rootCK.
rewrite -(ge_leif (leif_Re_Creal y)).
have Ray: `|y| \is real by apply: normr_real.
rewrite -(Creal_ReP _ Ray) rootC_Re_max ?(Creal_ImP _ Ray) //.
by rewrite -normrX rootCK // ger0_norm.
Qed.

Lemma rootC_gt0 n x : (n > 0)%N -> (n.-root x > 0) = (x > 0).
Proof. by move=> n_gt0; rewrite !lt0r rootC_ge0 ?rootC_eq0. Qed.

Lemma rootC_le0 n x : (1 < n)%N -> (n.-root x <= 0) = (x == 0).
Proof.
by move=> n_gt1; rewrite le_eqVlt rootC_lt0 // orbF rootC_eq0 1?ltnW.
Qed.

Lemma ler_rootCl n : (n > 0)%N -> {in Num.nneg, {mono n.-root : x y / x <= y}}.
Proof.
move=> n_gt0 x x_ge0 y; have [y_ge0 | not_y_ge0] := boolP (0 <= y).
  by rewrite -(ler_pXn2r n_gt0) ?qualifE /= ?rootC_ge0 ?rootCK.
rewrite (contraNF (@le_trans _ _ _ 0 _ _)) ?rootC_ge0 //.
by rewrite (contraNF (le_trans x_ge0)).
Qed.

Lemma ler_rootC n : (n > 0)%N -> {in Num.nneg &, {mono n.-root : x y / x <= y}}.
Proof. by move=> n_gt0 x y x_ge0 _; apply: ler_rootCl. Qed.

Lemma ltr_rootCl n : (n > 0)%N -> {in Num.nneg, {mono n.-root : x y / x < y}}.
Proof. by move=> n_gt0 x x_ge0 y; rewrite !lt_def ler_rootCl ?eqr_rootC. Qed.

Lemma ltr_rootC n : (n > 0)%N -> {in Num.nneg &, {mono n.-root : x y / x < y}}.
Proof. by move/ler_rootC/leW_mono_in. Qed.

Lemma exprCK n x : (0 < n)%N -> 0 <= x -> n.-root (x ^+ n) = x.
Proof.
move=> n_gt0 x_ge0; apply/eqP.
by rewrite -(eqrXn2 n_gt0) ?rootC_ge0 ?exprn_ge0 ?rootCK.
Qed.

Lemma norm_rootC n x : `|n.-root x| = n.-root `|x|.
Proof.
have [-> | n_gt0] := posnP n; first by rewrite !root0C normr0.
by apply/eqP; rewrite -(eqrXn2 n_gt0) ?rootC_ge0 // -normrX !rootCK.
Qed.

Lemma rootCX n x k : (n > 0)%N -> 0 <= x -> n.-root (x ^+ k) = n.-root x ^+ k.
Proof.
move=> n_gt0 x_ge0; apply/eqP.
by rewrite -(eqrXn2 n_gt0) ?(exprn_ge0, rootC_ge0) // 1?exprAC !rootCK.
Qed.

Lemma rootC1 n : (n > 0)%N -> n.-root 1 = 1.
Proof. by move/(rootCX 0)/(_ ler01). Qed.

Lemma rootCpX n x k : (k > 0)%N -> 0 <= x -> n.-root (x ^+ k) = n.-root x ^+ k.
Proof.
by case: n => [|n] k_gt0; [rewrite !root0C expr0n gtn_eqF | apply: rootCX].
Qed.

Lemma rootCV n x : 0 <= x -> n.-root x^-1 = (n.-root x)^-1.
Proof.
move=> x_ge0; have [->|n_gt0] := posnP n; first by rewrite !root0C invr0.
apply/eqP.
by rewrite -(eqrXn2 n_gt0) ?(invr_ge0, rootC_ge0) // !exprVn !rootCK.
Qed.

Lemma rootC_eq1 n x : (n > 0)%N -> (n.-root x == 1) = (x == 1).
Proof. by move=> n_gt0; rewrite -{1}(rootC1 n_gt0) eqr_rootC. Qed.

Lemma rootC_ge1 n x : (n > 0)%N -> (n.-root x >= 1) = (x >= 1).
Proof.
by move=> n_gt0; rewrite -{1}(rootC1 n_gt0) ler_rootCl // qualifE /= ler01.
Qed.

Lemma rootC_gt1 n x : (n > 0)%N -> (n.-root x > 1) = (x > 1).
Proof. by move=> n_gt0; rewrite !lt_def rootC_eq1 ?rootC_ge1. Qed.

Lemma rootC_le1 n x : (n > 0)%N -> 0 <= x -> (n.-root x <= 1) = (x <= 1).
Proof. by move=> n_gt0 x_ge0; rewrite -{1}(rootC1 n_gt0) ler_rootCl. Qed.

Lemma rootC_lt1 n x : (n > 0)%N -> 0 <= x -> (n.-root x < 1) = (x < 1).
Proof. by move=> n_gt0 x_ge0; rewrite !lt_neqAle rootC_eq1 ?rootC_le1. Qed.

Lemma rootCMl n x z : 0 <= x -> n.-root (x * z) = n.-root x * n.-root z.
Proof.
rewrite le0r => /predU1P[-> | x_gt0]; first by rewrite !(mul0r, rootC0).
have [| n_gt1 | ->] := ltngtP n 1; last by rewrite !root1C.
  by case: n => //; rewrite !root0C mul0r.
have [x_ge0 n_gt0] := (ltW x_gt0, ltnW n_gt1).
have nx_gt0: 0 < n.-root x by rewrite rootC_gt0.
have Rnx: n.-root x \is real by rewrite ger0_real ?ltW.
apply: eqC_semipolar; last 1 first; try apply/eqP.
- by rewrite ImMl // !(Im_rootC_ge0, mulr_ge0, rootC_ge0).
- by rewrite -(eqrXn2 n_gt0) // -!normrX exprMn !rootCK.
rewrite eq_le; apply/andP; split; last first.
  rewrite rootC_Re_max ?exprMn ?rootCK ?ImMl //.
  by rewrite mulr_ge0 ?Im_rootC_ge0 ?ltW.
rewrite -[n.-root _](mulVKf (negbT (gt_eqF nx_gt0))) !(ReMl Rnx) //.
rewrite ler_pM2l // rootC_Re_max ?exprMn ?exprVn ?rootCK ?mulKf ?gt_eqF //.
by rewrite ImMl ?rpredV // mulr_ge0 ?invr_ge0 ?Im_rootC_ge0 ?ltW.
Qed.

Lemma rootCMr n x z : 0 <= x -> n.-root (z * x) = n.-root z * n.-root x.
Proof. by move=> x_ge0; rewrite mulrC rootCMl // mulrC. Qed.

Lemma imaginaryCE : 'i = sqrtC (-1).
Proof.
have : sqrtC (-1) ^+ 2 - 'i ^+ 2 == 0 by rewrite sqrCi rootCK // subrr.
rewrite subr_sqr mulf_eq0 subr_eq0 addr_eq0; have [//|_/= /eqP sCN1E] := eqP.
by have := @Im_rootC_ge0 2 (-1) isT; rewrite sCN1E raddfN /= Im_i ler0N1.
Qed.

(* More properties of n.-root will be established in cyclotomic.v. *)

(* The proper form of the Arithmetic - Geometric Mean inequality. *)

Lemma leif_rootC_AGM (I : finType) (A : {pred I}) (n := #|A|) E :
    {in A, forall i, 0 <= E i} ->
  n.-root (\prod_(i in A) E i) <= (\sum_(i in A) E i) / n%:R
                             ?= iff [forall i in A, forall j in A, E i == E j].
Proof.
move=> Ege0; have [n0 | n_gt0] := posnP n.
  rewrite n0 root0C invr0 mulr0; apply/leif_refl/forall_inP=> i.
  by rewrite (card0_eq n0).
rewrite -(mono_in_leif (ler_pXn2r n_gt0)) ?rootCK //=; first 1 last.
- by rewrite qualifE /= rootC_ge0 // prodr_ge0.
- by rewrite rpred_div ?rpred_nat ?rpred_sum.
exact: leif_AGM.
Qed.

(* Square root. *)

Lemma sqrtC0 : sqrtC 0 = 0. Proof. exact: rootC0. Qed.
Lemma sqrtC1 : sqrtC 1 = 1. Proof. exact: rootC1. Qed.
Lemma sqrtCK x : sqrtC x ^+ 2 = x. Proof. exact: rootCK. Qed.
Lemma sqrCK x : 0 <= x -> sqrtC (x ^+ 2) = x. Proof. exact: exprCK. Qed.

Lemma sqrtC_ge0 x : (0 <= sqrtC x) = (0 <= x). Proof. exact: rootC_ge0. Qed.
Lemma sqrtC_eq0 x : (sqrtC x == 0) = (x == 0). Proof. exact: rootC_eq0. Qed.
Lemma sqrtC_gt0 x : (sqrtC x > 0) = (x > 0). Proof. exact: rootC_gt0. Qed.
Lemma sqrtC_lt0 x : (sqrtC x < 0) = false. Proof. exact: rootC_lt0. Qed.
Lemma sqrtC_le0 x : (sqrtC x <= 0) = (x == 0). Proof. exact: rootC_le0. Qed.

Lemma ler_sqrtC : {in Num.nneg &, {mono sqrtC : x y / x <= y}}.
Proof. exact: ler_rootC. Qed.
Lemma ltr_sqrtC : {in Num.nneg &, {mono sqrtC : x y / x < y}}.
Proof. exact: ltr_rootC. Qed.
Lemma eqr_sqrtC : {mono sqrtC : x y / x == y}.
Proof. exact: eqr_rootC. Qed.
Lemma sqrtC_inj : injective sqrtC.
Proof. exact: rootC_inj. Qed.
Lemma sqrtCM : {in Num.nneg &, {morph sqrtC : x y / x * y}}.
Proof. by move=> x y _; apply: rootCMr. Qed.

Lemma sqrCK_P x : reflect (sqrtC (x ^+ 2) = x) ((0 <= 'Im x) && ~~ (x < 0)).
Proof.
apply: (iffP andP) => [[leI0x not_gt0x] | <-]; last first.
  by rewrite sqrtC_lt0 Im_rootC_ge0.
have /eqP := sqrtCK (x ^+ 2); rewrite eqf_sqr => /pred2P[] // defNx.
apply: sqrCK; rewrite -real_leNgt ?rpred0 // in not_gt0x;
apply/Creal_ImP/le_anti;
by rewrite leI0x -oppr_ge0 -raddfN -defNx Im_rootC_ge0.
Qed.

Lemma normC_def x : `|x| = sqrtC (x * x^* ).
Proof. by rewrite -normCK sqrCK. Qed.

Lemma norm_conjC x : `|x^*| = `|x|.
Proof. by rewrite !normC_def conjCK mulrC. Qed.

Lemma normC_rect :
  {in real &, forall x y, `|x + 'i * y| = sqrtC (x ^+ 2 + y ^+ 2)}.
Proof. by move=> x y Rx Ry; rewrite /= normC_def -normCK normC2_rect. Qed.

Lemma normC_Re_Im z : `|z| = sqrtC ('Re z ^+ 2 + 'Im z ^+ 2).
Proof. by rewrite normC_def -normCK normC2_Re_Im. Qed.

(* Norm sum (in)equalities. *)

Lemma normCDeq x y :
    `|x + y| = `|x| + `|y| ->
  {t : C | `|t| == 1 & (x, y) = (`|x| * t, `|y| * t)}.
Proof.
move=> lin_xy; apply: sig2_eqW; pose u z := if z == 0 then 1 else z / `|z|.
have uE z: (`|u z| = 1) * (`|z| * u z = z).
  rewrite /u; have [->|nz_z] := eqVneq; first by rewrite normr0 normr1 mul0r.
  by rewrite normf_div normr_id mulrCA divff ?mulr1 ?normr_eq0.
have [->|nz_x] := eqVneq x 0; first by exists (u y); rewrite uE ?normr0 ?mul0r.
exists (u x); rewrite uE // /u (negPf nz_x); congr (_ , _).
have{lin_xy} def2xy: `|x| * `|y| *+ 2 = x * y ^* + y * x ^*.
  apply/(addrI (x * x^* ))/(addIr (y * y^* )); rewrite -2!{1}normCK -sqrrD.
  by rewrite addrA -addrA -!mulrDr -mulrDl -rmorphD -normCK lin_xy.
have def_xy: x * y^* = y * x^*.
  apply/eqP; rewrite -subr_eq0 -[_ == 0](@expf_eq0 _ _ 2).
  rewrite (canRL (subrK _) (subr_sqrDB _ _)) opprK -def2xy exprMn_n exprMn.
  by rewrite mulrN (@GRing.mul C).[AC (2*2) (1*4*(3*2))] -!normCK mulNrn addNr.
have{def_xy def2xy} def_yx: `|y * x| = y * x^*.
  by apply: (mulIf nz2); rewrite !mulr_natr mulrC normrM def2xy def_xy.
rewrite -{1}(divfK nz_x y) invC_norm mulrCA -{}def_yx !normrM invfM.
by rewrite mulrCA divfK ?normr_eq0 // mulrAC mulrA.
Qed.

Lemma normC_sum_eq (I : finType) (P : pred I) (F : I -> C) :
     `|\sum_(i | P i) F i| = \sum_(i | P i) `|F i| ->
   {t : C | `|t| == 1 & forall i, P i -> F i = `|F i| * t}.
Proof.
have [i /andP[Pi nzFi] | F0] := pickP [pred i | P i & F i != 0]; last first.
  exists 1 => [|i Pi]; first by rewrite normr1.
  by case/nandP: (F0 i) => [/negP[]// | /negbNE/eqP->]; rewrite normr0 mul0r.
rewrite !(bigD1 i Pi) /= => norm_sumF; pose Q j := P j && (j != i).
rewrite -normr_eq0 in nzFi; set c := F i / `|F i|; exists c => [|j Pj].
  by rewrite normrM normfV normr_id divff.
have [Qj | /nandP[/negP[]// | /negbNE/eqP->]] := boolP (Q j); last first.
  by rewrite mulrC divfK.
have: `|F i + F j| = `|F i| + `|F j|.
  do [rewrite !(bigD1 j Qj) /=; set z := \sum_(k | _) `|_|] in norm_sumF.
  apply/eqP; rewrite eq_le ler_normD -(lerD2r z) -addrA -norm_sumF addrA.
  by rewrite (le_trans (ler_normD _ _)) // lerD2l ler_norm_sum.
by case/normCDeq=> k _ [/(canLR (mulKf nzFi)) <-]; rewrite -(mulrC (F i)).
Qed.

Lemma normC_sum_eq1 (I : finType) (P : pred I) (F : I -> C) :
    `|\sum_(i | P i) F i| = (\sum_(i | P i) `|F i|) ->
     (forall i, P i -> `|F i| = 1) ->
   {t : C | `|t| == 1 & forall i, P i -> F i = t}.
Proof.
case/normC_sum_eq=> t t1 defF normF.
by exists t => // i Pi; rewrite defF // normF // mul1r.
Qed.

Lemma normC_sum_upper (I : finType) (P : pred I) (F G : I -> C) :
     (forall i, P i -> `|F i| <= G i) ->
     \sum_(i | P i) F i = \sum_(i | P i) G i ->
   forall i, P i -> F i = G i.
Proof.
set sumF := \sum_(i | _) _; set sumG := \sum_(i | _) _ => leFG eq_sumFG.
have posG i: P i -> 0 <= G i by move/leFG; apply: le_trans.
have norm_sumG: `|sumG| = sumG by rewrite ger0_norm ?sumr_ge0.
have norm_sumF: `|sumF| = \sum_(i | P i) `|F i|.
  apply/eqP; rewrite eq_le ler_norm_sum eq_sumFG norm_sumG -subr_ge0 -sumrB.
  by rewrite sumr_ge0 // => i Pi; rewrite subr_ge0 ?leFG.
have [t _ defF] := normC_sum_eq norm_sumF.
have [/(psumr_eq0P posG) G0 i Pi | nz_sumG] := eqVneq sumG 0.
  by apply/eqP; rewrite G0 // -normr_eq0 eq_le normr_ge0 -(G0 i Pi) leFG.
have t1: t = 1.
  apply: (mulfI nz_sumG); rewrite mulr1 -{1}norm_sumG -eq_sumFG norm_sumF.
  by rewrite mulr_suml -(eq_bigr _ defF).
have /psumr_eq0P eqFG i: P i -> 0 <= G i - F i.
  by move=> Pi; rewrite subr_ge0 defF // t1 mulr1 leFG.
move=> i /eqFG/(canRL (subrK _))->; rewrite ?add0r //.
by rewrite sumrB -/sumF eq_sumFG subrr.
Qed.

Lemma normCBeq x y :
  `|x - y| = `|x| - `|y| -> {t | `|t| == 1 & (x, y) = (`|x| * t, `|y| * t)}.
Proof.
set z := x - y; rewrite -(subrK y x) -/z => /(canLR (subrK _))/esym-Dx.
have [t t_1 [Dz Dy]] := normCDeq Dx.
by exists t; rewrite // Dx mulrDl -Dz -Dy.
Qed.

End ClosedFieldTheory.

Notation "n .-root" := (@nthroot _ n).
Notation sqrtC := 2.-root.
Notation "'i" := imaginary : ring_scope.
Notation "'Re z" := (Re z) : ring_scope.
Notation "'Im z" := (Im z) : ring_scope.

Arguments conjCK {C} x.
Arguments sqrCK {C} [x] le0x.
Arguments sqrCK_P {C x}.

#[global] Hint Extern 0 (is_true (in_mem ('Re _) _)) =>
  solve [apply: Creal_Re] : core.
#[global] Hint Extern 0 (is_true (in_mem ('Im _) _)) =>
  solve [apply: Creal_Im] : core.

Module Export Pdeg2.

Module NumClosed.

Section Pdeg2NumClosed.

Variables (F : numClosedFieldType) (p : {poly F}).

Hypothesis degp : size p = 3.

Let a := p`_2.
Let b := p`_1.
Let c := p`_0.

Let delta := b ^+ 2 - 4 * a * c.

Let r1 := (- b - sqrtC delta) / (2 * a).
Let r2 := (- b + sqrtC delta) / (2 * a).

Lemma deg2_poly_factor : p = a *: ('X - r1%:P) * ('X - r2%:P).
Proof. by apply: deg2_poly_factor; rewrite ?pnatr_eq0// sqrtCK. Qed.

Lemma deg2_poly_root1 : root p r1.
Proof. by apply: deg2_poly_root1; rewrite ?pnatr_eq0// sqrtCK. Qed.

Lemma deg2_poly_root2 : root p r2.
Proof. by apply: deg2_poly_root2; rewrite ?pnatr_eq0// sqrtCK. Qed.

End Pdeg2NumClosed.

End NumClosed.

Module NumClosedMonic.

Export FieldMonic.

Section Pdeg2NumClosedMonic.

Variables (F : numClosedFieldType) (p : {poly F}).

Hypothesis degp : size p = 3.
Hypothesis monicp : p \is monic.

Let a := p`_2.
Let b := p`_1.
Let c := p`_0.

Let delta := b ^+ 2 - 4 * c.

Let r1 := (- b - sqrtC delta) / 2.
Let r2 := (- b + sqrtC delta) / 2.

Lemma deg2_poly_factor : p = ('X - r1%:P) * ('X - r2%:P).
Proof. by apply: deg2_poly_factor; rewrite ?pnatr_eq0// sqrtCK. Qed.

Lemma deg2_poly_root1 : root p r1.
Proof. by apply: deg2_poly_root1; rewrite ?pnatr_eq0// sqrtCK. Qed.

Lemma deg2_poly_root2 : root p r2.
Proof. by apply: deg2_poly_root2; rewrite ?pnatr_eq0// sqrtCK. Qed.

End Pdeg2NumClosedMonic.
End NumClosedMonic.

Module Real.

Section Pdeg2Real.

Variable F : realFieldType.

Section Pdeg2RealConvex.

Variable p : {poly F}.
Hypothesis degp : size p = 3.

Let a := p`_2.
Let b := p`_1.
Let c := p`_0.

Hypothesis age0 : 0 <= a.

Let delta := b ^+ 2 - 4 * a * c.

Let pneq0 : p != 0. Proof. by rewrite -size_poly_gt0 degp. Qed.
Let aneq0 : a != 0.
Proof. by move: pneq0; rewrite -lead_coef_eq0 lead_coefE degp. Qed.
Let agt0 : 0 < a. Proof. by rewrite lt_def aneq0. Qed.
Let a4gt0 : 0 < 4 * a. Proof. by rewrite mulr_gt0 ?ltr0n. Qed.

Lemma deg2_poly_min x : p.[- b / (2 * a)] <= p.[x].
Proof.
rewrite [p]deg2_poly_canonical ?pnatr_eq0// -/a -/b -/c /delta !hornerE/=.
by rewrite ler_pM2l// lerD2r addrC mulNr subrr expr0n sqr_ge0.
Qed.

Lemma deg2_poly_minE : p.[- b / (2 * a)] = - delta / (4 * a).
Proof.
rewrite [p]deg2_poly_canonical ?pnatr_eq0// -/a -/b -/c -/delta !hornerE/=.
rewrite [X in X^+2]addrC [in LHS]mulNr subrr expr0n add0r mulNr.
by rewrite mulrC mulNr invfM mulrA mulfVK.
Qed.

Lemma deg2_poly_gt0 : reflect (forall x, 0 < p.[x]) (delta < 0).
Proof.
apply/(iffP idP) => [dlt0 x | /(_ (- b / (2 * a)))]; last first.
  by rewrite deg2_poly_minE ltr_pdivlMr// mul0r oppr_gt0.
apply: lt_le_trans (deg2_poly_min _).
by rewrite deg2_poly_minE ltr_pdivlMr// mul0r oppr_gt0.
Qed.

Lemma deg2_poly_ge0 : reflect (forall x, 0 <= p.[x]) (delta <= 0).
Proof.
apply/(iffP idP) => [dlt0 x | /(_ (- b / (2 * a)))]; last first.
  by rewrite deg2_poly_minE ler_pdivlMr// mul0r oppr_ge0.
apply: le_trans (deg2_poly_min _).
by rewrite deg2_poly_minE ler_pdivlMr// mul0r oppr_ge0.
Qed.

End Pdeg2RealConvex.

Section Pdeg2RealConcave.

Variable p : {poly F}.
Hypothesis degp : size p = 3.

Let a := p`_2.
Let b := p`_1.
Let c := p`_0.

Hypothesis ale0 : a <= 0.

Let delta := b ^+ 2 - 4 * a * c.

Let degpN : size (- p) = 3. Proof. by rewrite size_polyN. Qed.
Let b2a : - (- p)`_1 / (2 * (- p)`_2) = - b / (2 * a).
Proof. by rewrite !coefN mulrN divrNN. Qed.
Let deltaN : (- p)`_1 ^+ 2 - 4 * (- p)`_2 * (- p)`_0 = delta.
Proof. by rewrite !coefN sqrrN -mulrN opprK mulrN mulNr. Qed.

Lemma deg2_poly_max x : p.[x] <= p.[- b / (2 * a)].
Proof. by rewrite -lerN2 -!hornerN -b2a deg2_poly_min// coefN oppr_ge0. Qed.

Lemma deg2_poly_maxE : p.[- b / (2 * a)] = - delta / (4 * a).
Proof.
apply/eqP; rewrite [eqbRHS]mulNr -eqr_oppLR -hornerN -b2a.
by rewrite deg2_poly_minE// deltaN coefN mulrN divrNN.
Qed.

Lemma deg2_poly_lt0 : reflect (forall x, p.[x] < 0) (delta < 0).
Proof.
rewrite -deltaN; apply/(iffP (deg2_poly_gt0 _ _)); rewrite ?coefN ?oppr_ge0//.
- by move=> gt0 x; rewrite -oppr_gt0 -hornerN gt0.
- by move=> lt0 x; rewrite hornerN oppr_gt0 lt0.
Qed.

Lemma deg2_poly_le0 : reflect (forall x, p.[x] <= 0) (delta <= 0).
Proof.
rewrite -deltaN; apply/(iffP (deg2_poly_ge0 _ _)); rewrite ?coefN ?oppr_ge0//.
- by move=> ge0 x; rewrite -oppr_ge0 -hornerN ge0.
- by move=> le0 x; rewrite hornerN oppr_ge0 le0.
Qed.

End Pdeg2RealConcave.
End Pdeg2Real.

Section Pdeg2RealClosed.

Variable F : rcfType.

Section Pdeg2RealClosedConvex.

Variable p : {poly F}.
Hypothesis degp : size p = 3.

Let a := p`_2.
Let b := p`_1.
Let c := p`_0.

Let pneq0 : p != 0. Proof. by rewrite -size_poly_gt0 degp. Qed.
Let aneq0 : a != 0.
Proof. by move: pneq0; rewrite -lead_coef_eq0 lead_coefE degp. Qed.
Let sqa2 : 4 * a ^+ 2 = (2 * a) ^+ 2. Proof. by rewrite exprMn -natrX. Qed.
Let nz2 : 2 != 0 :> F. Proof. by rewrite pnatr_eq0. Qed.

Let delta := b ^+ 2 - 4 * a * c.

Let r1 := (- b - sqrt delta) / (2 * a).
Let r2 := (- b + sqrt delta) / (2 * a).

Lemma deg2_poly_factor : 0 <= delta -> p = a *: ('X - r1%:P) * ('X - r2%:P).
Proof. by move=> dge0; apply: deg2_poly_factor; rewrite ?sqr_sqrtr. Qed.

Lemma deg2_poly_root1 : 0 <= delta -> root p r1.
Proof. by move=> dge0; apply: deg2_poly_root1; rewrite ?sqr_sqrtr. Qed.

Lemma deg2_poly_root2 : 0 <= delta -> root p r2.
Proof. by move=> dge0; apply: deg2_poly_root2; rewrite ?sqr_sqrtr. Qed.

Lemma deg2_poly_noroot : reflect (forall x, ~~ root p x) (delta < 0).
Proof.
apply/(iffP idP) => [dlt0 x | /(_ r1)].
  case: ltgtP aneq0 => [agt0 _|alt0 _|//]; rewrite rootE; last first.
    exact/lt0r_neq0/(deg2_poly_gt0 degp (ltW alt0)).
  rewrite -oppr_eq0 -hornerN.
  apply/lt0r_neq0/deg2_poly_gt0; rewrite ?size_polyN ?coefN ?oppr_ge0 ?ltW//.
  by rewrite sqrrN -mulrA mulrNN mulrA.
by rewrite ltNge; apply: contraNN => ?; apply: deg2_poly_root1.
Qed.

Hypothesis age0 : 0 <= a.

Let agt0 : 0 < a. Proof. by rewrite lt_def aneq0. Qed.
Let a2gt0 : 0 < 2 * a. Proof. by rewrite mulr_gt0 ?ltr0n. Qed.
Let a4gt0 : 0 < 4 * a. Proof. by rewrite mulr_gt0 ?ltr0n. Qed.
Let aa4gt0 : 0 < 4 * a * a. Proof. by rewrite mulr_gt0 ?ltr0n. Qed.

Let xb4 x : (x + b / (2 * a)) ^+ 2 * (4 * a * a) = (x * (2 * a) + b) ^+ 2.
Proof.
have -> : 4 * a * a = (2 * a) ^+ 2 by rewrite expr2 mulrACA -natrM mulrA.
by rewrite -exprMn mulrDl mulfVK ?mulf_neq0 ?pnatr_eq0.
Qed.

Lemma deg2_poly_gt0l x : x < r1 -> 0 < p.[x].
Proof.
move=> xltr1; have [? | dge0] := ltP delta 0; first exact: deg2_poly_gt0.
have {}xltr1 : sqrt delta < - (x * (2 * a) + b).
  by rewrite ltrNr -ltrBrDr addrC -ltr_pdivlMr.
rewrite [p]deg2_poly_canonical// -/a -/b -/c -/delta !hornerE/=.
rewrite mulr_gt0// subr_gt0 ltr_pdivrMr// xb4 -sqrrN.
rewrite -ltr_sqrt ?sqrtr_sqr ?(lt_le_trans xltr1) ?ler_norm//.
by rewrite exprn_gt0 ?(le_lt_trans _ xltr1) ?sqrtr_ge0.
Qed.

Lemma deg2_poly_gt0r x : r2 < x -> 0 < p.[x].
Proof.
move=> xgtr2; have [? | dge0] := ltP delta 0; first exact: deg2_poly_gt0.
have {}xgtr2 : sqrt delta < x * (2 * a) + b.
  by rewrite -ltrBlDr addrC -ltr_pdivrMr.
rewrite [p]deg2_poly_canonical// -/a -/b -/c -/delta !hornerE/=.
rewrite mulr_gt0// subr_gt0 ltr_pdivrMr// xb4.
rewrite -ltr_sqrt ?sqrtr_sqr ?(lt_le_trans xgtr2) ?ler_norm//.
by rewrite exprn_gt0 ?(le_lt_trans _ xgtr2) ?sqrtr_ge0.
Qed.

Lemma deg2_poly_lt0m x : r1 < x < r2 -> p.[x] < 0.
Proof.
move=> /andP[r1ltx xltr2].
have [dle0 | dgt0] := leP delta 0.
  by move: (lt_trans r1ltx xltr2); rewrite /r1 /r2 ler0_sqrtr// oppr0 ltxx.
rewrite [p]deg2_poly_canonical// !hornerE/= -/a -/b -/c -/delta.
rewrite pmulr_rlt0// subr_lt0 ltr_pdivlMr// xb4 -ltr_sqrt// sqrtr_sqr ltr_norml.
by rewrite -ltrBlDr addrC -ltr_pdivrMr// r1ltx -ltrBrDr addrC -ltr_pdivlMr.
Qed.

Lemma deg2_poly_ge0l x : x <= r1 -> 0 <= p.[x].
Proof.
rewrite le_eqVlt => /orP[/eqP->|xltr1]; last exact/ltW/deg2_poly_gt0l.
have [dge0|dlt0] := leP 0 delta; last by apply: deg2_poly_ge0 => //; apply: ltW.
by rewrite le_eqVlt (rootP (deg2_poly_root1 dge0)) eqxx.
Qed.

Lemma deg2_poly_ge0r x : r2 <= x -> 0 <= p.[x].
Proof.
rewrite le_eqVlt => /orP[/eqP<-|xgtr2]; last exact/ltW/deg2_poly_gt0r.
have [dge0|dlt0] := leP 0 delta; last by apply: deg2_poly_ge0 => //; apply: ltW.
by rewrite le_eqVlt (rootP (deg2_poly_root2 dge0)) eqxx.
Qed.

Lemma deg2_poly_le0m x : 0 <= delta -> r1 <= x <= r2 -> p.[x] <= 0.
Proof.
move=> dge0; rewrite le_eqVlt andb_orl => /orP[/andP[/eqP<- _]|].
  by rewrite le_eqVlt (rootP (deg2_poly_root1 dge0)) eqxx.
rewrite le_eqVlt andb_orr => /orP[/andP[_ /eqP->]|].
  by rewrite le_eqVlt (rootP (deg2_poly_root2 dge0)) eqxx.
by move=> ?; apply/ltW/deg2_poly_lt0m.
Qed.

End Pdeg2RealClosedConvex.

Section Pdeg2RealClosedConcave.

Variable p : {poly F}.
Hypothesis degp : size p = 3.

Let a := p`_2.
Let b := p`_1.
Let c := p`_0.

Let delta := b ^+ 2 - 4 * a * c.

Let r1 := (- b + sqrt delta) / (2 * a).
Let r2 := (- b - sqrt delta) / (2 * a).

Hypothesis ale0 : a <= 0.

Let degpN : size (- p) = 3. Proof. by rewrite size_polyN. Qed.
Let aNge0 : 0 <= (- p)`_2. Proof. by rewrite coefN oppr_ge0. Qed.
Let deltaN : (- p)`_1 ^+ 2 - 4 * (- p)`_2 * (- p)`_0 = delta.
Proof. by rewrite !coefN sqrrN -mulrN opprK mulrN mulNr. Qed.
Let r1N : (- (- p)`_1 - sqrt delta) / (2 * (- p)`_2) = r1.
Proof. by rewrite !coefN -opprD mulrN divrNN. Qed.
Let r2N : (- (- p)`_1 + sqrt delta) / (2 * (- p)`_2) = r2.
Proof. by rewrite !coefN mulrN divrN -mulNr opprK opprD. Qed.

Lemma deg2_poly_lt0l x : x < r1 -> p.[x] < 0.
Proof. by move=> ?; rewrite -oppr_gt0 -hornerN deg2_poly_gt0l// deltaN r1N. Qed.

Lemma deg2_poly_lt0r x : r2 < x -> p.[x] < 0.
Proof. by move=> ?; rewrite -oppr_gt0 -hornerN deg2_poly_gt0r// deltaN r2N. Qed.

Lemma deg2_poly_gt0m x : r1 < x < r2 -> 0 < p.[x].
Proof.
by move=> ?; rewrite -oppr_lt0 -hornerN deg2_poly_lt0m// deltaN r1N r2N.
Qed.

Lemma deg2_poly_le0l x : x <= r1 -> p.[x] <= 0.
Proof. by move=> ?; rewrite -oppr_ge0 -hornerN deg2_poly_ge0l// deltaN r1N. Qed.

Lemma deg2_poly_le0r x : r2 <= x -> p.[x] <= 0.
Proof. by move=> ?; rewrite -oppr_ge0 -hornerN deg2_poly_ge0r// deltaN r2N. Qed.

Lemma deg2_poly_ge0m x : 0 <= delta -> r1 <= x <= r2 -> 0 <= p.[x].
Proof.
by move=> ? ?; rewrite -oppr_le0 -hornerN deg2_poly_le0m ?deltaN// r1N r2N.
Qed.

End Pdeg2RealClosedConcave.
End Pdeg2RealClosed.
End Real.

Module RealMonic.

Import Real.
Export FieldMonic.

Section Pdeg2RealMonic.

Variable F : realFieldType.

Variable p : {poly F}.
Hypothesis degp : size p = 3.
Hypothesis monicp : p \is monic.

Let a := p`_2.
Let b := p`_1.
Let c := p`_0.

Let delta := b ^+ 2 - 4 * c.

Let a1 : a = 1. Proof. by move: (monicP monicp); rewrite lead_coefE degp. Qed.
Let a2 : 2 * a = 2. Proof. by rewrite a1 mulr1. Qed.
Let a4 : 4 * a = 4. Proof. by rewrite a1 mulr1. Qed.

Lemma deg2_poly_min x : p.[- b / 2] <= p.[x].
Proof. by rewrite -a2 deg2_poly_min -/a ?a1 ?ler01. Qed.

Let deltam : delta = b ^+ 2 - 4 * a * c. Proof. by rewrite a1 mulr1. Qed.

Lemma deg2_poly_minE : p.[- b / 2] = - delta / 4.
Proof. by rewrite -a2 -a4 deltam deg2_poly_minE. Qed.

Lemma deg2_poly_gt0 : reflect (forall x, 0 < p.[x]) (delta < 0).
Proof. by rewrite deltam; apply: deg2_poly_gt0; rewrite // -/a a1 ler01. Qed.

Lemma deg2_poly_ge0 : reflect (forall x, 0 <= p.[x]) (delta <= 0).
Proof. by rewrite deltam; apply: deg2_poly_ge0; rewrite // -/a a1 ler01. Qed.

End Pdeg2RealMonic.

Section Pdeg2RealClosedMonic.

Variables (F : rcfType) (p : {poly F}).
Hypothesis degp : size p = 3.
Hypothesis monicp : p \is monic.

Let a := p`_2.
Let b := p`_1.
Let c := p`_0.

Let a1 : a = 1. Proof. by move: (monicP monicp); rewrite lead_coefE degp. Qed.

Let delta := b ^+ 2 - 4 * c.

Let deltam : delta = b ^+ 2 - 4 * a * c. Proof. by rewrite a1 mulr1. Qed.

Let r1 := (- b - sqrt delta) / 2.
Let r2 := (- b + sqrt delta) / 2.

Let nz2 : 2 != 0 :> F. Proof. by rewrite pnatr_eq0. Qed.

Lemma deg2_poly_factor : 0 <= delta -> p = ('X - r1%:P) * ('X - r2%:P).
Proof. by move=> dge0; apply: deg2_poly_factor; rewrite ?sqr_sqrtr. Qed.

Lemma deg2_poly_root1 : 0 <= delta -> root p r1.
Proof. by move=> dge0; apply: deg2_poly_root1; rewrite ?sqr_sqrtr. Qed.

Lemma deg2_poly_root2 : 0 <= delta -> root p r2.
Proof. by move=> dge0; apply: deg2_poly_root2; rewrite ?sqr_sqrtr. Qed.

Lemma deg2_poly_noroot : reflect (forall x, ~~ root p x) (delta < 0).
Proof. by rewrite deltam; apply: deg2_poly_noroot. Qed.

Lemma deg2_poly_gt0l x : x < r1 -> 0 < p.[x].
Proof.
by move=> ?; apply: deg2_poly_gt0l; rewrite // -/a ?a1 ?ler01 ?mulr1.
Qed.

Lemma deg2_poly_gt0r x : r2 < x -> 0 < p.[x].
Proof.
by move=> ?; apply: deg2_poly_gt0r; rewrite // -/a ?a1 ?ler01 ?mulr1.
Qed.

Lemma deg2_poly_lt0m x : r1 < x < r2 -> p.[x] < 0.
Proof.
by move=> ?; apply: deg2_poly_lt0m; rewrite // -/a ?a1 ?ler01 ?mulr1.
Qed.

Lemma deg2_poly_ge0l x : x <= r1 -> 0 <= p.[x].
Proof.
by move=> ?; apply: deg2_poly_ge0l; rewrite // -/a ?a1 ?ler01 ?mulr1.
Qed.

Lemma deg2_poly_ge0r x : r2 <= x -> 0 <= p.[x].
Proof.
by move=> ?; apply: deg2_poly_ge0r; rewrite // -/a ?a1 ?ler01 ?mulr1.
Qed.

Lemma deg2_poly_le0m x : 0 <= delta -> r1 <= x <= r2 -> p.[x] <= 0.
move=> dge0 xm.
by apply: deg2_poly_le0m; rewrite -/a -/b -/c ?a1 ?mulr1 -/delta ?ler01.
Qed.

End Pdeg2RealClosedMonic.
End RealMonic.
End Pdeg2.

Section Degle2PolyRealConvex.

Variable (F : realFieldType) (p : {poly F}).
Hypothesis degp : (size p <= 3)%N.

Let a := p`_2.
Let b := p`_1.
Let c := p`_0.

Let delta := b ^+ 2 - 4 * a * c.

Lemma deg_le2_poly_delta_ge0 : 0 <= a -> (forall x, 0 <= p.[x]) -> delta <= 0.
Proof.
move=> age0 pge0; move: degp; rewrite leq_eqVlt => /orP[/eqP|] degp'.
  exact/(Real.deg2_poly_ge0 degp' age0).
have a0 : a = 0 by rewrite /a nth_default.
rewrite /delta a0 mulr0 mul0r subr0 exprn_even_le0//=.
have [//|/eqP nzb] := eqP; move: (pge0 ((- 1 - c) / b)).
have -> : p = b *: 'X + c%:P.
  apply/polyP => + /[!coefE] => -[|[|i]] /=; rewrite !Monoid.simpm//.
  by rewrite nth_default// -ltnS (leq_trans degp').
by rewrite !hornerE/= mulrAC mulfV// mul1r subrK ler0N1.
Qed.

End Degle2PolyRealConvex.

Section Degle2PolyRealConcave.

Variable (F : realFieldType) (p : {poly F}).
Hypothesis degp : (size p <= 3)%N.

Let a := p`_2.
Let b := p`_1.
Let c := p`_0.

Let delta := b ^+ 2 - 4 * a * c.

Lemma deg_le2_poly_delta_le0 : a <= 0 -> (forall x, p.[x] <= 0) -> delta <= 0.
Proof.
move=> ale0 ple0; rewrite /delta -sqrrN -[c]opprK mulrN -mulNr -[-(4 * a)]mulrN.
rewrite -!coefN deg_le2_poly_delta_ge0 ?size_polyN ?coefN ?oppr_ge0// => x.
by rewrite hornerN oppr_ge0.
Qed.

End Degle2PolyRealConcave.

Section Degle2PolyRealClosedConvex.

Variable (F : rcfType) (p : {poly F}).
Hypothesis degp : (size p <= 3)%N.

Let a := p`_2.
Let b := p`_1.
Let c := p`_0.

Let delta := b ^+ 2 - 4 * a * c.

Lemma deg_le2_poly_ge0 : (forall x, 0 <= p.[x]) -> delta <= 0.
Proof.
have [age0|alt0] := leP 0 a; first exact: deg_le2_poly_delta_ge0.
move=> pge0; move: degp; rewrite leq_eqVlt => /orP[/eqP|] degp'; last first.
  by move: alt0; rewrite /a nth_default ?ltxx.
have [//|dge0] := leP delta 0.
pose r1 := (- b - sqrt delta) / (2 * a).
pose r2 := (- b + sqrt delta) / (2 * a).
pose x0 := Num.max (r1 + 1) (r2 + 1).
move: (pge0 x0); rewrite (Real.deg2_poly_factor degp' (ltW dge0)).
rewrite !hornerE/= -mulrA nmulr_rge0// leNgt => /negbTE<-.
by apply: mulr_gt0; rewrite subr_gt0 lt_max ltrDl ltr01 ?orbT.
Qed.

End Degle2PolyRealClosedConvex.

Section Degle2PolyRealClosedConcave.

Variable (F : rcfType) (p : {poly F}).
Hypothesis degp : (size p <= 3)%N.

Let a := p`_2.
Let b := p`_1.
Let c := p`_0.

Let delta := b ^+ 2 - 4 * a * c.

Lemma deg_le2_poly_le0 : (forall x, p.[x] <= 0) -> delta <= 0.
Proof.
move=> ple0; rewrite /delta -sqrrN -[c]opprK mulrN -mulNr -[-(4 * a)]mulrN.
by rewrite -!coefN deg_le2_poly_ge0 ?size_polyN// => x; rewrite hornerN oppr_ge0.
Qed.

End Degle2PolyRealClosedConcave.
End Theory.

Module Exports. HB.reexport. End Exports.

End Num.
Export Num.Exports.
