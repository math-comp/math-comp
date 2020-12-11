(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq choice.
From mathcomp Require Import div fintype path bigop finset prime order ssralg.
From mathcomp Require Import poly polydiv mxpoly generic_quotient countalg.
From mathcomp Require Import ssrnum closed_field ssrint rat intdiv.
From mathcomp Require Import algebraics_fundamentals.

(******************************************************************************)
(* This file provides an axiomatic construction of the algebraic numbers.     *)
(* The construction only assumes the existence of an algebraically closed     *)
(* filed with an automorphism of order 2; this amounts to the purely          *)
(* algebraic contents of the Fundamenta Theorem of Algebra.                   *)
(*       algC == the closed, countable field of algebraic numbers.            *)
(*  algCeq, algCring, ..., algCnumField == structures for algC.               *)
(* The ssrnum interfaces are implemented for algC as follows:                 *)
(*     x <= y <=> (y - x) is a nonnegative real                               *)
(*      x < y <=> (y - x) is a (strictly) positive real                       *)
(*       `|z| == the complex norm of z, i.e., sqrtC (z * z^* ).               *)
(*      Creal == the subset of real numbers (:= Num.real for algC).           *)
(*         'i == the imaginary number (:= sqrtC (-1)).                        *)
(*      'Re z == the real component of z.                                     *)
(*      'Im z == the imaginary component of z.                                *)
(*        z^* == the complex conjugate of z (:= conjC z).                     *)
(*    sqrtC z == a nonnegative square root of z, i.e., 0 <= sqrt x if 0 <= x. *)
(*  n.-root z == more generally, for n > 0, an nth root of z, chosen with a   *)
(*               minimal non-negative argument for n > 1 (i.e., with a        *)
(*               maximal real part subject to a nonnegative imaginary part).  *)
(*               Note that n.-root (-1) is a primitive 2nth root of unity,    *)
(*               an thus not equal to -1 for n odd > 1 (this will be shown in *)
(*               file cyclotomic.v).                                          *)
(* In addition, we provide:                                                   *)
(*       Crat == the subset of rational numbers.                              *)
(*  getCrat z == some a : rat such that ratr a = z, provided z \in Crat.      *)
(* minCpoly z == the minimal (monic) polynomial over Crat with root z.        *)
(* algC_invaut nu == an inverse of nu : {rmorphism algC -> algC}.             *)
(*         (x %| y)%C <=> y is an integer (Cint) multiple of x; if x or y are *)
(*        (x %| y)%Cx     of type nat or int they are coerced to algC here.   *)
(*                        The (x %| y)%Cx display form is a workaround for    *)
(*                        design limitations of the Coq Notation facilities.  *)
(* (x == y %[mod z])%C <=> x and y differ by an integer (Cint) multiple of z; *)
(*                as above, arguments of type nat or int are cast to algC.    *)
(* (x != y %[mod z])%C <=> x and y do not differ by an integer multiple of z. *)
(* Note that in file algnum we give an alternative definition of divisibility *)
(* based on algebraic integers, overloading the notation in the %A scope.     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope C_scope.
Declare Scope C_core_scope.
Declare Scope C_expanded_scope.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(* The Num mixin for an algebraically closed field with an automorphism of    *)
(* order 2, making it into a field of complex numbers.                        *)
Lemma ComplexNumMixin (L : closedFieldType) (conj : {rmorphism L -> L}) :
    involutive conj -> ~ conj =1 id ->
  {numL : numMixin L | forall x : NumDomainType L numL, `|x| ^+ 2 = x * conj x}.
Proof.
move=> conjK conj_nt.
have nz2: 2%:R != 0 :> L.
  apply/eqP=> char2; apply: conj_nt => e; apply/eqP/idPn=> eJ.
  have opp_id x: - x = x :> L.
    by apply/esym/eqP; rewrite -addr_eq0 -mulr2n -mulr_natl char2 mul0r.
  have{} char2: 2 \in [char L] by apply/eqP.
  without loss{eJ} eJ: e / conj e = e + 1.
    move/(_ (e / (e + conj e))); apply.
    rewrite fmorph_div rmorphD conjK -{1}[conj e](addNKr e) mulrDl.
    by rewrite opp_id (addrC e) divff // addr_eq0 opp_id.
  pose a := e * conj e; have aJ: conj a = a by rewrite rmorphM conjK mulrC.
  have [w Dw] := @solve_monicpoly _ 2 (nth 0 [:: e * a; - 1]) isT.
  have{} Dw: w ^+ 2 + w = e * a.
    by rewrite Dw !big_ord_recl big_ord0 /= mulr1 mulN1r addr0 subrK.
  pose b := w + conj w; have bJ: conj b = b by rewrite rmorphD conjK addrC.
  have Db2: b ^+ 2 + b = a.
    rewrite -Frobenius_autE // rmorphD addrACA Dw /= Frobenius_autE -rmorphX.
    by rewrite -rmorphD Dw rmorphM aJ eJ -mulrDl -{1}[e]opp_id addKr mul1r.
  have /eqP[] := oner_eq0 L; apply: (addrI b); rewrite addr0 -{2}bJ.
  have: (b + e) * (b + conj e) == 0.
    rewrite mulrDl 2!mulrDr -/a addrA addr_eq0 opp_id (mulrC e) -addrA.
    by rewrite -mulrDr eJ addrAC -{2}[e]opp_id subrr add0r mulr1 Db2.
  rewrite mulf_eq0 !addr_eq0 !opp_id => /pred2P[] -> //.
  by rewrite {2}eJ rmorphD rmorph1.
have mul2I: injective (fun z : L => z *+ 2).
  by move=> x y; rewrite /= -mulr_natl -(mulr_natl y) => /mulfI->.
pose sqrt x : L := sval (sig_eqW (@solve_monicpoly _ 2 (nth 0 [:: x]) isT)).
have sqrtK x: sqrt x ^+ 2 = x.
  rewrite /sqrt; case: sig_eqW => /= y ->.
  by rewrite !big_ord_recl big_ord0 /= mulr1 mul0r !addr0.
have sqrtE x y: y ^+ 2 = x -> {b : bool | y = (-1) ^+ b * sqrt x}.
  move=> Dx; exists (y != sqrt x); apply/eqP; rewrite mulr_sign if_neg.
  by case: ifPn => //; apply/implyP; rewrite implyNb -eqf_sqr Dx sqrtK.
pose i := sqrt (- 1).
have sqrMi x: (i * x) ^+ 2 = - x ^+ 2 by rewrite exprMn sqrtK mulN1r.
have iJ : conj i = - i.
  have /sqrtE[b]: conj i ^+ 2 = - 1 by rewrite -rmorphX sqrtK rmorphN1.
  rewrite mulr_sign -/i; case: b => // Ri.
  case: conj_nt => z; wlog zJ: z / conj z = - z.
    move/(_ (z - conj z)); rewrite !rmorphB conjK opprB => zJ.
    by apply/mul2I/(canRL (subrK _)); rewrite -addrA zJ // addrC subrK.
  have [-> | nz_z] := eqVneq z 0; first exact: rmorph0.
  have [u Ru [v Rv Dz]]:
    exists2 u, conj u = u & exists2 v, conj v = v & (u + z * v) ^+ 2 = z.
  - pose y := sqrt z; exists ((y + conj y) / 2%:R).
      by rewrite fmorph_div rmorphD conjK addrC rmorph_nat.
    exists ((y - conj y) / (z *+ 2)).
      rewrite fmorph_div rmorphMn zJ mulNrn invrN mulrN -mulNr rmorphB opprB.
      by rewrite conjK.
    rewrite -(mulr_natl z) invfM (mulrC z) !mulrA divfK // -mulrDl addrACA.
    by rewrite subrr addr0 -mulr2n -mulr_natr mulfK ?Neq0 ?sqrtK.
  suffices u0: u = 0 by rewrite -Dz u0 add0r rmorphX rmorphM Rv zJ mulNr sqrrN.
  suffices [b Du]: exists b : bool, u = (-1) ^+ b * i * z * v.
    apply: mul2I; rewrite mul0rn mulr2n -{2}Ru.
    by rewrite Du !rmorphM rmorph_sign Rv Ri zJ !mulrN mulNr subrr.
  have/eqP:= zJ; rewrite -addr_eq0 -{1 2}Dz rmorphX rmorphD rmorphM Ru Rv zJ.
  rewrite mulNr sqrrB sqrrD addrACA (addrACA (u ^+ 2)) addNr addr0 -!mulr2n.
  rewrite -mulrnDl -(mul0rn _ 2) (inj_eq mul2I) /= -[rhs in _ + rhs]opprK.
  rewrite -sqrMi subr_eq0 eqf_sqr -mulNr !mulrA.
  by case/pred2P=> ->; [exists false | exists true]; rewrite mulr_sign.
pose norm x := sqrt x * conj (sqrt x).
have normK x : norm x ^+ 2 = x * conj x by rewrite exprMn -rmorphX sqrtK.
have normE x y : y ^+ 2 = x -> norm x = y * conj y.
  rewrite /norm => /sqrtE[b /(canLR (signrMK b)) <-].
  by rewrite !rmorphM rmorph_sign mulrACA -mulrA signrMK.
have norm_eq0 x : norm x = 0 -> x = 0.
  by move/eqP; rewrite mulf_eq0 fmorph_eq0 -mulf_eq0 -expr2 sqrtK => /eqP.
have normM x y : norm (x * y) = norm x * norm y.
  by rewrite mulrACA -rmorphM; apply: normE; rewrite exprMn !sqrtK.
have normN x : norm (- x) = norm x.
  by rewrite -mulN1r normM {1}/norm iJ mulrN -expr2 sqrtK opprK mul1r.
pose le x y := norm (y - x) == y - x; pose lt x y := (y != x) && le x y.
have posE x: le 0 x = (norm x == x) by rewrite /le subr0.
have leB x y: le x y = le 0 (y - x) by rewrite posE.
have posP x : reflect (exists y, x = y * conj y) (le 0 x).
  rewrite posE; apply: (iffP eqP) => [Dx | [y {x}->]]; first by exists (sqrt x).
  by rewrite (normE _ _ (normK y)) rmorphM conjK (mulrC (conj _)) -expr2 normK.
have posJ x : le 0 x -> conj x = x.
  by case/posP=> {x}u ->; rewrite rmorphM conjK mulrC.
have pos_linear x y : le 0 x -> le 0 y -> le x y || le y x.
  move=> pos_x pos_y; rewrite leB -opprB orbC leB !posE normN -eqf_sqr.
  by rewrite normK rmorphB !posJ ?subrr.
have sposDl x y : lt 0 x -> le 0 y -> lt 0 (x + y).
  have sqrtJ z : le 0 z -> conj (sqrt z) = sqrt z.
    rewrite posE -{2}[z]sqrtK -subr_eq0 -mulrBr mulf_eq0 subr_eq0.
    by case/pred2P=> ->; rewrite ?rmorph0.
  case/andP=> nz_x /sqrtJ uJ /sqrtJ vJ.
  set u := sqrt x in uJ; set v := sqrt y in vJ; pose w := u + i * v.
  have ->: x + y = w * conj w.
    rewrite rmorphD rmorphM iJ uJ vJ mulNr mulrC -subr_sqr sqrMi opprK.
    by rewrite !sqrtK.
  apply/andP; split; last by apply/posP; exists w.
  rewrite -normK expf_eq0 //=; apply: contraNneq nz_x => /norm_eq0 w0.
  rewrite -[x]sqrtK expf_eq0 /= -/u -(inj_eq mul2I) !mulr2n -{2}(rmorph0 conj).
  by rewrite -w0 rmorphD rmorphM iJ uJ vJ mulNr addrACA subrr addr0.
have sposD x y : lt 0 x -> lt 0 y -> lt 0 (x + y).
  by move=> x_gt0 /andP[_]; apply: sposDl.
have normD x y : le (norm (x + y)) (norm x + norm y).
  have sposM u v: lt 0 u -> le 0 (u * v) -> le 0 v.
    by rewrite /lt !posE normM andbC => /andP[/eqP-> /mulfI/inj_eq->].
  have posD u v: le 0 u -> le 0 v -> le 0 (u + v).
    have [-> | nz_u u_ge0 v_ge0] := eqVneq u 0; first by rewrite add0r.
    by have /andP[]: lt 0 (u + v) by rewrite sposDl // /lt nz_u.
  have le_sqr u v: conj u = u -> le 0 v -> le (u ^+ 2) (v ^+ 2) -> le u v.
    case: (eqVneq u 0) => [-> //|nz_u Ru v_ge0].
    have [u_gt0 | u_le0 _] := boolP (lt 0 u).
      by rewrite leB (leB u) subr_sqr mulrC addrC; apply: sposM; apply: sposDl.
    rewrite leB posD // posE normN -addr_eq0; apply/eqP.
    rewrite /lt nz_u posE -subr_eq0 in u_le0; apply: (mulfI u_le0).
    by rewrite mulr0 -subr_sqr normK Ru subrr.
  have pos_norm z: le 0 (norm z) by apply/posP; exists (sqrt z).
  rewrite le_sqr ?posJ ?posD // sqrrD !normK -normM rmorphD mulrDl !mulrDr.
  rewrite addrA addrC !addrA -(addrC (y * conj y)) !addrA.
  move: (y * _ + _) => u; rewrite -!addrA leB opprD addrACA {u}subrr add0r -leB.
  rewrite {}le_sqr ?posD //.
    by rewrite rmorphD !rmorphM !conjK addrC mulrC (mulrC y).
  rewrite -mulr2n -mulr_natr exprMn normK -natrX mulr_natr sqrrD mulrACA.
  rewrite -rmorphM (mulrC y x) addrAC leB mulrnA mulr2n opprD addrACA.
  rewrite subrr addr0 {2}(mulrC x) rmorphM mulrACA -opprB addrAC -sqrrB -sqrMi.
  apply/posP; exists (i * (x * conj y - y * conj x)); congr (_ * _).
  rewrite !(rmorphM, rmorphB) iJ !conjK mulNr -mulrN opprB.
  by rewrite (mulrC x) (mulrC y).
by exists (NumMixin normD sposD norm_eq0 pos_linear normM (rrefl _) (rrefl _)).
Qed.

Module Algebraics.

Module Type Specification.

Parameter type : Type.

Parameter eqMixin : Equality.class_of type.
Canonical eqType := EqType type eqMixin.

Parameter choiceMixin : Choice.mixin_of type.
Canonical choiceType := ChoiceType type choiceMixin.

Parameter countMixin : Countable.mixin_of type.
Canonical countType := CountType type countMixin.

Parameter zmodMixin : GRing.Zmodule.mixin_of type.
Canonical zmodType := ZmodType type zmodMixin.
Canonical countZmodType := [countZmodType of type].

Parameter ringMixin : GRing.Ring.mixin_of zmodType.
Canonical ringType := RingType type ringMixin.
Canonical countRingType := [countRingType of type].

Parameter unitRingMixin : GRing.UnitRing.mixin_of ringType.
Canonical unitRingType := UnitRingType type unitRingMixin.

Axiom mulC : @commutative ringType ringType *%R.
Canonical comRingType := ComRingType type mulC.
Canonical comUnitRingType := [comUnitRingType of type].

Axiom idomainAxiom : GRing.IntegralDomain.axiom ringType.
Canonical idomainType := IdomainType type idomainAxiom.

Axiom fieldMixin : GRing.Field.mixin_of unitRingType.
Canonical fieldType := FieldType type fieldMixin.

Parameter decFieldMixin : GRing.DecidableField.mixin_of unitRingType.
Canonical decFieldType := DecFieldType type decFieldMixin.

Axiom closedFieldAxiom : GRing.ClosedField.axiom ringType.
Canonical closedFieldType := ClosedFieldType type closedFieldAxiom.

Parameter numMixin : numMixin idomainType.
Canonical porderType := POrderType ring_display type numMixin.
Canonical numDomainType := NumDomainType type numMixin.
Canonical normedZmodType := NormedZmodType type type numMixin.
Canonical numFieldType := [numFieldType of type].

Parameter conjMixin : Num.ClosedField.imaginary_mixin_of numDomainType.
Canonical numClosedFieldType := NumClosedFieldType type conjMixin.

Axiom archimedean : Num.archimedean_axiom numDomainType.
Canonical archiNumDomainType := ArchiNumDomainType type archimedean.
Canonical archiNumFieldType := [archiNumFieldType of type].
Canonical archiNumClosedFieldType := [archiNumClosedFieldType of type].

Axiom algebraic : integralRange (@ratr unitRingType).

End Specification.

Module Implementation : Specification.

Definition L := tag Fundamental_Theorem_of_Algebraics.

Definition conjL : {rmorphism L -> L} :=
  s2val (tagged Fundamental_Theorem_of_Algebraics).

Fact conjL_K : involutive conjL.
Proof. exact: s2valP (tagged Fundamental_Theorem_of_Algebraics). Qed.

Fact conjL_nt : ~ conjL =1 id.
Proof. exact: s2valP' (tagged Fundamental_Theorem_of_Algebraics). Qed.

Definition LnumMixin := ComplexNumMixin conjL_K conjL_nt.
Definition Lnum := NumDomainType L (sval LnumMixin).

Definition QtoL := [rmorphism of @ratr [numFieldType of Lnum]].
Notation pQtoL := (map_poly QtoL).

Definition rootQtoL p_j :=
  if p_j.1 == 0 then 0 else
  (sval (closed_field_poly_normal (pQtoL p_j.1)))`_p_j.2.

Definition eq_root p_j q_k := rootQtoL p_j == rootQtoL q_k.
Fact eq_root_is_equiv : equiv_class_of eq_root.
Proof. by rewrite /eq_root; split=> [ ? | ? ? | ? ? ? ] // /eqP->. Qed.
Canonical eq_root_equiv := EquivRelPack eq_root_is_equiv.
Definition type : Type := {eq_quot eq_root}%qT.

Definition eqMixin : Equality.class_of type := EquivQuot.eqMixin _.
Canonical eqType := EqType type eqMixin.

Definition choiceMixin : Choice.mixin_of type := EquivQuot.choiceMixin _.
Canonical choiceType := ChoiceType type choiceMixin.

Definition countMixin : Countable.mixin_of type := CanCountMixin reprK.
Canonical countType := CountType type countMixin.

Definition CtoL (u : type) := rootQtoL (repr u).

Fact CtoL_inj : injective CtoL.
Proof. by move=> u v /eqP eq_uv; rewrite -[u]reprK -[v]reprK; apply/eqmodP. Qed.

Fact CtoL_P u : integralOver QtoL (CtoL u).
Proof.
rewrite /CtoL /rootQtoL; case: (repr u) => p j /=.
case: (closed_field_poly_normal _) => r Dp /=.
case: ifPn => [_ | nz_p]; first exact: integral0.
have [/(nth_default 0)-> | lt_j_r] := leqP (size r) j; first exact: integral0.
apply/integral_algebraic; exists p; rewrite // Dp -mul_polyC rootM orbC.
by rewrite root_prod_XsubC mem_nth.
Qed.

Fact LtoC_subproof z : integralOver QtoL z -> {u | CtoL u = z}.
Proof.
case/sig2_eqW=> p mon_p pz0; rewrite /CtoL.
pose j := index z (sval (closed_field_poly_normal (pQtoL p))).
pose u := \pi_type%qT (p, j); exists u; have /eqmodP/eqP-> := reprK u.
rewrite /rootQtoL -if_neg monic_neq0 //; apply: nth_index => /=.
case: (closed_field_poly_normal _) => r /= Dp.
by rewrite Dp (monicP _) ?(monic_map QtoL) // scale1r root_prod_XsubC in pz0.
Qed.

Definition LtoC z Az := sval (@LtoC_subproof z Az).
Fact LtoC_K z Az : CtoL (@LtoC z Az) = z.
Proof. exact: (svalP (LtoC_subproof Az)). Qed.

Fact CtoL_K u : LtoC (CtoL_P u) = u.
Proof. by apply: CtoL_inj; rewrite LtoC_K. Qed.

Definition zero := LtoC (integral0 _).
Definition add u v := LtoC (integral_add (CtoL_P u) (CtoL_P v)).
Definition opp u := LtoC (integral_opp (CtoL_P u)).

Fact addA : associative add.
Proof. by move=> u v w; apply: CtoL_inj; rewrite !LtoC_K addrA. Qed.

Fact addC : commutative add.
Proof. by move=> u v; apply: CtoL_inj; rewrite !LtoC_K addrC. Qed.

Fact add0 : left_id zero add.
Proof. by move=> u; apply: CtoL_inj; rewrite !LtoC_K add0r. Qed.

Fact addN : left_inverse zero opp add.
Proof. by move=> u; apply: CtoL_inj; rewrite !LtoC_K addNr. Qed.

Definition zmodMixin := ZmodMixin addA addC add0 addN.
Canonical zmodType := ZmodType type zmodMixin.
Canonical countZmodType := [countZmodType of type].

Fact CtoL_is_additive : additive CtoL.
Proof. by move=> u v; rewrite !LtoC_K. Qed.
Canonical CtoL_additive := Additive CtoL_is_additive.

Definition one := LtoC (integral1 _).
Definition mul u v := LtoC (integral_mul (CtoL_P u) (CtoL_P v)).
Definition inv u := LtoC (integral_inv (CtoL_P u)).

Fact mulA : associative mul.
Proof. by move=> u v w; apply: CtoL_inj; rewrite !LtoC_K mulrA. Qed.

Fact mulC : commutative mul.
Proof. by move=> u v; apply: CtoL_inj; rewrite !LtoC_K mulrC. Qed.

Fact mul1 : left_id one mul.
Proof. by move=> u; apply: CtoL_inj; rewrite !LtoC_K mul1r. Qed.

Fact mulD : left_distributive mul +%R.
Proof. by move=> u v w; apply: CtoL_inj; rewrite !LtoC_K mulrDl. Qed.

Fact one_nz : one != 0 :> type.
Proof. by rewrite -(inj_eq CtoL_inj) !LtoC_K oner_eq0. Qed.

Definition ringMixin := ComRingMixin mulA mulC mul1 mulD one_nz.
Canonical ringType := RingType type ringMixin.
Canonical comRingType := ComRingType type mulC.
Canonical countRingType := [countRingType of type].

Fact CtoL_is_multiplicative : multiplicative CtoL.
Proof. by split=> [u v|]; rewrite !LtoC_K. Qed.
Canonical CtoL_rmorphism := AddRMorphism CtoL_is_multiplicative.

Fact mulVf : GRing.Field.axiom inv.
Proof.
move=> u; rewrite -(inj_eq CtoL_inj) rmorph0 => nz_u.
by apply: CtoL_inj; rewrite !LtoC_K mulVf.
Qed.
Fact inv0 : inv 0 = 0. Proof. by apply: CtoL_inj; rewrite !LtoC_K invr0. Qed.

Definition unitRingMixin := FieldUnitMixin mulVf inv0.
Canonical unitRingType := UnitRingType type unitRingMixin.
Canonical comUnitRingType := [comUnitRingType of type].

Definition fieldMixin := FieldMixin mulVf inv0.
Definition idomainAxiom := FieldIdomainMixin fieldMixin.
Canonical idomainType := IdomainType type idomainAxiom.
Canonical fieldType := FieldType type fieldMixin.

Fact closedFieldAxiom : GRing.ClosedField.axiom ringType.
Proof.
move=> n a n_gt0; pose p := 'X^n - \poly_(i < n) CtoL (a i).
have Ap: {in p : seq L, integralRange QtoL}.
  move=> _ /(nthP 0)[j _ <-]; rewrite coefB coefXn coef_poly.
  apply: integral_sub; first exact: integral_nat.
  by case: ifP => _; [apply: CtoL_P | apply: integral0].
have sz_p: size p = n.+1.
  by rewrite size_addl size_polyXn // size_opp ltnS size_poly.
have [z pz0]: exists z, root p z by apply/closed_rootP; rewrite sz_p eqSS -lt0n.
have Az: integralOver ratr z.
  by apply: integral_root Ap; rewrite // -size_poly_gt0 sz_p.
exists (LtoC Az); apply/CtoL_inj; rewrite -[CtoL _]subr0 -(rootP pz0).
rewrite rmorphX /= LtoC_K hornerD hornerXn hornerN opprD addNKr opprK.
rewrite horner_poly rmorph_sum; apply: eq_bigr => k _.
by rewrite rmorphM rmorphX /= LtoC_K.
Qed.

Definition decFieldMixin := closed_field_QEMixin closedFieldAxiom.
Canonical decFieldType := DecFieldType type decFieldMixin.
Canonical closedFieldType := ClosedFieldType type closedFieldAxiom.

Fact conj_subproof u : integralOver QtoL (conjL (CtoL u)).
Proof.
have [p mon_p pu0] := CtoL_P u; exists p => //.
rewrite -(fmorph_root conjL) conjL_K map_poly_id // => _ /(nthP 0)[j _ <-].
by rewrite coef_map fmorph_rat.
Qed.
Fact conj_is_rmorphism : rmorphism (fun u => LtoC (conj_subproof u)).
Proof.
do 2?split=> [u v|]; apply: CtoL_inj; last by rewrite !LtoC_K rmorph1.
- by rewrite LtoC_K 3!{1}rmorphB /= !LtoC_K.
by rewrite LtoC_K 3!{1}rmorphM /= !LtoC_K.
Qed.
Definition conj : {rmorphism type -> type} := RMorphism conj_is_rmorphism.
Lemma conjK : involutive conj.
Proof. by move=> u; apply: CtoL_inj; rewrite !LtoC_K conjL_K. Qed.

Fact conj_nt : ~ conj =1 id.
Proof.
have [i i2]: exists i : type, i ^+ 2 = -1.
  have [i] := @solve_monicpoly _ 2 (nth 0 [:: -1 : type]) isT.
  by rewrite !big_ord_recl big_ord0 /= mul0r mulr1 !addr0; exists i.
move/(_ i)/(congr1 CtoL); rewrite LtoC_K => iL_J.
have/lt_geF/idP[] := @ltr01 Lnum; rewrite -oppr_ge0 -(rmorphN1 CtoL_rmorphism).
by rewrite -i2 rmorphX /= expr2 -{2}iL_J -(svalP LnumMixin) exprn_ge0.
Qed.

Definition numMixin : numMixin closedFieldType :=
  sval (ComplexNumMixin conjK conj_nt).
Canonical porderType := POrderType ring_display type numMixin.
Canonical numDomainType := NumDomainType type numMixin.
Canonical normedZmodType := NormedZmodType type type numMixin.
Canonical numFieldType := [numFieldType of type].

Lemma normK u : `|u| ^+ 2 = u * conj u.
Proof. exact: svalP (ComplexNumMixin conjK conj_nt) u. Qed.

Lemma algebraic : integralRange (@ratr unitRingType).
Proof.
move=> u; have [p mon_p pu0] := CtoL_P u; exists p => {mon_p}//.
rewrite -(fmorph_root CtoL_rmorphism) -map_poly_comp; congr (root _ _): pu0.
by apply/esym/eq_map_poly; apply: fmorph_eq_rat.
Qed.

Definition conjMixin :=
  ImaginaryMixin (svalP (imaginary_exists closedFieldType))
                 (fun x => esym (normK x)).
Canonical numClosedFieldType := NumClosedFieldType type conjMixin.

Fact archimedean : Num.archimedean_axiom numDomainType.
Proof. exact: rat_algebraic_archimedean algebraic. Qed.
Canonical archiNumDomainType := ArchiNumDomainType type archimedean.
Canonical archiNumFieldType := [archiNumFieldType of type].
Canonical archiNumClosedFieldType := [archiNumClosedFieldType of type].

End Implementation.

Definition divisor := Implementation.type.

Module Internals.

Import Implementation.

Local Notation algC := type.
Local Notation QtoC := (ratr : rat -> algC).
Local Notation QtoCm := [rmorphism of QtoC].
Local Notation pQtoC := (map_poly QtoC).

Fact algCi_subproof : {i : algC | i ^+ 2 = -1}.
Proof. exact: GRing.imaginary_exists. Qed.

Variant getCrat_spec : Type := GetCrat_spec CtoQ of cancel QtoC CtoQ.

Fact getCrat_subproof : getCrat_spec.
Proof.
have isQ := rat_algebraic_decidable algebraic.
exists (fun z => if isQ z is left Qz then sval (sig_eqW Qz) else 0) => a.
case: (isQ _) => [Qa | []]; last by exists a.
by case: (sig_eqW _) => b /= /fmorph_inj.
Qed.

Fact minCpoly_subproof (x : algC) :
  {p | p \is monic & forall q, root (pQtoC q) x = (p %| q)%R}.
Proof.
have isQ := rat_algebraic_decidable algebraic.
have [p [mon_p px0 irr_p]] := minPoly_decidable_closure isQ (algebraic x).
exists p => // q; apply/idP/idP=> [qx0 | /dvdpP[r ->]]; last first.
  by rewrite rmorphM rootM px0 orbT.
suffices /eqp_dvdl <-: gcdp p q %= p by apply: dvdp_gcdr.
rewrite irr_p ?dvdp_gcdl ?gtn_eqF // -(size_map_poly QtoCm) gcdp_map /=.
rewrite (@root_size_gt1 _ x) ?root_gcd ?px0 //.
by rewrite gcdp_eq0 negb_and map_poly_eq0 monic_neq0.
Qed.

Definition algC_divisor (x : algC) := x : divisor.
Definition int_divisor m := m%:~R : divisor.
Definition nat_divisor n := n%:R : divisor.

End Internals.

Module Import Exports.

Import Implementation Internals.

Notation algC := type.
Delimit Scope C_scope with C.
Delimit Scope C_core_scope with Cc.
Delimit Scope C_expanded_scope with Cx.
Open Scope C_core_scope.

Canonical eqType.
Canonical choiceType.
Canonical countType.
Canonical zmodType.
Canonical countZmodType.
Canonical ringType.
Canonical countRingType.
Canonical unitRingType.
Canonical comRingType.
Canonical comUnitRingType.
Canonical idomainType.
Canonical porderType.
Canonical numDomainType.
Canonical normedZmodType.
Canonical fieldType.
Canonical numFieldType.
Canonical decFieldType.
Canonical closedFieldType.
Canonical numClosedFieldType.
Canonical archiNumDomainType.
Canonical archiNumFieldType.
Canonical archiNumClosedFieldType.

Notation algCeq := eqType.
Notation algCzmod := zmodType.
Notation algCring := ringType.
Notation algCuring := unitRingType.
Notation algCnum := numDomainType.
Notation algCfield := fieldType.
Notation algCnumField := numFieldType.
Notation algCnumClosedField := numClosedFieldType.

Notation Creal := (@Num.Def.Rreal numDomainType).

Definition getCrat := let: GetCrat_spec CtoQ _ := getCrat_subproof in CtoQ.
Definition Crat : {pred algC} := fun x => ratr (getCrat x) == x.

Definition minCpoly x : {poly algC} :=
  let: exist2 p _ _ := minCpoly_subproof x in map_poly ratr p.

Coercion nat_divisor : nat >-> divisor.
Coercion int_divisor : int >-> divisor.
Coercion algC_divisor : algC >-> divisor.

Lemma nCdivE (p : nat) : p = p%:R :> divisor. Proof. by []. Qed.
Lemma zCdivE (p : int) : p = p%:~R :> divisor. Proof. by []. Qed.
Definition CdivE := (nCdivE, zCdivE).

Definition dvdC (x : divisor) : {pred algC} :=
   fun y => if x == 0 then y == 0 else y / x \in Num.int.
Notation "x %| y" := (y \in dvdC x) : C_expanded_scope.
Notation "x %| y" := (@in_mem divisor y (mem (dvdC x))) : C_scope.

Definition eqCmod (e x y : divisor) := (e %| x - y)%C.

Notation "x == y %[mod e ]" := (eqCmod e x y) : C_scope.
Notation "x != y %[mod e ]" := (~~ (x == y %[mod e])%C) : C_scope.

End Exports.

End Algebraics.

Export Algebraics.Exports.

Section AlgebraicsTheory.

Implicit Types (x y z : algC) (n : nat) (m : int) (b : bool).
Import Algebraics.Internals.

Local Notation ZtoQ := (intr : int -> rat).
Local Notation ZtoC := (intr : int -> algC).
Local Notation QtoC := (ratr : rat -> algC).
Local Notation QtoCm := [rmorphism of QtoC].
Local Notation CtoQ := getCrat.
Local Notation intrp := (map_poly intr).
Local Notation pZtoQ := (map_poly ZtoQ).
Local Notation pZtoC := (map_poly ZtoC).
Local Notation pQtoC := (map_poly ratr).

Let intr_inj_ZtoC := (intr_inj : injective ZtoC).
Local Hint Resolve intr_inj_ZtoC : core.

(* Specialization of a few basic ssrnum order lemmas. *)

Definition eqC_nat n p : (n%:R == p%:R :> algC) = (n == p) := eqr_nat _ n p.
Definition leC_nat n p : (n%:R <= p%:R :> algC) = (n <= p)%N := ler_nat _ n p.
Definition ltC_nat n p : (n%:R < p%:R :> algC) = (n < p)%N := ltr_nat _ n p.
Definition Cchar : [char algC] =i pred0 := @char_num _.

(* This can be used in the converse direction to evaluate assertions over     *)
(* manifest rationals, such as 3%:R^-1 + 7%:%^-1 < 2%:%^-1 :> algC.           *)
(* Missing norm and integer exponent, due to gaps in ssrint and rat.          *)
Definition CratrE :=
  let CnF := Algebraics.Implementation.numFieldType in
  let QtoCm := ratr_rmorphism CnF in
  ((rmorph0 QtoCm, rmorph1 QtoCm, rmorphMn QtoCm, rmorphN QtoCm, rmorphD QtoCm),
   (rmorphM QtoCm, rmorphX QtoCm, fmorphV QtoCm),
   (rmorphMz QtoCm, rmorphXz QtoCm, @ratr_norm CnF, @ratr_sg CnF),
   =^~ (@ler_rat CnF, @ltr_rat CnF, (inj_eq (fmorph_inj QtoCm)))).

Definition CintrE :=
  let CnF := Algebraics.Implementation.numFieldType in
  let ZtoCm := intmul1_rmorphism CnF in
  ((rmorph0 ZtoCm, rmorph1 ZtoCm, rmorphMn ZtoCm, rmorphN ZtoCm, rmorphD ZtoCm),
   (rmorphM ZtoCm, rmorphX ZtoCm),
   (rmorphMz ZtoCm, @intr_norm CnF, @intr_sg CnF),
   =^~ (@ler_int CnF, @ltr_int CnF, (inj_eq (@intr_inj CnF)))).

Let nz2 : 2%:R != 0 :> algC. Proof. by rewrite -!CintrE. Qed.

(* Conjugation and norm. *)

Definition algC_algebraic x := Algebraics.Implementation.algebraic x.

(* Real number subset. *)

Lemma algCrect x : x = 'Re x + 'i * 'Im x.
Proof. by rewrite [LHS]Crect. Qed.

Lemma algCreal_Re x : 'Re x \is Creal.
Proof. by rewrite Creal_Re. Qed.

Lemma algCreal_Im x : 'Im x \is Creal.
Proof. by rewrite Creal_Im. Qed.
Hint Resolve algCreal_Re algCreal_Im : core.

(* Integer divisibility. *)

Lemma dvdCP x y : reflect (exists2 z, z \in Num.int & y = z * x) (x %| y)%C.
Proof.
rewrite unfold_in; have [-> | nz_x] := eqVneq.
  by apply: (iffP eqP) => [->|[z _ ->]]; first exists 0; rewrite ?mulr0.
apply: (iffP idP) => [Zyx | [z Zz ->]]; last by rewrite mulfK.
by exists (y / x); rewrite ?divfK.
Qed.

Lemma dvdCP_nat x y : 0 <= x -> 0 <= y -> (x %| y)%C -> {n | y = n%:R * x}.
Proof.
move=> x_ge0 y_ge0 x_dv_y; apply: sig_eqW.
case/dvdCP: x_dv_y => z Zz -> in y_ge0 *; move: x_ge0 y_ge0 Zz.
rewrite le_eqVlt => /predU1P[<- | ]; first by exists 22; rewrite !mulr0.
by move=> /pmulr_lge0-> /RintEge0-> /RnatP[n ->]; exists n.
Qed.

Lemma dvdC0 x : (x %| 0)%C.
Proof. by apply/dvdCP; exists 0; rewrite ?mul0r. Qed.

Lemma dvd0C x : (0 %| x)%C = (x == 0).
Proof. by rewrite unfold_in eqxx. Qed.

Lemma dvdC_mull x y z : y \in Num.int -> (x %| z)%C -> (x %| y * z)%C.
Proof.
move=> Zy /dvdCP[m Zm ->]; apply/dvdCP.
by exists (y * m); rewrite ?mulrA ?rpredM.
Qed.

Lemma dvdC_mulr x y z : y \in Num.int -> (x %| z)%C -> (x %| z * y)%C.
Proof. by rewrite mulrC; apply: dvdC_mull. Qed.

Lemma dvdC_mul2r x y z : y != 0 -> (x * y %| z * y)%C = (x %| z)%C.
Proof.
move=> nz_y; rewrite !unfold_in !(mulIr_eq0 _ (mulIf nz_y)).
by rewrite mulrAC invfM mulrA divfK.
Qed.

Lemma dvdC_mul2l x y z : y != 0 -> (y * x %| y * z)%C = (x %| z)%C.
Proof. by rewrite !(mulrC y); apply: dvdC_mul2r. Qed.

Lemma dvdC_trans x y z : (x %| y)%C -> (y %| z)%C -> (x %| z)%C.
Proof. by move=> x_dv_y /dvdCP[m Zm ->]; apply: dvdC_mull. Qed.

Lemma dvdC_refl x : (x %| x)%C.
Proof. by apply/dvdCP; exists 1; rewrite ?mul1r. Qed.
Hint Resolve dvdC_refl : core.

Fact dvdC_key x : pred_key (dvdC x). Proof. by []. Qed.
Lemma dvdC_zmod x : zmod_closed (dvdC x).
Proof.
split=> [| _ _ /dvdCP[y Zy ->] /dvdCP[z Zz ->]]; first exact: dvdC0.
by rewrite -mulrBl dvdC_mull ?rpredB.
Qed.
Canonical dvdC_keyed x := KeyedPred (dvdC_key x).
Canonical dvdC_opprPred x := OpprPred (dvdC_zmod x).
Canonical dvdC_addrPred x := AddrPred (dvdC_zmod x).
Canonical dvdC_zmodPred x := ZmodPred (dvdC_zmod x).

Lemma dvdC_nat (p n : nat) : (p %| n)%C = (p %| n)%N.
Proof.
rewrite unfold_in RintEge0 ?divr_ge0 ?invr_ge0 ?ler0n // !pnatr_eq0.
have [-> | nz_p] := eqVneq; first by rewrite dvd0n.
apply/RnatP/dvdnP=> [[q def_q] | [q ->]]; exists q.
  by apply/eqP; rewrite -eqC_nat natrM -def_q divfK ?pnatr_eq0.
by rewrite [num in num / _]natrM mulfK ?pnatr_eq0.
Qed.

Lemma dvdC_int (p : nat) x : x \in Num.int -> (p %| x)%C = (p %| `|floorR x|)%N.
Proof.
move=> Zx; rewrite -{1}(floorRK Zx) {1}[floorR x]intEsign.
by rewrite rmorphMsign rpredMsign dvdC_nat.
Qed.

(* Elementary modular arithmetic. *)

Lemma eqCmod_refl e x : (x == x %[mod e])%C.
Proof. by rewrite /eqCmod subrr rpred0. Qed.

Lemma eqCmodm0 e : (e == 0 %[mod e])%C. Proof. by rewrite /eqCmod subr0. Qed.
Hint Resolve eqCmod_refl eqCmodm0 : core.

Lemma eqCmod0 e x : (x == 0 %[mod e])%C = (e %| x)%C.
Proof. by rewrite /eqCmod subr0. Qed.

Lemma eqCmod_sym e x y : ((x == y %[mod e]) = (y == x %[mod e]))%C.
Proof. by rewrite /eqCmod -opprB rpredN. Qed.

Lemma eqCmod_trans e y x z :
  (x == y %[mod e] -> y == z %[mod e] -> x == z %[mod e])%C.
Proof. by move=> Exy Eyz; rewrite /eqCmod -[x](subrK y) -addrA rpredD. Qed.

Lemma eqCmod_transl e x y z :
  (x == y %[mod e])%C -> (x == z %[mod e])%C = (y == z %[mod e])%C.
Proof. by move/(sym_left_transitive (eqCmod_sym e) (@eqCmod_trans e)). Qed.

Lemma eqCmod_transr e x y z :
  (x == y %[mod e])%C -> (z == x %[mod e])%C = (z == y %[mod e])%C.
Proof. by move/(sym_right_transitive (eqCmod_sym e) (@eqCmod_trans e)). Qed.

Lemma eqCmodN e x y : (- x == y %[mod e])%C = (x == - y %[mod e])%C.
Proof. by rewrite eqCmod_sym /eqCmod !opprK addrC. Qed.

Lemma eqCmodDr e x y z : (y + x == z + x %[mod e])%C = (y == z %[mod e])%C.
Proof. by rewrite /eqCmod addrAC opprD !addrA subrK. Qed.

Lemma eqCmodDl e x y z : (x + y == x + z %[mod e])%C = (y == z %[mod e])%C.
Proof. by rewrite !(addrC x) eqCmodDr. Qed.

Lemma eqCmodD e x1 x2 y1 y2 :
  (x1 == x2 %[mod e] -> y1 == y2 %[mod e] -> x1 + y1 == x2 + y2 %[mod e])%C.
Proof.
by rewrite -(eqCmodDl e x2 y1) -(eqCmodDr e y1); apply: eqCmod_trans.
Qed.

Lemma eqCmod_nat (e m n : nat) : (m == n %[mod e])%C = (m == n %[mod e]).
Proof.
without loss lenm: m n / (n <= m)%N.
  by move=> IH; case/orP: (leq_total m n) => /IH //; rewrite eqCmod_sym eq_sym.
by rewrite /eqCmod -natrB // dvdC_nat eqn_mod_dvd.
Qed.

Lemma eqCmod0_nat (e m : nat) : (m == 0 %[mod e])%C = (e %| m)%N.
Proof. by rewrite eqCmod0 dvdC_nat. Qed.

Lemma eqCmodMr e :
  {in Num.int, forall z x y, x == y %[mod e] -> x * z == y * z %[mod e]}%C.
Proof. by move=> z Zz x y; rewrite /eqCmod -mulrBl => /dvdC_mulr->. Qed.

Lemma eqCmodMl e :
  {in Num.int, forall z x y, x == y %[mod e] -> z * x == z * y %[mod e]}%C.
Proof. by move=> z Zz x y Exy; rewrite !(mulrC z) eqCmodMr. Qed.

Lemma eqCmodMl0 e : {in Num.int, forall x, x * e == 0 %[mod e]}%C.
Proof. by move=> x Zx; rewrite -(mulr0 x) eqCmodMl. Qed.

Lemma eqCmodMr0 e : {in Num.int, forall x, e * x == 0 %[mod e]}%C.
Proof. by move=> x Zx; rewrite /= mulrC eqCmodMl0. Qed.

Lemma eqCmod_addl_mul e : {in Num.int, forall x y, x * e + y == y %[mod e]}%C.
Proof. by move=> x Zx y; rewrite -{2}[y]add0r eqCmodDr eqCmodMl0. Qed.

Lemma eqCmodM e : {in Num.int & Num.int, forall x1 y2 x2 y1,
  x1 == x2 %[mod e] -> y1 == y2 %[mod e] -> x1 * y1 == x2 * y2 %[mod e]}%C.
Proof.
move=> x1 y2 Zx1 Zy2 x2 y1 eq_x /(eqCmodMl Zx1)/eqCmod_trans-> //.
exact: eqCmodMr.
Qed.

(* Rational number subset. *)

Lemma ratCK : cancel QtoC CtoQ.
Proof. by rewrite /getCrat; case: getCrat_subproof. Qed.

Lemma getCratK : {in Crat, cancel CtoQ QtoC}.
Proof. by move=> x /eqP. Qed.

Lemma Crat_rat (a : rat) : QtoC a \in Crat.
Proof. by rewrite unfold_in ratCK. Qed.

Lemma CratP x : reflect (exists a, x = QtoC a) (x \in Crat).
Proof.
by apply: (iffP eqP) => [<- | [a ->]]; [exists (CtoQ x) | rewrite ratCK].
Qed.

Lemma Crat0 : 0 \in Crat. Proof. by apply/CratP; exists 0; rewrite rmorph0. Qed.
Lemma Crat1 : 1 \in Crat. Proof. by apply/CratP; exists 1; rewrite rmorph1. Qed.
Hint Resolve Crat0 Crat1 : core.

Fact Crat_key : pred_key Crat. Proof. by []. Qed.
Fact Crat_divring_closed : divring_closed Crat.
Proof.
split=> // _ _ /CratP[x ->] /CratP[y ->].
  by rewrite -rmorphB Crat_rat.
by rewrite -fmorph_div Crat_rat.
Qed.
Canonical Crat_keyed := KeyedPred Crat_key.
Canonical Crat_opprPred := OpprPred Crat_divring_closed.
Canonical Crat_addrPred := AddrPred Crat_divring_closed.
Canonical Crat_mulrPred := MulrPred Crat_divring_closed.
Canonical Crat_zmodPred := ZmodPred Crat_divring_closed.
Canonical Crat_semiringPred := SemiringPred Crat_divring_closed.
Canonical Crat_smulrPred := SmulrPred Crat_divring_closed.
Canonical Crat_divrPred := DivrPred Crat_divring_closed.
Canonical Crat_subringPred := SubringPred Crat_divring_closed.
Canonical Crat_sdivrPred := SdivrPred Crat_divring_closed.
Canonical Crat_divringPred := DivringPred Crat_divring_closed.

Lemma rpred_Crat
        (S : {pred algC}) (ringS : divringPred S) (kS : keyed_pred ringS) :
  {subset Crat <= kS}.
Proof. by move=> _ /CratP[a ->]; apply: rpred_rat. Qed.

Lemma conj_Crat z : z \in Crat -> z^* = z.
Proof. by move/getCratK <-; rewrite fmorph_div !rmorph_int. Qed.

Lemma Creal_Crat : {subset Crat <= Creal}.
Proof. by move=> x /conj_Crat/CrealP. Qed.

Lemma Cint_rat a : (QtoC a \in Num.int) = (a \in Num.int).
Proof.
apply/idP/idP=> [Za | /numqK <-]; last by rewrite rmorph_int.
apply/RintP; exists (floorR (QtoC a)); apply: (can_inj ratCK).
by rewrite rmorph_int floorRK.
Qed.

Lemma minCpolyP x :
   {p | minCpoly x = pQtoC p /\ p \is monic
      & forall q, root (pQtoC q) x = (p %| q)%R}.
Proof. by rewrite /minCpoly; case: (minCpoly_subproof x) => p; exists p. Qed.

Lemma minCpoly_monic x : minCpoly x \is monic.
Proof. by have [p [-> mon_p] _] := minCpolyP x; rewrite map_monic. Qed.

Lemma minCpoly_eq0 x : (minCpoly x == 0) = false.
Proof. exact/negbTE/monic_neq0/minCpoly_monic. Qed.

Lemma root_minCpoly x : root (minCpoly x) x.
Proof. by have [p [-> _] ->] := minCpolyP x. Qed.

Lemma size_minCpoly x : (1 < size (minCpoly x))%N.
Proof. by apply: root_size_gt1 (root_minCpoly x); rewrite ?minCpoly_eq0. Qed.

(* Basic properties of automorphisms. *)
Section AutC.

Implicit Type nu : {rmorphism algC -> algC}.

Lemma aut_Crat nu : {in Crat, nu =1 id}.
Proof. by move=> _ /CratP[a ->]; apply: fmorph_rat. Qed.

Lemma Crat_aut nu x : (nu x \in Crat) = (x \in Crat).
Proof.
apply/idP/idP=> /CratP[a] => [|->]; last by rewrite fmorph_rat Crat_rat.
by rewrite -(fmorph_rat nu) => /fmorph_inj->; apply: Crat_rat.
Qed.

Lemma algC_invaut_subproof nu x : {y | nu y = x}.
Proof.
have [r Dp] := closed_field_poly_normal (minCpoly x).
suffices /mapP/sig2_eqW[y _ ->]: x \in map nu r by exists y.
rewrite -root_prod_XsubC; congr (root _ x): (root_minCpoly x).
have [q [Dq _] _] := minCpolyP x; rewrite Dq -(eq_map_poly (fmorph_rat nu)).
rewrite (map_poly_comp nu) -{q}Dq Dp (monicP (minCpoly_monic x)) scale1r.
rewrite rmorph_prod big_map; apply: eq_bigr => z _.
by rewrite rmorphB /= map_polyX map_polyC.
Qed.
Definition algC_invaut nu x := sval (algC_invaut_subproof nu x).

Lemma algC_invautK nu : cancel (algC_invaut nu) nu.
Proof. by move=> x; rewrite /algC_invaut; case: algC_invaut_subproof. Qed.

Lemma algC_autK nu : cancel nu (algC_invaut nu).
Proof. exact: inj_can_sym (algC_invautK nu) (fmorph_inj nu). Qed.

Fact algC_invaut_is_rmorphism nu : rmorphism (algC_invaut nu).
Proof. exact: can2_rmorphism (algC_autK nu) (algC_invautK nu). Qed.
Canonical algC_invaut_additive nu := Additive (algC_invaut_is_rmorphism nu).
Canonical algC_invaut_rmorphism nu := RMorphism (algC_invaut_is_rmorphism nu).

Lemma minCpoly_aut nu x : minCpoly (nu x) = minCpoly x.
Proof.
wlog suffices dvd_nu: nu x / (minCpoly x %| minCpoly (nu x))%R.
  apply/eqP; rewrite -eqp_monic ?minCpoly_monic //; apply/andP; split=> //.
  by rewrite -{2}(algC_autK nu x) dvd_nu.
have [[q [Dq _] min_q] [q1 [Dq1 _] _]] := (minCpolyP x, minCpolyP (nu x)).
rewrite Dq Dq1 dvdp_map -min_q -(fmorph_root nu) -map_poly_comp.
by rewrite (eq_map_poly (fmorph_rat nu)) -Dq1 root_minCpoly.
Qed.

End AutC.

End AlgebraicsTheory.
Hint Resolve Crat0 Crat1 dvdC0 dvdC_refl eqCmod_refl eqCmodm0 : core.

Module mc_1_12.

Implicit Types (x y z : algC) (n : nat) (m : int) (b : bool).

Notation Cint := (Num.int : {pred algC}) (only parsing).
Notation Cnat := (Num.nat : {pred algC}) (only parsing).
Notation floorC := (floorR : algC -> int) (only parsing).
Notation truncC := (Num.trunc : algC -> nat) (only parsing).

Lemma Creal0 : 0 \is Creal. Proof. exact: real0. Qed.
Lemma Creal1 : 1 \is Creal. Proof. exact: real1. Qed.

Lemma floorC_itv x : x \is Creal -> (floorC x)%:~R <= x < (floorC x + 1)%:~R.
Proof. exact: floorR_itv. Qed.

Lemma floorC_def x m : m%:~R <= x < (m + 1)%:~R -> floorC x = m.
Proof. exact: floorR_def. Qed.

Lemma intCK : cancel intr floorC.
Proof. exact: intRK. Qed.

Lemma floorCK : {in Cint, cancel floorC intr}.
Proof. exact: floorRK. Qed.

Lemma floorC0 : floorC 0 = 0. Proof. exact: floorR0. Qed.
Lemma floorC1 : floorC 1 = 1. Proof. exact: floorR1. Qed.

Lemma floorCpK (p : {poly algC}) :
  p \is a polyOver Cint -> map_poly intr (map_poly floorC p) = p.
Proof. exact: floorRpK. Qed.

Lemma floorCpP (p : {poly algC}) :
  p \is a polyOver Cint -> {q | p = map_poly intr q}.
Proof. exact: floorRpP. Qed.

Lemma Cint_int m : m%:~R \in Cint.
Proof. exact: Rint_int. Qed.

Lemma CintP x : reflect (exists m, x = m%:~R) (x \in Cint).
Proof. exact: RintP. Qed.

Lemma floorCD : {in Cint & Creal, {morph floorC : x y / x + y}}.
Proof. exact: floorRD. Qed.

Lemma floorCN : {in Cint, {morph floorC : x / - x}}.
Proof. exact: floorRN. Qed.

Lemma floorCM : {in Cint &, {morph floorC : x y / x * y}}.
Proof. exact: floorRM. Qed.

Lemma floorCX n : {in Cint, {morph floorC : x / x ^+ n}}.
Proof. exact: floorRX. Qed.

Lemma rpred_Cint
        (S : {pred algC}) (ringS : subringPred S) (kS : keyed_pred ringS) x :
  x \in Cint -> x \in kS.
Proof. exact: rpred_Rint. Qed.

Lemma Cint0 : 0 \in Cint. Proof. exact: Rint0. Qed.
Lemma Cint1 : 1 \in Cint. Proof. exact: Rint1. Qed.

Lemma Creal_Cint : {subset Cint <= Creal}.
Proof. exact: Rreal_Rint. Qed.

Lemma conj_Cint x : x \in Cint -> x^* = x.
Proof. exact: conj_Rint. Qed.

Lemma Cint_normK x : x \in Cint -> `|x| ^+ 2 = x ^+ 2.
Proof. exact: Rint_normK. Qed.

Lemma CintEsign x : x \in Cint -> x = (-1) ^+ (x < 0)%C * `|x|.
Proof. exact: RintEsign. Qed.

Lemma truncC_itv x : 0 <= x -> (truncC x)%:R <= x < (truncC x).+1%:R.
Proof. exact: truncR_itv. Qed.

Lemma truncC_def x n : n%:R <= x < n.+1%:R -> truncC x = n.
Proof. exact: truncR_def. Qed.

Lemma natCK n : truncC n%:R = n.
Proof. exact: natRK. Qed.

Lemma CnatP x : reflect (exists n, x = n%:R) (x \in Cnat).
Proof. exact: RnatP. Qed.

Lemma truncCK : {in Cnat, cancel truncC (GRing.natmul 1)}.
Proof. exact: truncRK. Qed.

Lemma truncC_gt0 x : (0 < truncC x)%N = (1 <= x).
Proof. exact: truncR_gt0. Qed.

Lemma truncC0Pn x : reflect (truncC x = 0%N) (~~ (1 <= x)).
Proof. exact: truncR0Pn. Qed.

Lemma truncC0 : truncC 0 = 0%N. Proof. exact: truncR0. Qed.
Lemma truncC1 : truncC 1 = 1%N. Proof. exact: truncR1. Qed.

Lemma truncCD :
  {in Cnat & Num.nneg, {morph truncC : x y / x + y >-> (x + y)%N}}.
Proof. exact: truncRD. Qed.

Lemma truncCM : {in Cnat &, {morph truncC : x y / x * y >-> (x * y)%N}}.
Proof. exact: truncRM. Qed.

Lemma truncCX n : {in Cnat, {morph truncC : x / x ^+ n >-> (x ^ n)%N}}.
Proof. exact: truncRX. Qed.

Lemma rpred_Cnat
        (S : {pred algC}) (ringS : semiringPred S) (kS : keyed_pred ringS) x :
  x \in Cnat -> x \in kS.
Proof. exact: rpred_Rnat. Qed.

Lemma Cnat_nat n : n%:R \in Cnat.
Proof. exact: Rnat_nat. Qed.
Lemma Cnat0 : 0 \in Cnat. Proof. exact: Rnat0. Qed.
Lemma Cnat1 : 1 \in Cnat. Proof. exact: Rnat1. Qed.

Lemma Cnat_ge0 x : x \in Cnat -> 0 <= x.
Proof. exact: Rnat_ge0. Qed.

Lemma Cnat_gt0 x : x \in Cnat -> (0 < x) = (x != 0).
Proof. exact: Rnat_gt0. Qed.

Lemma conj_Cnat x : x \in Cnat -> x^* = x.
Proof. exact: conj_Rnat. Qed.

Lemma norm_Cnat x : x \in Cnat -> `|x| = x.
Proof. exact: norm_Rnat. Qed.

Lemma Creal_Cnat : {subset Cnat <= Creal}.
Proof. exact: Rreal_Rnat. Qed.

Lemma Cnat_sum_eq1 (I : finType) (P : pred I) (F : I -> algC) :
     (forall i, P i -> F i \in Cnat) -> \sum_(i | P i) F i = 1 ->
   {i : I | [/\ P i, F i = 1 & forall j, j != i -> P j -> F j = 0]}.
Proof. exact: Rnat_sum_eq1. Qed.

Lemma Cnat_mul_eq1 x y :
  x \in Cnat -> y \in Cnat -> (x * y == 1) = (x == 1) && (y == 1).
Proof. exact: Rnat_mul_eq1. Qed.

Lemma Cnat_prod_eq1 (I : finType) (P : pred I) (F : I -> algC) :
    (forall i, P i -> F i \in Cnat) -> \prod_(i | P i) F i = 1 ->
  forall i, P i -> F i = 1.
Proof. exact: Rnat_prod_eq1. Qed.

Lemma Cint_Cnat : {subset Cnat <= Cint}.
Proof. exact: Rint_Rnat. Qed.

Lemma CintE x : (x \in Cint) = (x \in Cnat) || (- x \in Cnat).
Proof. exact: RintE. Qed.

Lemma Cnat_norm_Cint x : x \in Cint -> `|x| \in Cnat.
Proof. exact: Rnat_norm_Rint. Qed.

Lemma CnatEint x : (x \in Cnat) = (x \in Cint) && (0 <= x).
Proof. exact: RnatEint. Qed.

Lemma CintEge0 x : 0 <= x -> (x \in Cint) = (x \in Cnat).
Proof. exact: RintEge0. Qed.

Lemma Cnat_exp_even x n : ~~ odd n -> x \in Cint -> x ^+ n \in Cnat.
Proof. exact: Rnat_exp_even. Qed.

Lemma norm_Cint_ge1 x : x \in Cint -> x != 0 -> 1 <= `|x|.
Proof. exact: norm_Rint_ge1. Qed.

Lemma sqr_Cint_ge1 x : x \in Cint -> x != 0 -> 1 <= x ^+ 2.
Proof. exact: sqr_Rint_ge1. Qed.

Lemma Cint_ler_sqr x : x \in Cint -> x <= x ^+ 2.
Proof. exact: Rint_ler_sqr. Qed.

Section AutC.

Implicit Type nu : {rmorphism algC -> algC}.

Lemma aut_Cnat nu : {in Cnat, nu =1 id}. Proof. exact: aut_Rnat. Qed.
Lemma aut_Cint nu : {in Cint, nu =1 id}. Proof. exact: aut_Rint. Qed.

Lemma Cnat_aut nu x : (nu x \in Cnat) = (x \in Cnat).
Proof. exact: Rnat_aut. Qed.

Lemma Cint_aut nu x : (nu x \in Cint) = (x \in Cint).
Proof. exact: Rint_aut. Qed.

End AutC.

Section AutLmodC.

Variables (U V : lmodType algC) (f : {additive U -> V}).

Lemma raddfZ_Cnat a u : a \in Cnat -> f (a *: u) = a *: f u.
Proof. exact: raddfZ_Rnat. Qed.

Lemma raddfZ_Cint a u : a \in Cint -> f (a *: u) = a *: f u.
Proof. exact: raddfZ_Rint. Qed.

End AutLmodC.

Section PredCmod.

Variable V : lmodType algC.

Lemma rpredZ_Cnat S (addS : @addrPred V S) (kS : keyed_pred addS) :
  {in Cnat & kS, forall z u, z *: u \in kS}.
Proof. exact: rpredZ_Rnat. Qed.

Lemma rpredZ_Cint S (subS : @zmodPred V S) (kS : keyed_pred subS) :
  {in Cint & kS, forall z u, z *: u \in kS}.
Proof. exact: rpredZ_Rint. Qed.

End PredCmod.

End mc_1_12.

#[deprecated(since="mathcomp 1.13.0", note="Use Num.int instead.")]
Notation Cint := (Num.int : {pred algC}) (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use Num.nat instead.")]
Notation Cnat := (Num.nat : {pred algC}) (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use floorR instead.")]
Notation floorC := (floorR : algC -> int) (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use Num.trunc instead.")]
Notation truncC := (Num.trunc : algC -> nat) (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use real0 instead.")]
Notation Creal0 := mc_1_12.Creal0 (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use real1 instead.")]
Notation Creal1 := mc_1_12.Creal1 (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use floorR_itv instead.")]
Notation floorC_itv := mc_1_12.floorC_itv (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use floorR_def instead.")]
Notation floorC_def := mc_1_12.floorC_def (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use intRK instead.")]
Notation intCK := mc_1_12.intCK (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use floorRK instead.")]
Notation floorCK := mc_1_12.floorCK (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use floorR0 instead.")]
Notation floorC0 := mc_1_12.floorC0 (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use floorR1 instead.")]
Notation floorC1 := mc_1_12.floorC1 (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use floorRpK instead.")]
Notation floorCpK := mc_1_12.floorCpK (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use floorRpP instead.")]
Notation floorCpP := mc_1_12.floorCpP (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use Rint_int instead.")]
Notation Cint_int := mc_1_12.Cint_int (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use RintP instead.")]
Notation CintP := mc_1_12.CintP (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use floorRD instead.")]
Notation floorCD := mc_1_12.floorCD (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use floorRN instead.")]
Notation floorCN := mc_1_12.floorCN (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use floorRM instead.")]
Notation floorCM := mc_1_12.floorCM (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use floorRX instead.")]
Notation floorCX := mc_1_12.floorCX (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use rpred_Rint instead.")]
Notation rpred_Cint := mc_1_12.rpred_Cint (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use Rint0 instead.")]
Notation Cint0 := mc_1_12.Cint0 (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use Rint1 instead.")]
Notation Cint1 := mc_1_12.Cint1 (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use Rreal_Rint instead.")]
Notation Creal_Cint := mc_1_12.Creal_Cint (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use conj_Rint instead.")]
Notation conj_Cint := mc_1_12.conj_Cint (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use Rint_normK instead.")]
Notation Cint_normK := mc_1_12.Cint_normK (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use RintEsign instead.")]
Notation CintEsign := mc_1_12.CintEsign (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use truncR_itv instead.")]
Notation truncC_itv := mc_1_12.truncC_itv (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use truncR_def instead.")]
Notation truncC_def := mc_1_12.truncC_def (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use natRK instead.")]
Notation natCK := mc_1_12.natCK (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use RnatP instead.")]
Notation CnatP := mc_1_12.CnatP (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use truncRK instead.")]
Notation truncCK := mc_1_12.truncCK (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use truncR_gt0 instead.")]
Notation truncC_gt0 := mc_1_12.truncC_gt0 (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use truncR0Pn instead.")]
Notation truncC0Pn := mc_1_12.truncC0Pn (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use truncR0 instead.")]
Notation truncC0 := mc_1_12.truncC0 (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use truncR1 instead.")]
Notation truncC1 := mc_1_12.truncC1 (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use truncRD instead.")]
Notation truncCD := mc_1_12.truncCD (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use truncRM instead.")]
Notation truncCM := mc_1_12.truncCM (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use truncRX instead.")]
Notation truncCX := mc_1_12.truncCX (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use rpred_Rnat instead.")]
Notation rpred_Cnat := mc_1_12.rpred_Cnat (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use Rnat_nat instead.")]
Notation Cnat_nat := mc_1_12.Cnat_nat (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use Rnat0 instead.")]
Notation Cnat0 := mc_1_12.Cnat0 (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use Rnat1 instead.")]
Notation Cnat1 := mc_1_12.Cnat1 (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use Rnat_ge0 instead.")]
Notation Cnat_ge0 := mc_1_12.Cnat_ge0 (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use Rnat_gt0 instead.")]
Notation Cnat_gt0 := mc_1_12.Cnat_gt0 (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use conj_Rnat instead.")]
Notation conj_Cnat := mc_1_12.conj_Cnat (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use norm_Rnat instead.")]
Notation norm_Cnat := mc_1_12.norm_Cnat (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use Rreal_Rnat instead.")]
Notation Creal_Cnat := mc_1_12.Creal_Cnat (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use Rnat_sum_eq1 instead.")]
Notation Cnat_sum_eq1 := mc_1_12.Cnat_sum_eq1 (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use Rnat_mul_eq1 instead.")]
Notation Cnat_mul_eq1 := mc_1_12.Cnat_mul_eq1 (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use Rnat_prod_eq1 instead.")]
Notation Cnat_prod_eq1 := mc_1_12.Cnat_prod_eq1 (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use Rint_Rnat instead.")]
Notation Cint_Cnat := mc_1_12.Cint_Cnat (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use RintE instead.")]
Notation CintE := mc_1_12.CintE (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use Rnat_norm_Rint instead.")]
Notation Cnat_norm_Cint := mc_1_12.Cnat_norm_Cint (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use RnatEint instead.")]
Notation CnatEint := mc_1_12.CnatEint (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use RintEge0 instead.")]
Notation CintEge0 := mc_1_12.CintEge0 (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use Rnat_exp_even instead.")]
Notation Cnat_exp_even := mc_1_12.Cnat_exp_even (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use norm_Rint_ge1 instead.")]
Notation norm_Cint_ge1 := mc_1_12.norm_Cint_ge1 (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use sqr_Rint_ge1 instead.")]
Notation sqr_Cint_ge1 := mc_1_12.sqr_Cint_ge1 (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use Rint_ler_sqr instead.")]
Notation Cint_ler_sqr := mc_1_12.Cint_ler_sqr (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use aut_Rnat instead.")]
Notation aut_Cnat := mc_1_12.aut_Cnat (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use aut_Rint instead.")]
Notation aut_Cint := mc_1_12.aut_Cint (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use Rnat_aut instead.")]
Notation Cnat_aut := mc_1_12.Cnat_aut (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use Rint_aut instead.")]
Notation Cint_aut := mc_1_12.Cint_aut (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use raddfZ_Rnat instead.")]
Notation raddfZ_Cnat := mc_1_12.raddfZ_Cnat (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use raddfZ_Rint instead.")]
Notation raddfZ_Cint := mc_1_12.raddfZ_Cint (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use rpredZ_Rnat instead.")]
Notation rpredZ_Cnat := mc_1_12.rpredZ_Cnat (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use rpredZ_Rint instead.")]
Notation rpredZ_Cint := mc_1_12.rpredZ_Cint (only parsing).
