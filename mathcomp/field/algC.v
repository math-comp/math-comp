(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq choice div fintype.
Require Import path bigop finset prime ssralg poly polydiv mxpoly.
Require Import generic_quotient countalg ssrnum ssrint rat intdiv.
Require Import algebraics_fundamentals.

(******************************************************************************)
(* This file provides an axiomatic construction of the algebraic numbers.     *)
(* The construction only assumes the existence of an algebraically closed     *)
(* filed with an automorphism of order 2; this amounts to the purely          *)
(* algebraic contents of the Fundamenta Theorem of Algebra.                   *)
(*       algC == the closed, countable field of algebraic numbers.            *)
(*  algCeq, algCring, ..., algCnumField == structures for algC.               *)
(*        z^* == the complex conjugate of z (:= conjC z).                     *)
(*    sqrtC z == a nonnegative square root of z, i.e., 0 <= sqrt x if 0 <= x. *)
(*  n.-root z == more generally, for n > 0, an nth root of z, chosen with a   *)
(*               minimal non-negative argument for n > 1 (i.e., with a        *)
(*               maximal real part subject to a nonnegative imaginary part).  *)
(*               Note that n.-root (-1) is a primitive 2nth root of unity,    *)
(*               an thus not equal to -1 for n odd > 1 (this will be shown in *)
(*               file cyclotomic.v).                                          *)
(* The ssrnum interfaces are implemented for algC as follows:                 *)
(*     x <= y <=> (y - x) is a nonnegative real                               *)
(*      x < y <=> (y - x) is a (strictly) positive real                       *)
(*       `|z| == the complex norm of z, i.e., sqrtC (z * z^* ).               *)
(*      Creal == the subset of real numbers (:= Num.real for algC).           *)
(* In addition, we provide:                                                   *)
(*         'i == the imaginary number (:= sqrtC (-1)).                        *)
(*      'Re z == the real component of z.                                     *)
(*      'Im z == the imaginary component of z.                                *)
(*       Crat == the subset of rational numbers.                              *)
(*       Cint == the subset of integers.                                      *)
(*       Cnat == the subset of natural integers.                              *)
(*  getCrat z == some a : rat such that ratr a = z, provided z \in Crat.      *)
(*   floorC z == for z \in Creal, an m : int s.t. m%:~R <= z < (m + 1)%:~R.   *)
(*   truncC z == for z >= 0, an n : nat s.t. n%:R <= z < n.+1%:R, else 0%N.   *)
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

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(* The Num mixin for an algebraically closed field with an automorphism of    *)
(* order 2, making it into a field of complex numbers.                        *)
Lemma ComplexNumMixin (L : closedFieldType) (conj : {rmorphism L -> L}) :
    involutive conj -> ~ conj =1 id ->
  {numL | forall x : NumDomainType L numL, `|x| ^+ 2 = x * conj x}.
Proof.
move=> conjK conj_nt.
have nz2: 2%:R != 0 :> L.
  apply/eqP=> char2; apply: conj_nt => e; apply/eqP/idPn=> eJ.
  have opp_id x: - x = x :> L.
    by apply/esym/eqP; rewrite -addr_eq0 -mulr2n -mulr_natl char2 mul0r.
  have{char2} char2: 2 \in [char L] by exact/eqP.
  without loss{eJ} eJ: e / conj e = e + 1.
    move/(_ (e / (e + conj e))); apply.
    rewrite fmorph_div rmorphD conjK -{1}[conj e](addNKr e) mulrDl.
    by rewrite opp_id (addrC e) divff // addr_eq0 opp_id.
  pose a := e * conj e; have aJ: conj a = a by rewrite rmorphM conjK mulrC.
  have [w Dw] := @solve_monicpoly _ 2 (nth 0 [:: e * a; - 1]) isT.
  have{Dw} Dw: w ^+ 2 + w = e * a.
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
    move=> Ru v_ge0; have [-> // | nz_u] := eqVneq u 0.
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
  rewrite  subrr addr0 {2}(mulrC x) rmorphM mulrACA -opprB addrAC -sqrrB -sqrMi.
  apply/posP; exists (i * (x * conj y - y * conj x)); congr (_ * _).
  rewrite !(rmorphM, rmorphB) iJ !conjK mulNr -mulrN opprB.
  by rewrite (mulrC x) (mulrC y).
by exists (Num.Mixin normD sposD norm_eq0 pos_linear normM (rrefl _) (rrefl _)).
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

Parameter numMixin : Num.mixin_of ringType.
Canonical numDomainType := NumDomainType type numMixin.
Canonical numFieldType := [numFieldType of type].

Parameter conj : {rmorphism type -> type}.
Axiom conjK : involutive conj.
Axiom normK : forall x, `|x| ^+ 2 = x * conj x.

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

Definition countMixin : Countable.mixin_of type := CanCountMixin (@reprK _ _).
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

Definition fieldMixin := @FieldMixin _ _ mulVf inv0.
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

Definition decFieldMixin := closed_field.closed_fields_QEMixin closedFieldAxiom.
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
have/ltr_geF/idP[] := @ltr01 Lnum; rewrite -oppr_ge0 -(rmorphN1 CtoL_rmorphism).
rewrite -i2 rmorphX /= expr2 -{2}iL_J -(svalP LnumMixin).
by rewrite exprn_ge0 ?normr_ge0.
Qed.

Definition numMixin := sval (ComplexNumMixin conjK conj_nt).
Canonical numDomainType := NumDomainType type numMixin.
Canonical numFieldType := [numFieldType of type].

Lemma normK u : `|u| ^+ 2 = u * conj u.
Proof. exact: svalP (ComplexNumMixin conjK conj_nt) u. Qed.

Lemma algebraic : integralRange (@ratr unitRingType).
Proof.
move=> u; have [p mon_p pu0] := CtoL_P u; exists p => {mon_p}//.
rewrite -(fmorph_root CtoL_rmorphism) -map_poly_comp; congr (root _ _): pu0.
by apply/esym/eq_map_poly; apply: fmorph_eq_rat.
Qed.

End Implementation.

Definition divisor := Implementation.type.

Module Internals.

Import Implementation.

Local Notation algC := type.
Local Notation "z ^*" := (conj z) (at level 2, format "z ^*") : ring_scope.
Local Notation QtoC := (ratr : rat -> algC).
Local Notation QtoCm := [rmorphism of QtoC].
Local Notation pQtoC := (map_poly QtoC).
Local Notation ZtoQ := (intr : int -> rat).
Local Notation ZtoC := (intr : int -> algC).
Local Notation Creal := (Num.real : qualifier 0 algC).

Fact algCi_subproof : {i : algC | i ^+ 2 = -1}.
Proof. exact: imaginary_exists. Qed.

Let Re2 z := z + z^*.
Definition nnegIm z := 0 <= sval algCi_subproof * (z^* - z).
Definition argCle y z := nnegIm z ==> nnegIm y && (Re2 z <= Re2 y).

CoInductive rootC_spec n (x : algC) : Type :=
  RootCspec (y : algC) of if (n > 0)%N then y ^+ n = x else y = 0
                        & forall z, (n > 0)%N -> z ^+ n = x -> argCle y z.

Fact rootC_subproof n x : rootC_spec n x.
Proof.
have realRe2 u : Re2 u \is Creal.
  rewrite realEsqr expr2 {2}/Re2 -{2}[u]conjK addrC -rmorphD -normK.
  by rewrite exprn_ge0 ?normr_ge0.
have argCtotal : total argCle.
  move=> u v; rewrite /total /argCle.
  by do 2!case: (nnegIm _) => //; rewrite ?orbT //= real_leVge.
have argCtrans : transitive argCle.
  move=> u v w /implyP geZuv /implyP geZvw; apply/implyP.
  by case/geZvw/andP=> /geZuv/andP[-> geRuv] /ler_trans->.
pose p := 'X^n - (x *+ (n > 0))%:P; have [r0 Dp] := closed_field_poly_normal p.
have sz_p: size p = n.+1.
  rewrite size_addl ?size_polyXn // ltnS size_opp size_polyC mulrn_eq0.
  by case: posnP => //; case: negP.
pose r := sort argCle r0; have r_arg: sorted argCle r by apply: sort_sorted.
have{Dp} Dp: p = \prod_(z <- r) ('X - z%:P).
  rewrite Dp lead_coefE sz_p coefB coefXn coefC -mulrb -mulrnA mulnb lt0n andNb.
  rewrite subr0 eqxx scale1r; apply: eq_big_perm.
  by rewrite perm_eq_sym perm_sort.
have mem_rP z: (n > 0)%N -> reflect (z ^+ n = x) (z \in r).
  move=> n_gt0; rewrite -root_prod_XsubC -Dp rootE !hornerE hornerXn n_gt0.
  by rewrite subr_eq0; apply: eqP.
exists r`_0 => [|z n_gt0 /(mem_rP z n_gt0) r_z].
  have sz_r: size r = n by apply: succn_inj; rewrite -sz_p Dp size_prod_XsubC.
  case: posnP => [n0 | n_gt0]; first by rewrite nth_default // sz_r n0.
  by apply/mem_rP=> //; rewrite mem_nth ?sz_r.
case: {Dp mem_rP}r r_z r_arg => // y r1; rewrite inE => /predU1P[-> _|r1z].
  by apply/implyP=> ->; rewrite lerr.
by move/(order_path_min argCtrans)/allP->.
Qed.

CoInductive getCrat_spec : Type := GetCrat_spec CtoQ of cancel QtoC CtoQ.

Fact getCrat_subproof : getCrat_spec.
Proof.
have isQ := rat_algebraic_decidable algebraic.
exists (fun z => if isQ z is left Qz then sval (sig_eqW Qz) else 0) => a.
case: (isQ _) => [Qa | []]; last by exists a.
by case: (sig_eqW _) => b /= /fmorph_inj.
Qed.

Fact floorC_subproof x : {m | x \is Creal -> ZtoC m <= x < ZtoC (m + 1)}.
Proof.
have [Rx | _] := boolP (x \is Creal); last by exists 0.
without loss x_ge0: x Rx / x >= 0.
  have [x_ge0 | /ltrW x_le0] := real_ger0P Rx; first exact.
  case/(_ (- x)) => [||m /(_ isT)]; rewrite ?rpredN ?oppr_ge0 //.
  rewrite ler_oppr ltr_oppl -!rmorphN opprD /= ltr_neqAle ler_eqVlt.
  case: eqP => [-> _ | _ /and3P[lt_x_m _ le_m_x]].
    by exists (- m) => _; rewrite lerr rmorphD ltr_addl ltr01.
  by exists (- m - 1); rewrite le_m_x subrK.
have /ex_minnP[n lt_x_n1 min_n]: exists n, x < n.+1%:R.
  have [n le_x_n] := rat_algebraic_archimedean algebraic x.
  by exists n; rewrite -(ger0_norm x_ge0) (ltr_trans le_x_n) ?ltr_nat.
exists n%:Z => _; rewrite addrC -intS lt_x_n1 andbT.
case Dn: n => // [n1]; rewrite -Dn.
have [||//|] := @real_lerP _ n%:R x; rewrite ?rpred_nat //.
by rewrite Dn => /min_n; rewrite Dn ltnn.
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
Notation conjC := conj.
Delimit Scope C_scope with C.
Delimit Scope C_core_scope with Cc.
Delimit Scope C_expanded_scope with Cx.
Open Scope C_core_scope.
Notation "x ^*" := (conjC x) (at level 2, format "x ^*") : C_core_scope.
Notation "x ^*" := x^* (only parsing) : C_scope.

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
Canonical numDomainType.
Canonical fieldType.
Canonical numFieldType.
Canonical decFieldType.
Canonical closedFieldType.

Notation algCeq := eqType.
Notation algCzmod := zmodType.
Notation algCring := ringType.
Notation algCuring := unitRingType.
Notation algCnum := numDomainType.
Notation algCfield := fieldType.
Notation algCnumField := numFieldType.

Definition rootC n x := let: RootCspec y _ _ := rootC_subproof n x in y.
Notation "n .-root" := (rootC n) (at level 2, format "n .-root") : C_core_scope.
Notation "n .-root" := (rootC n) (only parsing) : C_scope.
Notation sqrtC := 2.-root.

Definition algCi := sqrtC (-1).
Notation "'i" := algCi (at level 0) : C_core_scope.
Notation "'i" := 'i (only parsing) : C_scope.

Definition algRe x := (x + x^*) / 2%:R.
Definition algIm x := 'i * (x^* - x) / 2%:R.
Notation "'Re z" := (algRe z) (at level 10, z at level 8) : C_core_scope.
Notation "'Im z" := (algIm z) (at level 10, z at level 8) : C_core_scope.
Notation "'Re z" := ('Re z) (only parsing) : C_scope.
Notation "'Im z" := ('Im z) (only parsing) : C_scope.

Notation Creal := (@Num.Def.Rreal numDomainType).

Definition getCrat := let: GetCrat_spec CtoQ _ := getCrat_subproof in CtoQ.
Definition Crat : pred_class := fun x : algC => ratr (getCrat x) == x.

Definition floorC x := sval (floorC_subproof x).
Definition Cint : pred_class := fun x : algC => (floorC x)%:~R == x.

Definition truncC x := if x >= 0 then `|floorC x|%N else 0%N.
Definition Cnat : pred_class := fun x : algC => (truncC x)%:R == x.

Definition minCpoly x : {poly algC} :=
  let: exist2 p _ _ := minCpoly_subproof x in map_poly ratr p.

Coercion nat_divisor : nat >-> divisor.
Coercion int_divisor : int >-> divisor.
Coercion algC_divisor : algC >-> divisor.

Lemma nCdivE (p : nat) : p = p%:R :> divisor. Proof. by []. Qed.
Lemma zCdivE (p : int) : p = p%:~R :> divisor. Proof. by []. Qed.
Definition CdivE := (nCdivE, zCdivE).

Definition dvdC (x : divisor) : pred_class :=
   fun y : algC => if x == 0 then y == 0 else y / x \in Cint.
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
Local Hint Resolve (@intr_inj _ : injective ZtoC).

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

Definition conjCK : involutive conjC := Algebraics.Implementation.conjK.
Definition normCK x : `|x| ^+ 2 = x * x^* := Algebraics.Implementation.normK x.
Definition algC_algebraic x := Algebraics.Implementation.algebraic x.

Lemma normCKC x : `|x| ^+ 2 = x^* * x. Proof. by rewrite normCK mulrC. Qed.

Lemma mul_conjC_ge0 x : 0 <= x * x^*.
Proof. by rewrite -normCK exprn_ge0 ?normr_ge0. Qed.

Lemma mul_conjC_gt0 x : (0 < x * x^*) = (x != 0).
Proof. 
have [->|x_neq0] := altP eqP; first by rewrite rmorph0 mulr0.
by rewrite -normCK exprn_gt0 ?normr_gt0.
Qed.

Lemma mul_conjC_eq0 x : (x * x^* == 0) = (x == 0).
Proof. by rewrite -normCK expf_eq0 normr_eq0. Qed.

Lemma conjC_ge0 x : (0 <= x^*) = (0 <= x).
Proof.
wlog suffices: x / 0 <= x -> 0 <= x^*.
  by move=> IH; apply/idP/idP=> /IH; rewrite ?conjCK.
rewrite le0r => /predU1P[-> | x_gt0]; first by rewrite rmorph0.
by rewrite -(pmulr_rge0 _ x_gt0) mul_conjC_ge0.
Qed.

Lemma conjC_nat n : (n%:R)^* = n%:R. Proof. exact: rmorph_nat. Qed.
Lemma conjC0 : 0^* = 0. Proof. exact: rmorph0. Qed.
Lemma conjC1 : 1^* = 1. Proof. exact: rmorph1. Qed.
Lemma conjC_eq0 x : (x^* == 0) = (x == 0). Proof. exact: fmorph_eq0. Qed.

Lemma invC_norm x : x^-1 = `|x| ^- 2 * x^*.
Proof.
have [-> | nx_x] := eqVneq x 0; first by rewrite conjC0 mulr0 invr0.
by rewrite normCK invfM divfK ?conjC_eq0.
Qed.

(* Real number subset. *)

Lemma Creal0 : 0 \is Creal. Proof. exact: rpred0. Qed.
Lemma Creal1 : 1 \is Creal. Proof. exact: rpred1. Qed.
Hint Resolve Creal0 Creal1. (* Trivial cannot resolve a general real0 hint. *)

Lemma CrealE x : (x \is Creal) = (x^* == x).
Proof.
rewrite realEsqr ger0_def normrX normCK.
by have [-> | /mulfI/inj_eq-> //] := eqVneq x 0; rewrite rmorph0 !eqxx.
Qed.

Lemma CrealP {x} : reflect (x^* = x) (x \is Creal).
Proof. by rewrite CrealE; apply: eqP. Qed.

Lemma conj_Creal x : x \is Creal -> x^* = x.
Proof. by move/CrealP. Qed.

Lemma conj_normC z : `|z|^* = `|z|.
Proof. by rewrite conj_Creal ?normr_real. Qed.

Lemma geC0_conj x : 0 <= x -> x^* = x.
Proof. by move=> /ger0_real/CrealP. Qed.

Lemma geC0_unit_exp x n : 0 <= x -> (x ^+ n.+1 == 1) = (x == 1).
Proof. by move=> x_ge0; rewrite pexpr_eq1. Qed.

(* Elementary properties of roots. *)

Ltac case_rootC := rewrite /rootC; case: (rootC_subproof _ _).

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

Lemma sqrCi : 'i ^+ 2 = -1. Proof. exact: rootCK. Qed.

Lemma nonRealCi : 'i \isn't Creal.
Proof. by rewrite realEsqr sqrCi oppr_ge0 ltr_geF ?ltr01. Qed.

Lemma neq0Ci : 'i != 0.
Proof. by apply: contraNneq nonRealCi => ->; apply: real0. Qed.

Lemma normCi : `|'i| = 1.
Proof.
apply/eqP; rewrite -(@pexpr_eq1 _ _ 2) ?normr_ge0 //.
by rewrite -normrX sqrCi normrN1.
Qed.

Lemma invCi : 'i^-1 = - 'i.
Proof. by rewrite -div1r -[1]opprK -sqrCi mulNr mulfK ?neq0Ci. Qed.

Lemma conjCi : 'i^* = - 'i.
Proof. by rewrite -invCi invC_norm normCi expr1n invr1 mul1r. Qed.

Lemma algCrect x : x = 'Re x + 'i * 'Im x.
Proof. 
rewrite 2!mulrA -expr2 sqrCi mulN1r opprB -mulrDl addrACA subrr addr0.
by rewrite -mulr2n -mulr_natr mulfK.
Qed.

Lemma Creal_Re x : 'Re x \is Creal.
Proof. by rewrite CrealE fmorph_div rmorph_nat rmorphD conjCK addrC. Qed.

Lemma Creal_Im x : 'Im x \is Creal.
Proof.
rewrite CrealE fmorph_div rmorph_nat rmorphM rmorphB conjCK.
by rewrite conjCi -opprB mulrNN.
Qed.
Hint Resolve Creal_Re Creal_Im.

Fact algRe_is_additive : additive algRe.
Proof. by move=> x y; rewrite /algRe rmorphB addrACA -opprD mulrBl. Qed.
Canonical algRe_additive := Additive algRe_is_additive.

Fact algIm_is_additive : additive algIm.
Proof.
by move=> x y; rewrite /algIm rmorphB opprD addrACA -opprD mulrBr mulrBl.
Qed.
Canonical algIm_additive := Additive algIm_is_additive.

Lemma Creal_ImP z : reflect ('Im z = 0) (z \is Creal).
Proof.
rewrite CrealE -subr_eq0 -(can_eq (mulKf neq0Ci)) mulr0.
by rewrite -(can_eq (divfK nz2)) mul0r; apply: eqP.
Qed.

Lemma Creal_ReP z : reflect ('Re z = z) (z \in Creal).
Proof.
rewrite (sameP (Creal_ImP z) eqP) -(can_eq (mulKf neq0Ci)) mulr0.
by rewrite -(inj_eq (addrI ('Re z))) addr0 -algCrect eq_sym; apply: eqP.
Qed.

Lemma algReMl : {in Creal, forall x, {morph algRe : z / x * z}}.
Proof.
by move=> x Rx z /=; rewrite /algRe rmorphM (conj_Creal Rx) -mulrDr -mulrA.
Qed.

Lemma algReMr : {in Creal, forall x, {morph algRe : z / z * x}}.
Proof. by move=> x Rx z /=; rewrite mulrC algReMl // mulrC. Qed.

Lemma algImMl : {in Creal, forall x, {morph algIm : z / x * z}}.
Proof.
by move=> x Rx z; rewrite /algIm rmorphM (conj_Creal Rx) -mulrBr mulrCA !mulrA.
Qed.

Lemma algImMr : {in Creal, forall x, {morph algIm : z / z * x}}.
Proof. by move=> x Rx z /=; rewrite mulrC algImMl // mulrC. Qed.

Lemma algRe_i : 'Re 'i = 0. Proof. by rewrite /algRe conjCi subrr mul0r. Qed.

Lemma algIm_i : 'Im 'i = 1.
Proof.
rewrite /algIm conjCi -opprD mulrN -mulr2n mulrnAr ['i * _]sqrCi.
by rewrite mulNrn opprK divff.
Qed.

Lemma algRe_conj z : 'Re z^* = 'Re z.
Proof. by rewrite /algRe addrC conjCK. Qed.

Lemma algIm_conj z : 'Im z^* = - 'Im z.
Proof. by rewrite /algIm -mulNr -mulrN opprB conjCK. Qed.

Lemma algRe_rect : {in Creal &, forall x y, 'Re (x + 'i * y) = x}.
Proof.
move=> x y Rx Ry; rewrite /= raddfD /= (Creal_ReP x Rx).
by rewrite algReMr // algRe_i mul0r addr0.
Qed.

Lemma algIm_rect : {in Creal &, forall x y, 'Im (x + 'i * y) = y}.
Proof.
move=> x y Rx Ry; rewrite /= raddfD /= (Creal_ImP x Rx) add0r.
by rewrite algImMr // algIm_i mul1r.
Qed.

Lemma conjC_rect : {in Creal &, forall x y, (x + 'i * y)^* = x - 'i * y}.
Proof.
by move=> x y Rx Ry; rewrite /= rmorphD rmorphM conjCi mulNr !conj_Creal.
Qed.

Lemma addC_rect x1 y1 x2 y2 :
  (x1 + 'i * y1) + (x2 + 'i * y2) = x1 + x2 + 'i * (y1 + y2).
Proof. by rewrite addrACA -mulrDr. Qed.

Lemma oppC_rect x y : - (x + 'i * y)  = - x + 'i * (- y).
Proof. by rewrite mulrN -opprD. Qed.

Lemma subC_rect x1 y1 x2 y2 :
  (x1 + 'i * y1) - (x2 + 'i * y2) = x1 - x2 + 'i * (y1 - y2).
Proof. by rewrite oppC_rect addC_rect. Qed.

Lemma mulC_rect x1 y1 x2 y2 :
  (x1 + 'i * y1) * (x2 + 'i * y2)
      = x1 * x2 - y1 * y2 + 'i * (x1 * y2 + x2 * y1).
Proof.
rewrite mulrDl !mulrDr mulrCA -!addrA mulrAC -mulrA; congr (_ + _).
by rewrite mulrACA -expr2 sqrCi mulN1r addrA addrC. 
Qed.

Lemma normC2_rect :
  {in Creal &, forall x y, `|x + 'i * y| ^+ 2 = x ^+ 2 + y ^+ 2}.
Proof.
move=> x y Rx Ry; rewrite /= normCK rmorphD rmorphM conjCi !conj_Creal //.
by rewrite mulrC mulNr -subr_sqr exprMn sqrCi mulN1r opprK.
Qed.

Lemma normC2_Re_Im z : `|z| ^+ 2 = 'Re z ^+ 2 + 'Im z ^+ 2.
Proof. by rewrite -normC2_rect -?algCrect. Qed.

Lemma invC_rect :
  {in Creal &, forall x y, (x + 'i * y)^-1  = (x - 'i * y) / (x ^+ 2 + y ^+ 2)}.
Proof.
by move=> x y Rx Ry; rewrite /= invC_norm conjC_rect // mulrC normC2_rect.
Qed.

Lemma lerif_normC_Re_Creal z : `|'Re z| <= `|z| ?= iff (z \is Creal).
Proof.
rewrite -(mono_in_lerif ler_sqr); try by rewrite qualifE normr_ge0.
rewrite normCK conj_Creal // normC2_Re_Im -expr2.
rewrite addrC -lerif_subLR subrr (sameP (Creal_ImP _) eqP) -sqrf_eq0 eq_sym.
by apply: lerif_eq; rewrite -realEsqr.
Qed.

Lemma lerif_Re_Creal z : 'Re z <= `|z| ?= iff (0 <= z).
Proof.
have ubRe: 'Re z <= `|'Re z| ?= iff (0 <= 'Re z).
  by rewrite ger0_def eq_sym; apply/lerif_eq/real_ler_norm.
congr (_ <= _ ?= iff _): (lerif_trans ubRe (lerif_normC_Re_Creal z)).
apply/andP/idP=> [[zRge0 /Creal_ReP <- //] | z_ge0].
by have Rz := ger0_real z_ge0; rewrite (Creal_ReP _ _).
Qed.

(* Equality from polar coordinates, for the upper plane. *)
Lemma eqC_semipolar x y :
  `|x| = `|y| -> 'Re x = 'Re y -> 0 <= 'Im x * 'Im y -> x = y.
Proof.
move=> eq_norm eq_Re sign_Im.
rewrite [x]algCrect [y]algCrect eq_Re; congr (_ + 'i * _).
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
  rewrite /argCle !dIm ler_pmul2r ?invr_gt0 ?ltr0n //.
  by apply: (iffP implyP) => geZyz /geZyz/andP.
rewrite /('Im x) pmulr_lge0 ?invr_gt0 ?ltr0n //; congr (0 <= _ * _).
case Du: algCi_subproof => [u u2N1] /=.
have/eqP := u2N1; rewrite -sqrCi eqf_sqr => /pred2P[] //.
have:= conjCi; rewrite /'i; case_rootC => /= v v2n1 min_v conj_v Duv.
have{min_v} /idPn[] := min_v u isT u2N1; rewrite negb_imply /nnegIm Du /= Duv.
rewrite rmorphN conj_v opprK -opprD mulrNN mulNr -mulr2n mulrnAr -expr2 v2n1.
by rewrite mulNrn opprK ler0n oppr_ge0 (leC_nat 2 0).
Qed.

Lemma rootC_Re_max n x y :
  (n > 0)%N -> y ^+ n = x -> 0 <= 'Im y -> 'Re y <= 'Re (n.-root%C x).
Proof.
by move=> n_gt0 yn_x leI0y; case_rootC=> z /= _ /(_ y n_gt0 yn_x)/argCleP[].
Qed.

Let neg_unity_root n : (n > 1)%N -> exists2 w : algC, w ^+ n = 1 & 'Re w < 0.
Proof.
move=> n_gt1; have [|w /eqP pw_0] := closed_rootP (\poly_(i < n) (1 : algC)) _.
  by rewrite size_poly_eq ?oner_eq0 // -(subnKC n_gt1).
rewrite horner_poly (eq_bigr _ (fun _ _ => mul1r _)) in pw_0.
have wn1: w ^+ n = 1 by apply/eqP; rewrite -subr_eq0 subrX1 pw_0 mulr0.
suffices /existsP[i ltRwi0]: [exists i : 'I_n, 'Re (w ^+ i) < 0].
  by exists (w ^+ i) => //; rewrite exprAC wn1 expr1n.
apply: contra_eqT (congr1 algRe pw_0); rewrite negb_exists => /forallP geRw0.
rewrite raddf_sum raddf0 /= (bigD1 (Ordinal (ltnW n_gt1))) //=.
rewrite (Creal_ReP _ _) ?rpred1 // gtr_eqF ?ltr_paddr ?ltr01 //=.
by apply: sumr_ge0 => i _; rewrite real_lerNgt.
Qed.

Lemma Im_rootC_ge0 n x : (n > 1)%N -> 0 <= 'Im (n.-root x).
Proof.
set y := n.-root x => n_gt1; have n_gt0 := ltnW n_gt1.
apply: wlog_neg; rewrite -real_ltrNge // => ltIy0.
suffices [z zn_x leI0z]: exists2 z, z ^+ n = x & 'Im z >= 0.
  by rewrite /y; case_rootC => /= y1 _ /(_ z n_gt0 zn_x)/argCleP[].
have [w wn1 ltRw0] := neg_unity_root n_gt1.
wlog leRI0yw: w wn1 ltRw0 / 0 <= 'Re y * 'Im w. 
  move=> IHw; have: 'Re y * 'Im w \is Creal by rewrite rpredM.
  case/real_ger0P=> [|/ltrW leRIyw0]; first exact: IHw.
  apply: (IHw w^*); rewrite ?algRe_conj ?algIm_conj ?mulrN ?oppr_ge0 //.
  by rewrite -rmorphX wn1 rmorph1.
exists (w * y); first by rewrite exprMn wn1 mul1r rootCK. 
rewrite [w]algCrect [y]algCrect mulC_rect.
by rewrite algIm_rect ?rpredD ?rpredN 1?rpredM // addr_ge0 // ltrW ?nmulr_rgt0.
Qed.

Lemma rootC_lt0 n x : (1 < n)%N -> (n.-root x < 0) = false.
Proof.
set y := n.-root x => n_gt1; have n_gt0 := ltnW n_gt1.
apply: negbTE; apply: wlog_neg => /negbNE lt0y; rewrite ler_gtF //.
have Rx: x \is Creal by rewrite -[x](rootCK n_gt0) rpredX // ltr0_real.
have Re_y: 'Re y = y by apply/Creal_ReP; rewrite ltr0_real.
have [z zn_x leR0z]: exists2 z, z ^+ n = x & 'Re z >= 0.
  have [w wn1 ltRw0] := neg_unity_root n_gt1.
  exists (w * y); first by rewrite exprMn wn1 mul1r rootCK. 
  by rewrite algReMr ?ltr0_real // ltrW // nmulr_lgt0.
without loss leI0z: z zn_x leR0z / 'Im z >= 0.
  move=> IHz; have: 'Im z \is Creal by [].
  case/real_ger0P=> [|/ltrW leIz0]; first exact: IHz.
  apply: (IHz z^*); rewrite ?algRe_conj ?algIm_conj ?oppr_ge0 //.
  by rewrite -rmorphX zn_x conj_Creal.
by apply: ler_trans leR0z _; rewrite -Re_y ?rootC_Re_max ?ltr0_real.
Qed.

Lemma rootC_ge0 n x : (n > 0)%N -> (0 <= n.-root x) = (0 <= x).
Proof.
set y := n.-root x => n_gt0.
apply/idP/idP=> [/(exprn_ge0 n) | x_ge0]; first by rewrite rootCK.
rewrite -(ger_lerif (lerif_Re_Creal y)).
have Ray: `|y| \is Creal by apply: normr_real.
rewrite -(Creal_ReP _ Ray) rootC_Re_max ?(Creal_ImP _ Ray) //.
by rewrite -normrX rootCK // ger0_norm.
Qed.

Lemma rootC_gt0 n x : (n > 0)%N -> (n.-root x > 0) = (x > 0).
Proof. by move=> n_gt0; rewrite !lt0r rootC_ge0 ?rootC_eq0. Qed.

Lemma rootC_le0 n x : (1 < n)%N -> (n.-root x <= 0) = (x == 0).
Proof.
by move=> n_gt1; rewrite ler_eqVlt rootC_lt0 // orbF rootC_eq0 1?ltnW.
Qed.

Lemma ler_rootCl n : (n > 0)%N -> {in Num.nneg, {mono n.-root : x y / x <= y}}.
Proof.
move=> n_gt0 x x_ge0 y; have [y_ge0 | not_y_ge0] := boolP (0 <= y).
  by rewrite -(ler_pexpn2r n_gt0) ?qualifE ?rootC_ge0 ?rootCK.
rewrite (contraNF (@ler_trans _ _ 0 _ _)) ?rootC_ge0 //.
by rewrite (contraNF (ler_trans x_ge0)).
Qed.

Lemma ler_rootC n : (n > 0)%N -> {in Num.nneg &, {mono n.-root : x y / x <= y}}.
Proof. by move=> n_gt0 x y x_ge0 _; apply: ler_rootCl. Qed.

Lemma ltr_rootCl n : (n > 0)%N -> {in Num.nneg, {mono n.-root : x y / x < y}}.
Proof. by move=> n_gt0 x x_ge0 y; rewrite !ltr_def ler_rootCl ?eqr_rootC. Qed.

Lemma ltr_rootC n : (n > 0)%N -> {in Num.nneg &, {mono n.-root : x y / x < y}}.
Proof. by move/ler_rootC/lerW_mono_in. Qed.

Lemma exprCK n x : (0 < n)%N -> 0 <= x -> n.-root (x ^+ n) = x.
Proof.
move=> n_gt0 x_ge0; apply/eqP.
by rewrite -(eqr_expn2 n_gt0) ?rootC_ge0 ?exprn_ge0 ?rootCK.
Qed.

Lemma norm_rootC n x : `|n.-root x| = n.-root `|x|.
Proof.
have [-> | n_gt0] := posnP n; first by rewrite !root0C normr0.
apply/eqP; rewrite -(eqr_expn2 n_gt0) ?rootC_ge0 ?normr_ge0 //.
by rewrite -normrX !rootCK.
Qed.

Lemma rootCX n x k : (n > 0)%N -> 0 <= x -> n.-root (x ^+ k) = n.-root x ^+ k.
Proof.
move=> n_gt0 x_ge0; apply/eqP.
by rewrite -(eqr_expn2 n_gt0) ?(exprn_ge0, rootC_ge0) // 1?exprAC !rootCK.
Qed.

Lemma rootC1 n : (n > 0)%N -> n.-root 1 = 1.
Proof. by move/(rootCX 0)/(_ ler01). Qed.

Lemma rootCpX n x k : (k > 0)%N -> 0 <= x -> n.-root (x ^+ k) = n.-root x ^+ k.
Proof.
by case: n => [|n] k_gt0; [rewrite !root0C expr0n gtn_eqF | exact: rootCX].
Qed.

Lemma rootCV n x : (n > 0)%N -> 0 <= x -> n.-root x^-1 = (n.-root x)^-1.
Proof.
move=> n_gt0 x_ge0; apply/eqP.
by rewrite -(eqr_expn2 n_gt0) ?(invr_ge0, rootC_ge0) // !exprVn !rootCK.
Qed.

Lemma rootC_eq1 n x : (n > 0)%N -> (n.-root x == 1) = (x == 1).
Proof. by move=> n_gt0; rewrite -{1}(rootC1 n_gt0) eqr_rootC. Qed.

Lemma rootC_ge1 n x : (n > 0)%N -> (n.-root x >= 1) = (x >= 1).
Proof.
by move=> n_gt0; rewrite -{1}(rootC1 n_gt0) ler_rootCl // qualifE ler01.
Qed.

Lemma rootC_gt1 n x : (n > 0)%N -> (n.-root x > 1) = (x > 1).
Proof. by move=> n_gt0; rewrite !ltr_def rootC_eq1 ?rootC_ge1. Qed.

Lemma rootC_le1 n x : (n > 0)%N -> 0 <= x -> (n.-root x <= 1) = (x <= 1).
Proof. by move=> n_gt0 x_ge0; rewrite -{1}(rootC1 n_gt0) ler_rootCl. Qed.

Lemma rootC_lt1 n x : (n > 0)%N -> 0 <= x -> (n.-root x < 1) = (x < 1).
Proof. by move=> n_gt0 x_ge0; rewrite !ltr_neqAle rootC_eq1 ?rootC_le1. Qed.

Lemma rootCMl n x z : 0 <= x -> n.-root (x * z) = n.-root x * n.-root z.
Proof.
rewrite le0r => /predU1P[-> | x_gt0]; first by rewrite !(mul0r, rootC0).
have [| n_gt1 | ->] := ltngtP n 1; last by rewrite !root1C.
  by case: n => //; rewrite !root0C mul0r.
have [x_ge0 n_gt0] := (ltrW x_gt0, ltnW n_gt1).
have nx_gt0: 0 < n.-root x by rewrite rootC_gt0.
have Rnx: n.-root x \is Creal by rewrite ger0_real ?ltrW.
apply: eqC_semipolar; last 1 first; try apply/eqP.
- by rewrite algImMl // !(Im_rootC_ge0, mulr_ge0, rootC_ge0).
- by rewrite -(eqr_expn2 n_gt0) ?normr_ge0 // -!normrX exprMn !rootCK.
rewrite eqr_le; apply/andP; split; last first.
  rewrite rootC_Re_max ?exprMn ?rootCK ?algImMl //.
  by rewrite mulr_ge0 ?Im_rootC_ge0 ?ltrW.
rewrite -[n.-root _](mulVKf (negbT (gtr_eqF nx_gt0))) !(algReMl Rnx) //.
rewrite ler_pmul2l // rootC_Re_max ?exprMn ?exprVn ?rootCK ?mulKf ?gtr_eqF //.
by rewrite algImMl ?rpredV // mulr_ge0 ?invr_ge0 ?Im_rootC_ge0 ?ltrW.
Qed.

Lemma rootCMr n x z : 0 <= x -> n.-root (z * x) = n.-root z * n.-root x.
Proof. by move=> x_ge0; rewrite mulrC rootCMl // mulrC. Qed.

(* More properties of n.-root will be established in cyclotomic.v. *)

(* The proper form of the Arithmetic - Geometric Mean inequality. *)

Lemma lerif_rootC_AGM (I : finType) (A : pred I) (n := #|A|) E :
    {in A, forall i, 0 <= E i} ->
  n.-root (\prod_(i in A) E i) <= (\sum_(i in A) E i) / n%:R
                             ?= iff [forall i in A, forall j in A, E i == E j].
Proof.
move=> Ege0; have [n0 | n_gt0] := posnP n.
  rewrite n0 root0C invr0 mulr0; apply/lerif_refl/forall_inP=> i.
  by rewrite (card0_eq n0).
rewrite -(mono_in_lerif (ler_pexpn2r n_gt0)) ?rootCK //=; first 1 last.
- by rewrite qualifE rootC_ge0 // prodr_ge0.
- by rewrite rpred_div ?rpred_nat ?rpred_sum.
exact: lerif_AGM.
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
apply: sqrCK; rewrite -real_lerNgt // in not_gt0x; apply/Creal_ImP/ler_anti; 
by rewrite leI0x -oppr_ge0 -raddfN -defNx Im_rootC_ge0.
Qed.

Lemma normC_def x : `|x| = sqrtC (x * x^*).
Proof. by rewrite -normCK sqrCK ?normr_ge0. Qed.

Lemma norm_conjC x : `|x^*| = `|x|.
Proof. by rewrite !normC_def conjCK mulrC. Qed.

Lemma normC_rect :
  {in Creal &, forall x y, `|x + 'i * y| = sqrtC (x ^+ 2 + y ^+ 2)}.
Proof. by move=> x y Rx Ry; rewrite /= normC_def -normCK normC2_rect. Qed.

Lemma normC_Re_Im z : `|z| = sqrtC ('Re z ^+ 2 + 'Im z ^+ 2).
Proof. by rewrite normC_def -normCK normC2_Re_Im. Qed.

(* Norm sum (in)equalities. *)

Lemma normC_add_eq x y :
    `|x + y| = `|x| + `|y| ->
  {t : algC | `|t| == 1 & (x, y) = (`|x| * t, `|y| * t)}.
Proof.
move=> lin_xy; apply: sig2_eqW; pose u z := if z == 0 then 1 else z / `|z|.
have uE z: (`|u z| = 1) * (`|z| * u z = z).
  rewrite /u; have [->|nz_z] := altP eqP; first by rewrite normr0 normr1 mul0r.
  by rewrite normf_div normr_id mulrCA divff ?mulr1 ?normr_eq0.
have [->|nz_x] := eqVneq x 0; first by exists (u y); rewrite uE ?normr0 ?mul0r.
exists (u x); rewrite uE // /u (negPf nz_x); congr (_ , _).
have{lin_xy} def2xy: `|x| * `|y| *+ 2 = x * y ^* + y * x ^*.
  apply/(addrI (x * x^*))/(addIr (y * y^*)); rewrite -2!{1}normCK -sqrrD.
  by rewrite addrA -addrA -!mulrDr -mulrDl -rmorphD -normCK lin_xy.
have def_xy: x * y^* = y * x^*.
  apply/eqP; rewrite -subr_eq0 -[_ == 0](@expf_eq0 _ _ 2).
  rewrite (canRL (subrK _) (subr_sqrDB _ _)) opprK -def2xy exprMn_n exprMn.
  by rewrite mulrN mulrAC mulrA -mulrA mulrACA -!normCK mulNrn addNr.
have{def_xy def2xy} def_yx: `|y * x| = y * x^*.
  by apply: (mulIf nz2); rewrite !mulr_natr mulrC normrM def2xy def_xy.
rewrite -{1}(divfK nz_x y) invC_norm mulrCA -{}def_yx !normrM invfM.
by rewrite mulrCA divfK ?normr_eq0 // mulrAC mulrA.
Qed.

Lemma normC_sum_eq (I : finType) (P : pred I) (F : I -> algC) :
     `|\sum_(i | P i) F i| = \sum_(i | P i) `|F i| ->
   {t : algC | `|t| == 1 & forall i, P i -> F i = `|F i| * t}.
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
  apply/eqP; rewrite eqr_le ler_norm_add -(ler_add2r z) -addrA -norm_sumF addrA.
  by rewrite (ler_trans (ler_norm_add _ _)) // ler_add2l ler_norm_sum.
by case/normC_add_eq=> k _ [/(canLR (mulKf nzFi)) <-]; rewrite -(mulrC (F i)).
Qed.

Lemma normC_sum_eq1 (I : finType) (P : pred I) (F : I -> algC) :
    `|\sum_(i | P i) F i| = (\sum_(i | P i) `|F i|) ->
     (forall i, P i -> `|F i| = 1) ->
   {t : algC | `|t| == 1 & forall i, P i -> F i = t}.
Proof.
case/normC_sum_eq=> t t1 defF normF.
by exists t => // i Pi; rewrite defF // normF // mul1r.
Qed.

Lemma normC_sum_upper (I : finType) (P : pred I) (F G : I -> algC) :
     (forall i, P i -> `|F i| <= G i) ->
     \sum_(i | P i) F i = \sum_(i | P i) G i ->
   forall i, P i -> F i = G i.
Proof.
set sumF := \sum_(i | _) _; set sumG := \sum_(i | _) _ => leFG eq_sumFG.
have posG i: P i -> 0 <= G i by move/leFG; apply: ler_trans; exact: normr_ge0.
have norm_sumG: `|sumG| = sumG by rewrite ger0_norm ?sumr_ge0.
have norm_sumF: `|sumF| = \sum_(i | P i) `|F i|.
  apply/eqP; rewrite eqr_le ler_norm_sum eq_sumFG norm_sumG -subr_ge0 -sumrB.
  by rewrite sumr_ge0 // => i Pi; rewrite subr_ge0 ?leFG.
have [t _ defF] := normC_sum_eq norm_sumF.
have [/(psumr_eq0P posG) G0 i Pi | nz_sumG] := eqVneq sumG 0.
  by apply/eqP; rewrite G0 // -normr_eq0 eqr_le normr_ge0 -(G0 i Pi) leFG.
have t1: t = 1.
  apply: (mulfI nz_sumG); rewrite mulr1 -{1}norm_sumG -eq_sumFG norm_sumF.
  by rewrite mulr_suml -(eq_bigr _ defF).
have /psumr_eq0P eqFG i: P i -> 0 <= G i - F i.
  by move=> Pi; rewrite subr_ge0 defF // t1 mulr1 leFG.
move=> i /eqFG/(canRL (subrK _))->; rewrite ?add0r //.
by rewrite sumrB -/sumF eq_sumFG subrr.
Qed.

Lemma normC_sub_eq x y :
  `|x - y| = `|x| - `|y| -> {t | `|t| == 1 & (x, y) = (`|x| * t, `|y| * t)}.
Proof.
rewrite -{-1}(subrK y x) => /(canLR (subrK _))/esym-Dx; rewrite Dx.
by have [t ? [Dxy Dy]] := normC_add_eq Dx; exists t; rewrite // mulrDl -Dxy -Dy.
Qed.

(* Integer subset. *)

(* Not relying on the undocumented interval library, for now. *)
Lemma floorC_itv x : x \is Creal -> (floorC x)%:~R <= x < (floorC x + 1)%:~R.
Proof. by rewrite /floorC => Rx; case: (floorC_subproof x) => //= m; apply. Qed.

Lemma floorC_def x m : m%:~R <= x < (m + 1)%:~R -> floorC x = m.
Proof.
case/andP=> lemx ltxm1; apply/eqP; rewrite eqr_le -!ltz_addr1.
have /floorC_itv/andP[lefx ltxf1]: x \is Creal.
  by rewrite -[x](subrK m%:~R) rpredD ?realz ?ler_sub_real.
by rewrite -!(ltr_int [numFieldType of algC]) 2?(@ler_lt_trans _ x).
Qed.

Lemma intCK : cancel intr floorC.
Proof.
by move=> m; apply: floorC_def; rewrite ler_int ltr_int ltz_addr1 lerr.
Qed.

Lemma floorCK : {in Cint, cancel floorC intr}. Proof. by move=> z /eqP. Qed.

Lemma floorC0 : floorC 0 = 0. Proof. exact: (intCK 0). Qed.
Lemma floorC1 : floorC 1 = 1. Proof. exact: (intCK 1). Qed.
Hint Resolve floorC0 floorC1.

Lemma floorCpK (p : {poly algC}) :
  p \is a polyOver Cint -> map_poly intr (map_poly floorC p) = p.
Proof.
move/(all_nthP 0)=> Zp; apply/polyP=> i.
rewrite coef_map coef_map_id0 //= -[p]coefK coef_poly.
by case: ifP => [/Zp/floorCK // | _]; rewrite floorC0.
Qed.

Lemma floorCpP (p : {poly algC}) :
  p \is a polyOver Cint -> {q | p = map_poly intr q}.
Proof. by exists (map_poly floorC p); rewrite floorCpK. Qed.

Lemma Cint_int m : m%:~R \in Cint.
Proof. by rewrite unfold_in intCK. Qed.

Lemma CintP x : reflect (exists m, x = m%:~R) (x \in Cint).
Proof.
by apply: (iffP idP) => [/eqP<-|[m ->]]; [exists (floorC x) | apply: Cint_int].
Qed.

Lemma floorCD : {in Cint & Creal, {morph floorC : x y / x + y}}.
Proof.
move=> _ y /CintP[m ->] Ry; apply: floorC_def.
by rewrite -addrA 2!rmorphD /= intCK ler_add2l ltr_add2l floorC_itv.
Qed.

Lemma floorCN : {in Cint, {morph floorC : x / - x}}.
Proof. by move=> _ /CintP[m ->]; rewrite -rmorphN !intCK. Qed.

Lemma floorCM : {in Cint &, {morph floorC : x y / x * y}}.
Proof. by move=> _ _ /CintP[m1 ->] /CintP[m2 ->]; rewrite -rmorphM !intCK. Qed.

Lemma floorCX n : {in Cint, {morph floorC : x / x ^+ n}}.
Proof. by move=> _ /CintP[m ->]; rewrite -rmorphX !intCK. Qed.

Lemma rpred_Cint S (ringS : subringPred S) (kS : keyed_pred ringS) x :
  x \in Cint -> x \in kS.
Proof. by case/CintP=> m ->; apply: rpred_int. Qed.

Lemma Cint0 : 0 \in Cint. Proof. exact: (Cint_int 0). Qed.
Lemma Cint1 : 1 \in Cint. Proof. exact: (Cint_int 1). Qed.
Hint Resolve Cint0 Cint1.

Fact Cint_key : pred_key Cint. Proof. by []. Qed.
Fact Cint_subring : subring_closed Cint.
Proof.
by split=> // _ _ /CintP[m ->] /CintP[p ->];
    rewrite -(rmorphB, rmorphM) Cint_int.
Qed.
Canonical Cint_keyed := KeyedPred Cint_key.
Canonical Cint_opprPred := OpprPred Cint_subring.
Canonical Cint_addrPred := AddrPred Cint_subring.
Canonical Cint_mulrPred := MulrPred Cint_subring.
Canonical Cint_zmodPred := ZmodPred Cint_subring.
Canonical Cint_semiringPred := SemiringPred Cint_subring.
Canonical Cint_smulrPred := SmulrPred Cint_subring.
Canonical Cint_subringPred := SubringPred Cint_subring.

Lemma Creal_Cint : {subset Cint <= Creal}.
Proof. by move=> _ /CintP[m ->]; apply: realz. Qed.

Lemma conj_Cint x : x \in Cint -> x^* = x.
Proof. by move/Creal_Cint/conj_Creal. Qed.

Lemma Cint_normK x : x \in Cint -> `|x| ^+ 2 = x ^+ 2.
Proof. by move/Creal_Cint/real_normK. Qed.

Lemma CintEsign x : x \in Cint -> x = (-1) ^+ (x < 0)%C * `|x|.
Proof. by move/Creal_Cint/realEsign. Qed.

(* Natural integer subset. *)

Lemma truncC_itv x : 0 <= x -> (truncC x)%:R <= x < (truncC x).+1%:R.
Proof.
move=> x_ge0; have /andP[lemx ltxm1] := floorC_itv (ger0_real x_ge0).
rewrite /truncC x_ge0 -addn1 !pmulrn PoszD gez0_abs ?lemx //.
by rewrite -ltz_addr1 -(ltr_int [numFieldType of algC]) (ler_lt_trans x_ge0).
Qed.

Lemma truncC_def x n : n%:R <= x < n.+1%:R -> truncC x = n.
Proof.
move=> ivt_n_x; have /andP[lenx _] := ivt_n_x.
by rewrite /truncC (ler_trans (ler0n _ n)) // (@floorC_def _ n) // addrC -intS.
Qed.

Lemma natCK n : truncC n%:R = n.
Proof. by apply: truncC_def; rewrite lerr ltr_nat /=. Qed.

Lemma CnatP x : reflect (exists n, x = n%:R) (x \in Cnat).
Proof.
by apply: (iffP eqP) => [<- | [n ->]]; [exists (truncC x) | rewrite natCK].
Qed.

Lemma truncCK : {in Cnat, cancel truncC (GRing.natmul 1)}.
Proof. by move=> x /eqP. Qed.

Lemma truncC_gt0 x : (0 < truncC x)%N = (1 <= x).
Proof.
apply/idP/idP=> [m_gt0 | x_ge1].
  have /truncC_itv/andP[lemx _]: 0 <= x.
    by move: m_gt0; rewrite /truncC; case: ifP.
  by apply: ler_trans lemx; rewrite ler1n.
have /truncC_itv/andP[_ ltxm1]:= ler_trans ler01 x_ge1.
by rewrite -ltnS -ltC_nat (ler_lt_trans x_ge1).
Qed.

Lemma truncC0Pn x : reflect (truncC x = 0%N) (~~ (1 <= x)).
Proof. by rewrite -truncC_gt0 -eqn0Ngt; apply: eqP. Qed.

Lemma truncC0 : truncC 0 = 0%N. Proof. exact: (natCK 0). Qed.
Lemma truncC1 : truncC 1 = 1%N. Proof. exact: (natCK 1). Qed.

Lemma truncCD :
  {in Cnat & Num.nneg, {morph truncC : x y / x + y >-> (x + y)%N}}.
Proof.
move=> _ y /CnatP[n ->] y_ge0; apply: truncC_def.
by rewrite -addnS !natrD !natCK ler_add2l ltr_add2l truncC_itv.
Qed.

Lemma truncCM : {in Cnat &, {morph truncC : x y / x * y >-> (x * y)%N}}.
Proof. by move=> _ _ /CnatP[n1 ->] /CnatP[n2 ->]; rewrite -natrM !natCK. Qed.

Lemma truncCX n : {in Cnat, {morph truncC : x / x ^+ n >-> (x ^ n)%N}}.
Proof. by move=> _ /CnatP[n1 ->]; rewrite -natrX !natCK. Qed.

Lemma rpred_Cnat S (ringS : semiringPred S) (kS : keyed_pred ringS) x :
  x \in Cnat -> x \in kS.
Proof. by case/CnatP=> n ->; apply: rpred_nat. Qed.

Lemma Cnat_nat n : n%:R \in Cnat. Proof. by apply/CnatP; exists n. Qed.
Lemma Cnat0 : 0 \in Cnat. Proof. exact: (Cnat_nat 0). Qed.
Lemma Cnat1 : 1 \in Cnat. Proof. exact: (Cnat_nat 1). Qed.
Hint Resolve Cnat_nat Cnat0 Cnat1.

Fact Cnat_key : pred_key Cnat. Proof. by []. Qed.
Fact Cnat_semiring : semiring_closed Cnat.
Proof.
by do 2![split] => //= _ _ /CnatP[n ->] /CnatP[m ->]; rewrite -(natrD, natrM).
Qed.
Canonical Cnat_keyed := KeyedPred Cnat_key.
Canonical Cnat_addrPred := AddrPred Cnat_semiring.
Canonical Cnat_mulrPred := MulrPred Cnat_semiring.
Canonical Cnat_semiringPred := SemiringPred Cnat_semiring.

Lemma Cnat_ge0 x : x \in Cnat -> 0 <= x.
Proof. by case/CnatP=> n ->; apply: ler0n. Qed.

Lemma Cnat_gt0 x : x \in Cnat -> (0 < x) = (x != 0).
Proof. by case/CnatP=> n ->; rewrite pnatr_eq0 ltr0n lt0n. Qed.

Lemma conj_Cnat x : x \in Cnat -> x^* = x.
Proof. by case/CnatP=> n ->; apply: rmorph_nat. Qed.

Lemma norm_Cnat x : x \in Cnat -> `|x| = x.
Proof. by move/Cnat_ge0/ger0_norm. Qed.

Lemma Creal_Cnat : {subset Cnat <= Creal}.
Proof. by move=> z /conj_Cnat/CrealP. Qed.

Lemma Cnat_sum_eq1 (I : finType) (P : pred I) (F : I -> algC) :
     (forall i, P i -> F i \in Cnat) -> \sum_(i | P i) F i = 1 ->
   {i : I | [/\ P i, F i = 1 & forall j, j != i -> P j -> F j = 0]}.
Proof.
move=> natF sumF1; pose nF i := truncC (F i).
have{natF} defF i: P i -> F i = (nF i)%:R by move/natF/eqP.
have{sumF1} /eqP sumF1: (\sum_(i | P i) nF i == 1)%N.
  by rewrite -eqC_nat natr_sum -(eq_bigr _ defF) sumF1.
have [i Pi nZfi]: {i : I | P i & nF i != 0%N}.
  by apply/sig2W/exists_inP; rewrite -negb_forall_in -sum_nat_eq0 sumF1.
have F'ge0 := (leq0n _, etrans (eq_sym _ _) (sum_nat_eq0 (predD1 P i) nF)).
rewrite -lt0n in nZfi; have [_] := (leqif_add (leqif_eq nZfi) (F'ge0 _)).
rewrite /= big_andbC -bigD1 // sumF1 => /esym/andP/=[/eqP Fi1 /forall_inP Fi'0].
exists i; split=> // [|j neq_ji Pj]; first by rewrite defF // -Fi1.
by rewrite defF // (eqP (Fi'0 j _)) // neq_ji.
Qed.

Lemma Cnat_mul_eq1 x y :
  x \in Cnat -> y \in Cnat -> (x * y == 1) = (x == 1) && (y == 1).
Proof. by do 2!move/truncCK <-; rewrite -natrM !pnatr_eq1 muln_eq1. Qed.

Lemma Cnat_prod_eq1 (I : finType) (P : pred I) (F : I -> algC) :
    (forall i, P i -> F i \in Cnat) -> \prod_(i | P i) F i = 1 ->
  forall i, P i -> F i = 1.
Proof.
move=> natF prodF1; apply/eqfun_inP; rewrite -big_andE.
move: prodF1; elim/(big_load (fun x => x \in Cnat)): _.
elim/big_rec2: _ => // i all1x x /natF N_Fi [Nx x1all1].
by split=> [|/eqP]; rewrite ?rpredM ?Cnat_mul_eq1 // => /andP[-> /eqP].
Qed.

(* Relating Cint and Cnat. *)

Lemma Cint_Cnat : {subset Cnat <= Cint}.
Proof. by move=> _ /CnatP[n ->]; rewrite pmulrn Cint_int. Qed.

Lemma CintE x : (x \in Cint) = (x \in Cnat) || (- x \in Cnat).
Proof.
apply/idP/idP=> [/CintP[[n | n] ->] | ]; first by rewrite Cnat_nat.
  by rewrite NegzE opprK Cnat_nat orbT.
by case/pred2P=> [<- | /(canLR (@opprK _)) <-]; rewrite ?rpredN rpred_nat.
Qed.

Lemma Cnat_norm_Cint x : x \in Cint -> `|x| \in Cnat.
Proof.
case/CintP=> [m ->]; rewrite [m]intEsign rmorphM rmorph_sign.
by rewrite normrM normr_sign mul1r normr_nat rpred_nat.
Qed.

Lemma CnatEint x : (x \in Cnat) = (x \in Cint) && (0 <= x).
Proof.
apply/idP/andP=> [Nx | [Zx x_ge0]]; first by rewrite Cint_Cnat ?Cnat_ge0.
by rewrite -(ger0_norm x_ge0) Cnat_norm_Cint.
Qed.

Lemma CintEge0 x : 0 <= x -> (x \in Cint) = (x \in Cnat).
Proof. by rewrite CnatEint andbC => ->. Qed.

Lemma Cnat_exp_even x n : ~~ odd n -> x \in Cint -> x ^+ n \in Cnat.
Proof.
rewrite -dvdn2 => /dvdnP[m ->] Zx; rewrite mulnC exprM -Cint_normK ?rpredX //.
exact: Cnat_norm_Cint.
Qed.

Lemma norm_Cint_ge1 x : x \in Cint -> x != 0 -> 1 <= `|x|.
Proof.
rewrite -normr_eq0 => /Cnat_norm_Cint/CnatP[n ->].
by rewrite pnatr_eq0 ler1n lt0n.
Qed.

Lemma sqr_Cint_ge1 x : x \in Cint -> x != 0 -> 1 <= x ^+ 2.
Proof.
by move=> Zx nz_x; rewrite -Cint_normK // expr_ge1 ?normr_ge0 ?norm_Cint_ge1.
Qed.

Lemma Cint_ler_sqr x : x \in Cint -> x <= x ^+ 2.
Proof.
move=> Zx; have [-> | nz_x] := eqVneq x 0; first by rewrite expr0n.
apply: ler_trans (_ : `|x| <= _); first by rewrite real_ler_norm ?Creal_Cint.
by rewrite -Cint_normK // ler_eexpr // norm_Cint_ge1.
Qed.

(* Integer divisibility. *)

Lemma dvdCP x y : reflect (exists2 z, z \in Cint & y = z * x) (x %| y)%C.
Proof.
rewrite unfold_in; have [-> | nz_x] := altP eqP.
  by apply: (iffP eqP) => [-> | [z _ ->]]; first exists 0; rewrite ?mulr0.
apply: (iffP idP) => [Zyx | [z Zz ->]]; last by rewrite mulfK.
by exists (y / x); rewrite ?divfK.
Qed.

Lemma dvdCP_nat x y : 0 <= x -> 0 <= y -> (x %| y)%C -> {n | y = n%:R * x}.
Proof.
move=> x_ge0 y_ge0 x_dv_y; apply: sig_eqW.
case/dvdCP: x_dv_y => z Zz -> in y_ge0 *; move: x_ge0 y_ge0 Zz.
rewrite ler_eqVlt => /predU1P[<- | ]; first by exists 22; rewrite !mulr0.
by move=> /pmulr_lge0-> /CintEge0-> /CnatP[n ->]; exists n.
Qed.

Lemma dvdC0 x : (x %| 0)%C.
Proof. by apply/dvdCP; exists 0; rewrite ?mul0r. Qed.

Lemma dvd0C x : (0 %| x)%C = (x == 0).
Proof. by rewrite unfold_in eqxx. Qed.

Lemma dvdC_mull x y z : y \in Cint -> (x %| z)%C -> (x %| y * z)%C.
Proof.
move=> Zy /dvdCP[m Zm ->]; apply/dvdCP.
by exists (y * m); rewrite ?mulrA ?rpredM.
Qed.

Lemma dvdC_mulr x y z : y \in Cint -> (x %| z)%C -> (x %| z * y)%C.
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
Hint Resolve dvdC_refl.

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
rewrite unfold_in CintEge0 ?divr_ge0 ?invr_ge0 ?ler0n // !pnatr_eq0.
have [-> | nz_p] := altP eqP; first by rewrite dvd0n.
apply/CnatP/dvdnP=> [[q def_q] | [q ->]]; exists q.
  by apply/eqP; rewrite -eqC_nat natrM -def_q divfK ?pnatr_eq0. 
by rewrite [num in num / _]natrM mulfK ?pnatr_eq0.
Qed.

Lemma dvdC_int (p : nat) x : x \in Cint -> (p %| x)%C = (p %| `|floorC x|)%N.
Proof.
move=> Zx; rewrite -{1}(floorCK Zx) {1}[floorC x]intEsign.
by rewrite rmorphMsign rpredMsign dvdC_nat.
Qed.

(* Elementary modular arithmetic. *)

Lemma eqCmod_refl e x : (x == x %[mod e])%C.
Proof. by rewrite /eqCmod subrr rpred0. Qed.

Lemma eqCmodm0 e : (e == 0 %[mod e])%C. Proof. by rewrite /eqCmod subr0. Qed.
Hint Resolve eqCmod_refl eqCmodm0.

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
Proof. rewrite -(eqCmodDl e x2 y1) -(eqCmodDr e y1); exact: eqCmod_trans. Qed.

Lemma eqCmod_nat (e m n : nat) : (m == n %[mod e])%C = (m == n %[mod e]).
Proof.
without loss lenm: m n / (n <= m)%N.
  by move=> IH; case/orP: (leq_total m n) => /IH //; rewrite eqCmod_sym eq_sym.
by rewrite /eqCmod -natrB // dvdC_nat eqn_mod_dvd.
Qed.

Lemma eqCmod0_nat (e m : nat) : (m == 0 %[mod e])%C = (e %| m)%N.
Proof. by rewrite eqCmod0 dvdC_nat. Qed.

Lemma eqCmodMr e :
  {in Cint, forall z x y, x == y %[mod e] -> x * z == y * z %[mod e]}%C.
Proof. by move=> z Zz x y; rewrite /eqCmod -mulrBl => /dvdC_mulr->. Qed.

Lemma eqCmodMl e :
  {in Cint, forall z x y, x == y %[mod e] -> z * x == z * y %[mod e]}%C.
Proof. by move=> z Zz x y Exy; rewrite !(mulrC z) eqCmodMr. Qed.

Lemma eqCmodMl0 e : {in Cint, forall x, x * e == 0 %[mod e]}%C.
Proof. by move=> x Zx; rewrite -(mulr0 x) eqCmodMl. Qed.

Lemma eqCmodMr0 e : {in Cint, forall x, e * x == 0 %[mod e]}%C.
Proof. by move=> x Zx; rewrite /= mulrC eqCmodMl0. Qed.

Lemma eqCmod_addl_mul e : {in Cint, forall x y, x * e + y == y %[mod e]}%C.
Proof. by move=> x Zx y; rewrite -{2}[y]add0r eqCmodDr eqCmodMl0. Qed.

Lemma eqCmodM e : {in Cint & Cint, forall x1 y2 x2 y1,
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
Hint Resolve Crat0 Crat1.

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

Lemma rpred_Crat S (ringS : divringPred S) (kS : keyed_pred ringS) :
  {subset Crat <= kS}.
Proof. by move=> _ /CratP[a ->]; apply: rpred_rat. Qed.

Lemma conj_Crat z : z \in Crat -> z^* = z.
Proof. by move/getCratK <-; rewrite fmorph_div !rmorph_int. Qed.

Lemma Creal_Crat : {subset Crat <= Creal}.
Proof. by move=> x /conj_Crat/CrealP. Qed.

Lemma Cint_rat a : (QtoC a \in Cint) = (a \in Qint).
Proof.
apply/idP/idP=> [Za | /numqK <-]; last by rewrite rmorph_int Cint_int.
apply/QintP; exists (floorC (QtoC a)); apply: (can_inj ratCK).
by rewrite rmorph_int floorCK.
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

Lemma aut_Cnat nu : {in Cnat, nu =1 id}.
Proof. by move=> _ /CnatP[n ->]; apply: rmorph_nat. Qed.

Lemma aut_Cint nu : {in Cint, nu =1 id}.
Proof. by move=> _ /CintP[m ->]; apply: rmorph_int. Qed.

Lemma aut_Crat nu : {in Crat, nu =1 id}.
Proof. by move=> _ /CratP[a ->]; apply: fmorph_rat. Qed.

Lemma Cnat_aut nu x : (nu x \in Cnat) = (x \in Cnat).
Proof.
by do [apply/idP/idP=> Nx; have:= aut_Cnat nu Nx] => [/fmorph_inj <- | ->].
Qed.

Lemma Cint_aut nu x : (nu x \in Cint) = (x \in Cint).
Proof. by rewrite !CintE -rmorphN !Cnat_aut. Qed.

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

Section AutLmodC.

Variables (U V : lmodType algC) (f : {additive U -> V}).

Lemma raddfZ_Cnat a u : a \in Cnat -> f (a *: u) = a *: f u. 
Proof. by case/CnatP=> n ->; exact: raddfZnat. Qed.

Lemma raddfZ_Cint a u : a \in Cint -> f (a *: u) = a *: f u. 
Proof. by case/CintP=> m ->; rewrite !scaler_int raddfMz. Qed.

End AutLmodC.

Section PredCmod.

Variable V : lmodType algC.

Lemma rpredZ_Cnat S (addS : @addrPred V S) (kS : keyed_pred addS) :
  {in Cnat & kS, forall z u, z *: u \in kS}.
Proof. by move=> _ u /CnatP[n ->]; apply: rpredZnat. Qed.

Lemma rpredZ_Cint S (subS : @zmodPred V S) (kS : keyed_pred subS) :
  {in Cint & kS, forall z u, z *: u \in kS}.
Proof. by move=> _ u /CintP[m ->]; apply: rpredZint. Qed.

End PredCmod.

End AlgebraicsTheory.
Hint Resolve Creal0 Creal1 Cnat_nat Cnat0 Cnat1 Cint0 Cint1 floorC0 Crat0 Crat1.
Hint Resolve dvdC0 dvdC_refl eqCmod_refl eqCmodm0.
