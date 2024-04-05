(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq choice.
From mathcomp Require Import div fintype path bigop finset prime order ssralg.
From mathcomp Require Import poly polydiv mxpoly generic_quotient countalg.
From mathcomp Require Import ssrnum closed_field ssrint archimedean rat intdiv.
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

HB.factory Record isComplex L of GRing.ClosedField L  := {
  conj :  {rmorphism L -> L};
  conjK : involutive conj;
  conj_nt : ~ conj =1 id
}.

HB.builders Context L of isComplex L.

Lemma nz2: 2 != 0 :> L.
Proof.
  apply/eqP=> char2; apply: conj_nt => e; apply/eqP/idPn=> eJ.
  have opp_id x: - x = x :> L.
    by apply/esym/eqP; rewrite -addr_eq0 -mulr2n -mulr_natl char2 mul0r.
  have{} char2: 2%N \in [char L] by apply/eqP.
  without loss{eJ} eJ: e / conj e = e + 1.
    move/(_ (e / (e + conj e))); apply.
    rewrite fmorph_div rmorphD /= conjK -{1}[conj e](addNKr e) mulrDl.
    by rewrite opp_id (addrC e) divff // addr_eq0 opp_id.
  pose a := e * conj e; have aJ: conj a = a by rewrite rmorphM /= conjK mulrC.
  have [w Dw] := @solve_monicpoly _ 2%N (nth 0 [:: e * a; - 1]) isT.
  have{} Dw: w ^+ 2 + w = e * a.
    by rewrite Dw !big_ord_recl big_ord0 /= mulr1 mulN1r addr0 subrK.
  pose b := w + conj w; have bJ: conj b = b by rewrite rmorphD /= conjK addrC.
  have Db2: b ^+ 2 + b = a.
    rewrite -Frobenius_autE // rmorphD addrACA Dw /= Frobenius_autE -rmorphXn.
    by rewrite -rmorphD Dw rmorphM /= aJ eJ -mulrDl -{1}[e]opp_id addKr mul1r.
  have /eqP[] := oner_eq0 L; apply: (addrI b); rewrite addr0 -{2}bJ.
  have: (b + e) * (b + conj e) == 0.
    (* FIX ME : had to add pattern selection *)
    rewrite mulrDl 2![_ * (b + _)]mulrDr -/a.
    rewrite addrA addr_eq0 opp_id (mulrC e) -addrA.
    by rewrite -mulrDr eJ addrAC -{2}[e]opp_id subrr add0r mulr1 Db2.
  rewrite mulf_eq0 !addr_eq0 !opp_id => /pred2P[] -> //.
  by rewrite {2}eJ rmorphD rmorph1.
Qed.

Lemma mul2I: injective (fun z : L => z *+ 2).
Proof.
  have nz2 := nz2.
  by move=> x y; rewrite /= -mulr_natl -(mulr_natl y) => /mulfI->.
Qed.

Definition sqrt x : L :=
  sval (sig_eqW (@solve_monicpoly _ 2%N (nth 0 [:: x]) isT)).

Lemma sqrtK x: sqrt x ^+ 2 = x.
Proof.
  rewrite /sqrt; case: sig_eqW => /= y ->.
  by rewrite !big_ord_recl big_ord0 /= mulr1 mul0r !addr0.
Qed.

Lemma sqrtE x y: y ^+ 2 = x -> {b : bool | y = (-1) ^+ b * sqrt x}.
Proof.
  move=> Dx; exists (y != sqrt x); apply/eqP; rewrite mulr_sign if_neg.
  by case: ifPn => //; apply/implyP; rewrite implyNb -eqf_sqr Dx sqrtK.
Qed.

Definition i := sqrt (- 1).

Lemma sqrMi x: (i * x) ^+ 2 = - x ^+ 2.
Proof. by rewrite exprMn sqrtK mulN1r. Qed.

Lemma iJ : conj i = - i.
Proof.
  have nz2 := nz2.
  have /sqrtE[b]: conj i ^+ 2 = - 1 by rewrite -rmorphXn /= sqrtK rmorphN1.
  rewrite mulr_sign -/i; case: b => // Ri.
  case: conj_nt => z; wlog zJ: z / conj z = - z.
    move/(_ (z - conj z)); rewrite !rmorphB conjK opprB => zJ.
    by apply/mul2I/(canRL (subrK _)); rewrite -addrA zJ // addrC subrK.
  have [-> | nz_z] := eqVneq z 0; first exact: rmorph0.
  have [u Ru [v Rv Dz]]:
    exists2 u, conj u = u & exists2 v, conj v = v & (u + z * v) ^+ 2 = z.
  - pose y := sqrt z; exists ((y + conj y) / 2).
      by rewrite fmorph_div rmorphD /= conjK addrC rmorph_nat.
    exists ((y - conj y) / (z *+ 2)).
      rewrite fmorph_div rmorphMn /= zJ mulNrn invrN mulrN -mulNr rmorphB opprB.
      by rewrite conjK.
    rewrite -(mulr_natl z) invfM (mulrC z) !mulrA divfK // -mulrDl addrACA.
    (* FIX ME : had to add the explicit pattern *)
    by rewrite subrr addr0 -mulr2n -[_ *+ 2]mulr_natr mulfK ?Neq0 ?sqrtK.
  suff u0: u = 0 by rewrite -Dz u0 add0r rmorphXn rmorphM /= Rv zJ mulNr sqrrN.
  suff [b Du]: exists b : bool, u = (-1) ^+ b * i * z * v.
    apply: mul2I; rewrite mul0rn mulr2n -{2}Ru.
    by rewrite Du !rmorphM /= rmorph_sign Rv Ri zJ !mulrN mulNr subrr.
  have/eqP:= zJ; rewrite -addr_eq0 -{1 2}Dz rmorphXn rmorphD rmorphM /= Ru Rv zJ.
  rewrite mulNr sqrrB sqrrD addrACA (addrACA (u ^+ 2)) addNr addr0 -!mulr2n.
  rewrite -mulrnDl -(mul0rn _ 2) (inj_eq mul2I) /= -[rhs in _ + rhs]opprK.
  rewrite -sqrMi subr_eq0 eqf_sqr -mulNr !mulrA.
  by case/pred2P=> ->; [exists false | exists true]; rewrite mulr_sign.
Qed.

Definition norm x := sqrt x * conj (sqrt x).

Lemma normK x : norm x ^+ 2 = x * conj x.
Proof. by rewrite exprMn -rmorphXn sqrtK. Qed.

Lemma normE x y : y ^+ 2 = x -> norm x = y * conj y.
Proof.
  rewrite /norm => /sqrtE[b /(canLR (signrMK b)) <-].
  by rewrite !rmorphM /= rmorph_sign mulrACA -mulrA signrMK.
Qed.

Lemma norm_eq0 x : norm x = 0 -> x = 0.
Proof.
  by move/eqP; rewrite mulf_eq0 fmorph_eq0 -mulf_eq0 -expr2 sqrtK => /eqP.
Qed.

Lemma normM x y : norm (x * y) = norm x * norm y.
Proof.
  by rewrite mulrACA -rmorphM; apply: normE; rewrite exprMn !sqrtK.
Qed.

Lemma normN x : norm (- x) = norm x.
Proof.
  by rewrite -mulN1r normM {1}/norm iJ mulrN -expr2 sqrtK opprK mul1r.
Qed.

Definition le x y := norm (y - x) == y - x.
Definition lt x y := (y != x) && le x y.

Lemma posE x: le 0 x = (norm x == x).
Proof. by rewrite /le subr0. Qed.

Lemma leB x y: le x y = le 0 (y - x).
Proof. by rewrite posE. Qed.

Lemma posP x : reflect (exists y, x = y * conj y) (le 0 x).
Proof.
  rewrite posE; apply: (iffP eqP) => [Dx | [y {x}->]]; first by exists (sqrt x).
  by rewrite (normE (normK y)) rmorphM /= conjK (mulrC (conj _)) -expr2 normK.
Qed.

Lemma posJ x : le 0 x -> conj x = x.
Proof.
  by case/posP=> {x}u ->; rewrite rmorphM /= conjK mulrC.
Qed.

Lemma pos_linear x y : le 0 x -> le 0 y -> le x y || le y x.
Proof.
  move=> pos_x pos_y; rewrite leB -opprB orbC leB !posE normN -eqf_sqr.
  by rewrite normK rmorphB !posJ ?subrr.
Qed.

Lemma sposDl x y : lt 0 x -> le 0 y -> lt 0 (x + y).
Proof.
  have sqrtJ z : le 0 z -> conj (sqrt z) = sqrt z.
    rewrite posE -{2}[z]sqrtK -subr_eq0 -mulrBr mulf_eq0 subr_eq0.
    by case/pred2P=> ->; rewrite ?rmorph0.
  case/andP=> nz_x /sqrtJ uJ /sqrtJ vJ.
  set u := sqrt x in uJ; set v := sqrt y in vJ; pose w := u + i * v.
  have ->: x + y = w * conj w.
    rewrite rmorphD rmorphM /= iJ uJ vJ mulNr mulrC -subr_sqr sqrMi opprK.
    by rewrite !sqrtK.
  apply/andP; split; last by apply/posP; exists w.
  rewrite -normK expf_eq0 //=; apply: contraNneq nz_x => /norm_eq0 w0.
  rewrite -[x]sqrtK expf_eq0 /= -/u -(inj_eq mul2I) !mulr2n -{2}(rmorph0 conj).
  by rewrite -w0 rmorphD rmorphM /= iJ uJ vJ mulNr addrACA subrr addr0.
Qed.

Lemma sposD x y : lt 0 x -> lt 0 y -> lt 0 (x + y).
Proof.
  by move=> x_gt0 /andP[_]; apply: sposDl.
Qed.

Lemma normD x y : le (norm (x + y)) (norm x + norm y).
Proof.
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
    by rewrite rmorphD !rmorphM /= !conjK addrC mulrC (mulrC y).
  rewrite -mulr2n -mulr_natr exprMn normK -natrX mulr_natr sqrrD mulrACA.
  rewrite -rmorphM (mulrC y x) addrAC leB mulrnA mulr2n opprD addrACA.
  rewrite subrr addr0 {2}(mulrC x) rmorphM mulrACA -opprB addrAC -sqrrB -sqrMi.
  apply/posP; exists (i * (x * conj y - y * conj x)); congr (_ * _).
  rewrite !(rmorphM, rmorphB) iJ !conjK mulNr -mulrN opprB.
  by rewrite (mulrC x) (mulrC y).
Qed.

HB.instance Definition _ :=
  Num.IntegralDomain_isNumRing.Build L normD sposD norm_eq0
         pos_linear normM (fun x y => erefl (le x y))
                          (fun x y => erefl (lt x y)).

HB.instance Definition _ :=
  Num.NumField_isImaginary.Build L (sqrtK _) normK.

HB.end.

Module Algebraics.

Module Type Specification.

Parameter type : Type.

Parameter conjMixin : Num.ClosedField type.

Parameter isCountable : Countable type.

(* Note that this cannot be included in conjMixin since a few proofs
   depend from nat_num being definitionally equal to (trunc x)%:R == x *)
Axiom archimedean : Num.archimedean_axiom (Num.ClosedField.Pack conjMixin).

Axiom algebraic : integralRange (@ratr (Num.ClosedField.Pack conjMixin)).

End Specification.

Module Implementation : Specification.

Definition L := tag Fundamental_Theorem_of_Algebraics.

Definition conjL : {rmorphism L -> L} :=
  s2val (tagged Fundamental_Theorem_of_Algebraics).

Fact conjL_K : involutive conjL.
Proof. exact: s2valP (tagged Fundamental_Theorem_of_Algebraics). Qed.

Fact conjL_nt : ~ conjL =1 id.
Proof. exact: s2valP' (tagged Fundamental_Theorem_of_Algebraics). Qed.

Definition L' : Type := eta L.
HB.instance Definition _ := GRing.ClosedField.on L'.
HB.instance Definition _ := isComplex.Build L' conjL_K conjL_nt.

Notation cfType := (L' : closedFieldType).

Definition QtoL : {rmorphism _ -> _} := @ratr cfType.

Notation pQtoL := (map_poly QtoL).

Definition rootQtoL p_j :=
  if p_j.1 == 0 then 0 else
  (sval (closed_field_poly_normal (pQtoL p_j.1)))`_p_j.2.

Definition eq_root p_j q_k := rootQtoL p_j == rootQtoL q_k.

Fact eq_root_is_equiv : equiv_class_of eq_root.
Proof. by rewrite /eq_root; split=> [ ? | ? ? | ? ? ? ] // /eqP->. Qed.
Canonical eq_root_equiv := EquivRelPack eq_root_is_equiv.

Definition type : Type := {eq_quot eq_root}%qT.

HB.instance Definition _ : EqQuotient _ eq_root type := EqQuotient.on type.
HB.instance Definition _ := Choice.on type.
HB.instance Definition _ := isCountable.Build type
  (pcan_pickleK (can_pcan reprK)).

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

HB.instance Definition _ := GRing.isZmodule.Build type addA addC add0 addN.

Fact CtoL_is_additive : additive CtoL.
Proof. by move=> u v; rewrite !LtoC_K. Qed.
HB.instance Definition _ := GRing.isAdditive.Build type L' CtoL
  CtoL_is_additive.

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

HB.instance Definition _ :=
  GRing.Zmodule_isComRing.Build type mulA mulC mul1 mulD one_nz.

Fact CtoL_is_multiplicative : multiplicative CtoL.
Proof. by split=> [u v|]; rewrite !LtoC_K. Qed.
HB.instance Definition _ := GRing.isMultiplicative.Build type L' CtoL
  CtoL_is_multiplicative.

Fact mulVf u :  u != 0 -> inv u * u = 1.
Proof.
rewrite -(inj_eq CtoL_inj) rmorph0 => nz_u.
by apply: CtoL_inj; rewrite !LtoC_K mulVf.
Qed.

Fact inv0 : inv 0 = 0. Proof. by apply: CtoL_inj; rewrite !LtoC_K invr0. Qed.

HB.instance Definition _ := GRing.ComRing_isField.Build type mulVf inv0.

Fact closedFieldAxiom : GRing.closed_field_axiom type.
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
rewrite rmorphXn /= LtoC_K hornerD hornerXn hornerN opprD addNKr opprK.
rewrite horner_poly rmorph_sum; apply: eq_bigr => k _.
by rewrite rmorphM rmorphXn /= LtoC_K.
Qed.

HB.instance Definition _ := Field_isAlgClosed.Build type closedFieldAxiom.

Fact conj_subproof u : integralOver QtoL (conjL (CtoL u)).
Proof.
have [p mon_p pu0] := CtoL_P u; exists p => //.
rewrite -(fmorph_root conjL) conjL_K map_poly_id // => _ /(nthP 0)[j _ <-].
by rewrite coef_map fmorph_rat.
Qed.

Fact conj_is_semi_additive : semi_additive (fun u => LtoC (conj_subproof u)).
Proof.
by split=> [|u v]; apply: CtoL_inj; rewrite LtoC_K ?raddf0// !rmorphD/= !LtoC_K.
Qed.

Fact conj_is_additive : {morph (fun u => LtoC (conj_subproof u)) : x / - x}.
Proof. by move=> u; apply: CtoL_inj; rewrite LtoC_K !raddfN /= LtoC_K. Qed.

Fact conj_is_multiplicative : multiplicative (fun u => LtoC (conj_subproof u)).
Proof.
split=> [u v|]; apply: CtoL_inj; last by rewrite !LtoC_K rmorph1.
by rewrite LtoC_K 3!{1}rmorphM /= !LtoC_K.
Qed.

Definition conj : {rmorphism type -> type} :=
  GRing.RMorphism.Pack
    (GRing.RMorphism.Class
       (GRing.isSemiAdditive.Build _ _ _ conj_is_semi_additive)
       (GRing.isMultiplicative.Build _ _ _ conj_is_multiplicative)).

Lemma conjK : involutive conj.
Proof. by move=> u; apply: CtoL_inj; rewrite !LtoC_K conjL_K. Qed.

Fact conj_nt : ~ conj =1 id.
Proof.
have [i i2]: exists i : type, i ^+ 2 = -1.
  have [i] := @solve_monicpoly _ 2%N (nth 0 [:: -1 : type]) isT.
  by rewrite !big_ord_recl big_ord0 /= mul0r mulr1 !addr0; exists i.
move/(_ i)/(congr1 CtoL); rewrite LtoC_K => iL_J.
have/lt_geF/idP[] := @ltr01 cfType.
rewrite -oppr_ge0 -(rmorphN1 CtoL).
by rewrite -i2 rmorphXn /= expr2 -{2}iL_J -normCK  exprn_ge0.
Qed.

HB.instance Definition _ := isComplex.Build type conjK conj_nt.

Definition conjMixin := Num.ClosedField.on type.

Lemma algebraic : integralRange (@ratr type).
Proof.
move=> u; have [p mon_p pu0] := CtoL_P u; exists p => {mon_p}//.
rewrite -(fmorph_root CtoL) -map_poly_comp; congr (root _ _):pu0.
by apply/esym/eq_map_poly; apply: fmorph_eq_rat.
Qed.

Fact archimedean : Num.archimedean_axiom type.
Proof. exact: rat_algebraic_archimedean algebraic. Qed.

Definition isCountable := Countable.on type.

End Implementation.

Definition divisor := Implementation.type.

#[export] HB.instance Definition _ := Implementation.conjMixin.
#[export] HB.instance Definition _ :=
  Num.NumDomain_bounded_isArchimedean.Build Implementation.type
    Implementation.archimedean.
#[export] HB.instance Definition _ := Implementation.isCountable.

Module Internals.

Import Implementation.

Local Notation algC := type.

Local Notation QtoC := (ratr : rat -> algC).
Local Notation pQtoC := (map_poly QtoC : {poly rat} -> {poly algC}).

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
  {p : {poly rat} | p \is monic & forall q, root (pQtoC q) x = (p %| q)%R}.
Proof.
have isQ := rat_algebraic_decidable algebraic.
have [p [mon_p px0 irr_p]] := minPoly_decidable_closure isQ (algebraic x).
exists p => // q; apply/idP/idP=> [qx0 | /dvdpP[r ->]]; last first.
  by rewrite rmorphM rootM px0 orbT.
suffices /eqp_dvdl <-: gcdp p q %= p by apply: dvdp_gcdr.
rewrite irr_p ?dvdp_gcdl ?gtn_eqF // -(size_map_poly QtoC) gcdp_map /=.
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
Notation algCeq := (type : eqType).
Notation algCzmod := (type : zmodType).
Notation algCring := (type : ringType).
Notation algCuring := (type : unitRingType).
Notation algCnum := (type : numDomainType).
Notation algCfield := (type : fieldType).
Notation algCnumField := (type : numFieldType).
Notation algCnumClosedField := (type : numClosedFieldType).

Notation Creal := (@Num.Def.Rreal algCnum).

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

Module HBExports. HB.reexport. End HBExports.

End Algebraics.

Export Algebraics.Exports.

Export Algebraics.HBExports.

Section AlgebraicsTheory.

Implicit Types (x y z : algC) (n : nat) (m : int) (b : bool).
Import Algebraics.Internals.

Local Notation ZtoQ := (intr : int -> rat).
Local Notation ZtoC := (intr : int -> algC).
Local Notation QtoC := (ratr : rat -> algC).
Local Notation CtoQ := getCrat.
Local Notation intrp := (map_poly intr).
Local Notation pZtoQ := (map_poly ZtoQ).
Local Notation pZtoC := (map_poly ZtoC).
Local Notation pQtoC := (map_poly ratr).

Let intr_inj_ZtoC := (intr_inj : injective ZtoC).
#[local] Hint Resolve intr_inj_ZtoC : core.

(* Specialization of a few basic ssrnum order lemmas. *)

Definition eqC_nat n p : (n%:R == p%:R :> algC) = (n == p) := eqr_nat _ n p.
Definition leC_nat n p : (n%:R <= p%:R :> algC) = (n <= p)%N := ler_nat _ n p.
Definition ltC_nat n p : (n%:R < p%:R :> algC) = (n < p)%N := ltr_nat _ n p.
Definition Cchar : [char algC] =i pred0 := @char_num _.

(* This can be used in the converse direction to evaluate assertions over     *)
(* manifest rationals, such as 3^-1 + 7%:%^-1 < 2%:%^-1 :> algC.              *)
(* Missing norm and integer exponent, due to gaps in ssrint and rat.          *)
Definition CratrE :=
  let CnF : numClosedFieldType := algC in
  let QtoCm : {rmorphism _ -> _} := @ratr CnF in
  ((rmorph0 QtoCm, rmorph1 QtoCm, rmorphMn QtoCm, rmorphN QtoCm, rmorphD QtoCm),
   (rmorphM QtoCm, rmorphXn QtoCm, fmorphV QtoCm),
   (rmorphMz QtoCm, rmorphXz QtoCm, @ratr_norm CnF, @ratr_sg CnF),
   =^~ (@ler_rat CnF, @ltr_rat CnF, (inj_eq (fmorph_inj QtoCm)))).

Definition CintrE :=
  let CnF : numClosedFieldType := algC in
  let ZtoCm : {rmorphism _ -> _} := *~%R (1 : CnF) in
  ((rmorph0 ZtoCm, rmorph1 ZtoCm, rmorphMn ZtoCm, rmorphN ZtoCm, rmorphD ZtoCm),
   (rmorphM ZtoCm, rmorphXn ZtoCm),
   (rmorphMz ZtoCm, @intr_norm CnF, @intr_sg CnF),
   =^~ (@ler_int CnF, @ltr_int CnF, (inj_eq (@intr_inj CnF)))).

Let nz2 : 2 != 0 :> algC.
Proof. by rewrite pnatr_eq0. Qed.

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
  by apply: (iffP eqP) => [-> | [z _ ->]]; first exists 0; rewrite ?mulr0.
apply: (iffP idP) => [Zyx | [z Zz ->]]; last by rewrite mulfK.
by exists (y / x); rewrite ?divfK.
Qed.

Lemma dvdCP_nat x y : 0 <= x -> 0 <= y -> (x %| y)%C -> {n | y = n%:R * x}.
Proof.
move=> x_ge0 y_ge0 x_dv_y; apply: sig_eqW.
case/dvdCP: x_dv_y => z Zz -> in y_ge0 *; move: x_ge0 y_ge0 Zz.
rewrite le_eqVlt => /predU1P[<- | ]; first by exists 22%N; rewrite !mulr0.
by move=> /pmulr_lge0-> /intrEge0-> /natrP[n ->]; exists n.
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

Lemma dvdC_zmod x : zmod_closed (dvdC x).
Proof.
split=> [| _ _ /dvdCP[y Zy ->] /dvdCP[z Zz ->]]; first exact: dvdC0.
by rewrite -mulrBl dvdC_mull ?rpredB.
Qed.
HB.instance Definition _ x := GRing.isZmodClosed.Build _ (dvdC x) (dvdC_zmod x).

Lemma dvdC_nat (p n : nat) : (p %| n)%C = (p %| n)%N.
Proof.
rewrite unfold_in intrEge0 ?divr_ge0 ?invr_ge0 ?ler0n // !pnatr_eq0.
have [-> | nz_p] := eqVneq; first by rewrite dvd0n.
apply/natrP/dvdnP=> [[q def_q] | [q ->]]; exists q.
  by apply/eqP; rewrite -eqC_nat natrM -def_q divfK ?pnatr_eq0.
by rewrite [num in num / _]natrM mulfK ?pnatr_eq0.
Qed.

Lemma dvdC_int (p : nat) x :
  x \in Num.int -> (p %| x)%C = (p %| `|Num.floor x|)%N.
Proof.
move=> Zx; rewrite -{1}(floorK Zx) {1}[Num.floor x]intEsign.
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
Proof.
by move=> Exy Eyz; rewrite /eqCmod -[x](subrK y) -[_ - z]addrA rpredD.
Qed.

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
#[local] Hint Resolve Crat0 Crat1 : core.

Fact Crat_divring_closed : divring_closed Crat.
Proof.
split=> // _ _ /CratP[x ->] /CratP[y ->].
  by rewrite -rmorphB Crat_rat.
by rewrite -fmorph_div Crat_rat.
Qed.
HB.instance Definition _ := GRing.isDivringClosed.Build _ Crat
  Crat_divring_closed.

Lemma rpred_Crat (S : divringClosed algC) : {subset Crat <= S}.
Proof. by move=> _ /CratP[a ->]; apply: rpred_rat. Qed.

Lemma conj_Crat z : z \in Crat -> z^* = z.
Proof. by move/getCratK <-; rewrite fmorph_div !rmorph_int. Qed.

Lemma Creal_Crat : {subset Crat <= Creal}.
Proof. by move=> x /conj_Crat/CrealP. Qed.

Lemma Cint_rat a : (QtoC a \in Num.int) = (a \in Num.int).
Proof.
apply/idP/idP=> [Za | /numqK <-]; last by rewrite rmorph_int.
apply/intrP; exists (Num.floor (QtoC a)); apply: (can_inj ratCK).
by rewrite rmorph_int floorK.
Qed.

Lemma minCpolyP x :
   {p : {poly rat} | minCpoly x = pQtoC p /\ p \is monic
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
rewrite rmorph_prod big_map /=; apply: eq_bigr => z _.
by rewrite rmorphB /= map_polyX map_polyC.
Qed.
Definition algC_invaut nu x := sval (algC_invaut_subproof nu x).

Lemma algC_invautK nu : cancel (algC_invaut nu) nu.
Proof. by move=> x; rewrite /algC_invaut; case: algC_invaut_subproof. Qed.

Lemma algC_autK nu : cancel nu (algC_invaut nu).
Proof. exact: inj_can_sym (algC_invautK nu) (fmorph_inj nu). Qed.

Fact algC_invaut_is_additive nu : additive (algC_invaut nu).
Proof. exact: can2_additive (algC_autK nu) (algC_invautK nu). Qed.

Fact algC_invaut_is_rmorphism nu : multiplicative (algC_invaut nu).
Proof. exact: can2_rmorphism (algC_autK nu) (algC_invautK nu). Qed.

HB.instance Definition _ (nu : {rmorphism algC -> algC}) :=
  GRing.isAdditive.Build algC algC (algC_invaut nu)
    (algC_invaut_is_additive nu).

HB.instance Definition _ (nu : {rmorphism algC -> algC}) :=
  GRing.isMultiplicative.Build algC algC (algC_invaut nu)
    (algC_invaut_is_rmorphism nu).

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
#[global] Hint Resolve Crat0 Crat1 dvdC0 dvdC_refl eqCmod_refl eqCmodm0 : core.

Module mc_2_0.

Implicit Types (x y z : algC) (n : nat) (m : int) (b : bool).

Notation Cint := (Num.int : {pred algC}) (only parsing).
Notation Cnat := (Num.nat : {pred algC}) (only parsing).
Notation floorC := (Num.floor : algC -> int) (only parsing).
Notation truncC := (Num.trunc : algC -> nat) (only parsing).

Lemma Creal0 : 0 \is Creal. Proof. exact: real0. Qed.
Lemma Creal1 : 1 \is Creal. Proof. exact: real1. Qed.

Lemma floorC_itv x : x \is Creal -> (floorC x)%:~R <= x < (floorC x + 1)%:~R.
Proof. exact: floor_itv. Qed.

Lemma floorC_def x m : m%:~R <= x < (m + 1)%:~R -> floorC x = m.
Proof. exact: floor_def. Qed.

Lemma intCK : cancel intr floorC.
Proof. exact: intrKfloor. Qed.

Lemma floorCK : {in Cint, cancel floorC intr}.
Proof. exact: floorK. Qed.

Lemma floorC0 : floorC 0 = 0. Proof. exact: floor0. Qed.
Lemma floorC1 : floorC 1 = 1. Proof. exact: floor1. Qed.

Lemma floorCpK (p : {poly algC}) :
  p \is a polyOver Cint -> map_poly intr (map_poly floorC p) = p.
Proof. exact: floorpK. Qed.

Lemma floorCpP (p : {poly algC}) :
  p \is a polyOver Cint -> {q | p = map_poly intr q}.
Proof. exact: floorpP. Qed.

Lemma Cint_int m : m%:~R \in Cint.
Proof. exact: intr_int. Qed.

Lemma CintP x : reflect (exists m, x = m%:~R) (x \in Cint).
Proof. exact: intrP. Qed.

Lemma floorCD : {in Cint & Creal, {morph floorC : x y / x + y}}.
Proof. exact: floorD. Qed.

Lemma floorCN : {in Cint, {morph floorC : x / - x}}.
Proof. exact: floorN. Qed.

Lemma floorCM : {in Cint &, {morph floorC : x y / x * y}}.
Proof. exact: floorM. Qed.

Lemma floorCX n : {in Cint, {morph floorC : x / x ^+ n}}.
Proof. exact: floorX. Qed.

Lemma rpred_Cint (S : subringClosed algC) x : x \in Cint -> x \in S.
Proof. exact: rpred_int_num. Qed.

Lemma Cint0 : 0 \in Cint. Proof. exact: int_num0. Qed.
Lemma Cint1 : 1 \in Cint. Proof. exact: int_num1. Qed.

Lemma Creal_Cint : {subset Cint <= Creal}.
Proof. exact: Rreal_int. Qed.

Lemma conj_Cint x : x \in Cint -> x^* = x.
Proof. exact: conj_intr. Qed.

Lemma Cint_normK x : x \in Cint -> `|x| ^+ 2 = x ^+ 2.
Proof. exact: intr_normK. Qed.

Lemma CintEsign x : x \in Cint -> x = (-1) ^+ (x < 0)%C * `|x|.
Proof. exact: intrEsign. Qed.

Lemma truncC_itv x : 0 <= x -> (truncC x)%:R <= x < (truncC x).+1%:R.
Proof. exact: trunc_itv. Qed.

Lemma truncC_def x n : n%:R <= x < n.+1%:R -> truncC x = n.
Proof. exact: trunc_def. Qed.

Lemma natCK n : truncC n%:R = n.
Proof. exact: natrK. Qed.

Lemma CnatP x : reflect (exists n, x = n%:R) (x \in Cnat).
Proof. exact: natrP. Qed.

Lemma truncCK : {in Cnat, cancel truncC (GRing.natmul 1)}.
Proof. exact: truncK. Qed.

Lemma truncC_gt0 x : (0 < truncC x)%N = (1 <= x).
Proof. exact: trunc_gt0. Qed.

Lemma truncC0Pn x : reflect (truncC x = 0) (~~ (1 <= x)).
Proof. exact: trunc0Pn. Qed.

Lemma truncC0 : truncC 0 = 0. Proof. exact: trunc0. Qed.
Lemma truncC1 : truncC 1 = 1. Proof. exact: trunc1. Qed.

Lemma truncCD :
  {in Cnat & Num.nneg, {morph truncC : x y / x + y >-> (x + y)%N}}.
Proof. exact: truncD. Qed.

Lemma truncCM : {in Cnat &, {morph truncC : x y / x * y >-> (x * y)%N}}.
Proof. exact: truncM. Qed.

Lemma truncCX n : {in Cnat, {morph truncC : x / x ^+ n >-> (x ^ n)%N}}.
Proof. exact: truncX. Qed.

Lemma rpred_Cnat (S : semiringClosed algC) x : x \in Cnat -> x \in S.
Proof. exact: rpred_nat_num. Qed.

Lemma Cnat_nat n : n%:R \in Cnat. Proof. exact: natr_nat. Qed.
Lemma Cnat0 : 0 \in Cnat. Proof. exact: nat_num0. Qed.
Lemma Cnat1 : 1 \in Cnat. Proof. exact: nat_num1. Qed.

Lemma Cnat_ge0 x : x \in Cnat -> 0 <= x.
Proof. exact: natr_ge0. Qed.

Lemma Cnat_gt0 x : x \in Cnat -> (0 < x) = (x != 0).
Proof. exact: natr_gt0. Qed.

Lemma conj_Cnat x : x \in Cnat -> x^* = x.
Proof. exact: conj_natr. Qed.

Lemma norm_Cnat x : x \in Cnat -> `|x| = x.
Proof. exact: norm_natr. Qed.

Lemma Creal_Cnat : {subset Cnat <= Creal}.
Proof. exact: Rreal_nat. Qed.

Lemma Cnat_sum_eq1 (I : finType) (P : pred I) (F : I -> algC) :
     (forall i, P i -> F i \in Cnat) -> \sum_(i | P i) F i = 1 ->
   {i : I | [/\ P i, F i = 1 & forall j, j != i -> P j -> F j = 0]}.
Proof. exact: natr_sum_eq1. Qed.

Lemma Cnat_mul_eq1 x y :
  x \in Cnat -> y \in Cnat -> (x * y == 1) = (x == 1) && (y == 1).
Proof. exact: natr_mul_eq1. Qed.

Lemma Cnat_prod_eq1 (I : finType) (P : pred I) (F : I -> algC) :
    (forall i, P i -> F i \in Cnat) -> \prod_(i | P i) F i = 1 ->
  forall i, P i -> F i = 1.
Proof. exact: natr_prod_eq1. Qed.

Lemma Cint_Cnat : {subset Cnat <= Cint}.
Proof. exact: intr_nat. Qed.

Lemma CintE x : (x \in Cint) = (x \in Cnat) || (- x \in Cnat).
Proof. exact: intrE. Qed.

Lemma Cnat_norm_Cint x : x \in Cint -> `|x| \in Cnat.
Proof. exact: natr_norm_int. Qed.

Lemma CnatEint x : (x \in Cnat) = (x \in Cint) && (0 <= x).
Proof. exact: natrEint. Qed.

Lemma CintEge0 x : 0 <= x -> (x \in Cint) = (x \in Cnat).
Proof. exact: intrEge0. Qed.

Lemma Cnat_exp_even x n : ~~ odd n -> x \in Cint -> x ^+ n \in Cnat.
Proof. exact: natr_exp_even. Qed.

Lemma norm_Cint_ge1 x : x \in Cint -> x != 0 -> 1 <= `|x|.
Proof. exact: norm_intr_ge1. Qed.

Lemma sqr_Cint_ge1 x : x \in Cint -> x != 0 -> 1 <= x ^+ 2.
Proof. exact: sqr_intr_ge1. Qed.

Lemma Cint_ler_sqr x : x \in Cint -> x <= x ^+ 2.
Proof. exact: intr_ler_sqr. Qed.

Section AutC.

Implicit Type nu : {rmorphism algC -> algC}.

Lemma aut_Cnat nu : {in Cnat, nu =1 id}. Proof. exact: aut_natr. Qed.
Lemma aut_Cint nu : {in Cint, nu =1 id}. Proof. exact: aut_intr. Qed.

Lemma Cnat_aut nu x : (nu x \in Cnat) = (x \in Cnat).
Proof. exact: natr_aut. Qed.

Lemma Cint_aut nu x : (nu x \in Cint) = (x \in Cint).
Proof. exact: intr_aut. Qed.

End AutC.

Section AutLmodC.

Variables (U V : lmodType algC) (f : {additive U -> V}).

Lemma raddfZ_Cnat a u : a \in Cnat -> f (a *: u) = a *: f u.
Proof. exact: raddfZ_nat. Qed.

Lemma raddfZ_Cint a u : a \in Cint -> f (a *: u) = a *: f u.
Proof. exact: raddfZ_int. Qed.

End AutLmodC.

Section PredCmod.

Variable V : lmodType algC.

Lemma rpredZ_Cnat (S : addrClosed V) : {in Cnat & S, forall z u, z *: u \in S}.
Proof. by move=> _ u /CnatP[n ->]; apply: rpredZnat. Qed.

Lemma rpredZ_Cint (S : zmodClosed V) : {in Cint & S, forall z u, z *: u \in S}.
Proof. by move=> _ u /CintP[m ->]; apply: rpredZint. Qed.

End PredCmod.

End mc_2_0.

#[deprecated(since="mathcomp 2.1.0", note="Use Num.int instead.")]
Notation Cint := (Num.int : {pred algC}) (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use Num.nat instead.")]
Notation Cnat := (Num.nat : {pred algC}) (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use Num.floor instead.")]
Notation floorC := (Num.floor : algC -> int) (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use Num.trunc instead.")]
Notation truncC := (Num.trunc : algC -> nat) (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use real0 instead.")]
Notation Creal0 := mc_2_0.Creal0 (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use real1 instead.")]
Notation Creal1 := mc_2_0.Creal1 (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use floor_itv instead.")]
Notation floorC_itv := mc_2_0.floorC_itv (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use floor_def instead.")]
Notation floorC_def := mc_2_0.floorC_def (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use intrKfloor instead.")]
Notation intCK := mc_2_0.intCK (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use floorK instead.")]
Notation floorCK := mc_2_0.floorCK (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use floor0 instead.")]
Notation floorC0 := mc_2_0.floorC0 (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use floor1 instead.")]
Notation floorC1 := mc_2_0.floorC1 (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use floorpK instead.")]
Notation floorCpK := mc_2_0.floorCpK (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use floorpP instead.")]
Notation floorCpP := mc_2_0.floorCpP (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use intr_int instead.")]
Notation Cint_int := mc_2_0.Cint_int (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use intrP instead.")]
Notation CintP := mc_2_0.CintP (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use floorD instead.")]
Notation floorCD := mc_2_0.floorCD (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use floorN instead.")]
Notation floorCN := mc_2_0.floorCN (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use floorM instead.")]
Notation floorCM := mc_2_0.floorCM (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use floorX instead.")]
Notation floorCX := mc_2_0.floorCX (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use rpred_int_num instead.")]
Notation rpred_Cint := mc_2_0.rpred_Cint (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use int_num0 instead.")]
Notation Cint0 := mc_2_0.Cint0 (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use int_num1 instead.")]
Notation Cint1 := mc_2_0.Cint1 (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use Rreal_int instead.")]
Notation Creal_Cint := mc_2_0.Creal_Cint (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use conj_intr instead.")]
Notation conj_Cint := mc_2_0.conj_Cint (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use intr_normK instead.")]
Notation Cint_normK := mc_2_0.Cint_normK (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use intrEsign instead.")]
Notation CintEsign := mc_2_0.CintEsign (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use trunc_itv instead.")]
Notation truncC_itv := mc_2_0.truncC_itv (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use trunc_def instead.")]
Notation truncC_def := mc_2_0.truncC_def (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use natrK instead.")]
Notation natCK := mc_2_0.natCK (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use natrP instead.")]
Notation CnatP := mc_2_0.CnatP (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use truncK instead.")]
Notation truncCK := mc_2_0.truncCK (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use trunc_gt0 instead.")]
Notation truncC_gt0 := mc_2_0.truncC_gt0 (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use trunc0Pn instead.")]
Notation truncC0Pn := mc_2_0.truncC0Pn (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use trunc0 instead.")]
Notation truncC0 := mc_2_0.truncC0 (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use trunc1 instead.")]
Notation truncC1 := mc_2_0.truncC1 (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use truncD instead.")]
Notation truncCD := mc_2_0.truncCD (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use truncM instead.")]
Notation truncCM := mc_2_0.truncCM (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use truncX instead.")]
Notation truncCX := mc_2_0.truncCX (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use rpred_nat_num instead.")]
Notation rpred_Cnat := mc_2_0.rpred_Cnat (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use natr_nat instead.")]
Notation Cnat_nat := mc_2_0.Cnat_nat (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use nat_num0 instead.")]
Notation Cnat0 := mc_2_0.Cnat0 (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use nat_num1 instead.")]
Notation Cnat1 := mc_2_0.Cnat1 (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use natr_ge0 instead.")]
Notation Cnat_ge0 := mc_2_0.Cnat_ge0 (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use natr_gt0 instead.")]
Notation Cnat_gt0 := mc_2_0.Cnat_gt0 (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use conj_natr instead.")]
Notation conj_Cnat := mc_2_0.conj_Cnat (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use norm_natr instead.")]
Notation norm_Cnat := mc_2_0.norm_Cnat (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use Rreal_nat instead.")]
Notation Creal_Cnat := mc_2_0.Creal_Cnat (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use natr_sum_eq1 instead.")]
Notation Cnat_sum_eq1 := mc_2_0.Cnat_sum_eq1 (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use natr_mul_eq1 instead.")]
Notation Cnat_mul_eq1 := mc_2_0.Cnat_mul_eq1 (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use natr_prod_eq1 instead.")]
Notation Cnat_prod_eq1 := mc_2_0.Cnat_prod_eq1 (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use intr_nat instead.")]
Notation Cint_Cnat := mc_2_0.Cint_Cnat (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use intrE instead.")]
Notation CintE := mc_2_0.CintE (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use natr_norm_int instead.")]
Notation Cnat_norm_Cint := mc_2_0.Cnat_norm_Cint (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use natrEint instead.")]
Notation CnatEint := mc_2_0.CnatEint (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use intrEge0 instead.")]
Notation CintEge0 := mc_2_0.CintEge0 (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use natr_exp_even instead.")]
Notation Cnat_exp_even := mc_2_0.Cnat_exp_even (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use norm_intr_ge1 instead.")]
Notation norm_Cint_ge1 := mc_2_0.norm_Cint_ge1 (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use sqr_intr_ge1 instead.")]
Notation sqr_Cint_ge1 := mc_2_0.sqr_Cint_ge1 (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use intr_ler_sqr instead.")]
Notation Cint_ler_sqr := mc_2_0.Cint_ler_sqr (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use aut_natr instead.")]
Notation aut_Cnat := mc_2_0.aut_Cnat (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use aut_intr instead.")]
Notation aut_Cint := mc_2_0.aut_Cint (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use natr_aut instead.")]
Notation Cnat_aut := mc_2_0.Cnat_aut (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use intr_aut instead.")]
Notation Cint_aut := mc_2_0.Cint_aut (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use raddfZ_nat instead.")]
Notation raddfZ_Cnat := mc_2_0.raddfZ_Cnat (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use raddfZ_int instead.")]
Notation raddfZ_Cint := mc_2_0.raddfZ_Cint (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use rpredZnat instead.")]
Notation rpredZ_Cnat := mc_2_0.rpredZ_Cnat (only parsing).
#[deprecated(since="mathcomp 2.1.0", note="Use rpredZint instead.")]
Notation rpredZ_Cint := mc_2_0.rpredZ_Cint (only parsing).

End AlgebraicsTheory.
#[global] Hint Resolve Creal0 Creal1 Cnat_nat Cnat0 Cnat1 Cint0 Cint1 : core.
#[global] Hint Resolve floorC0 Crat0 Crat1 : core.
#[global] Hint Resolve dvdC0 dvdC_refl eqCmod_refl eqCmodm0 : core.

Local Notation "p ^^ f" := (map_poly f p)
  (at level 30, f at level 30, format "p  ^^  f").

Record algR := in_algR {algRval : algC; algRvalP : algRval \is Num.real}.

Canonical algR_subType := [subType for algRval].
Definition algR_eqMixin := [eqMixin of algR by <:].
Canonical algR_eqType := EqType algR algR_eqMixin.
Definition algR_choiceMixin := [choiceMixin of algR by <:].
Canonical algR_choiceType := ChoiceType algR algR_choiceMixin.
Definition algR_countMixin := [countMixin of algR by <:].
Canonical algR_countType := CountType algR algR_countMixin.
Definition algR_zmodMixin := [zmodMixin of algR by <:].
Canonical algR_zmodType := ZmodType algR algR_zmodMixin.
Definition algR_ringMixin := [ringMixin of algR by <:].
Canonical algR_ringType := RingType algR algR_ringMixin.
Definition algR_comRingMixin := [comRingMixin of algR by <:].
Canonical algR_comRingType := ComRingType algR algR_comRingMixin.
Definition algR_unitRingMixin := [unitRingMixin of algR by <:].
Canonical algR_unitRingType := UnitRingType algR algR_unitRingMixin.
Canonical algR_comUnitRingType := [comUnitRingType of algR].
Definition algR_idomainMixin := [idomainMixin of algR by <:].
Canonical algR_idomainType := IdomainType algR algR_idomainMixin.
Definition algR_fieldMixin := [fieldMixin of algR by <:].
Canonical algR_fieldType := FieldType algR algR_fieldMixin.
Definition algR_porderMixin := [porderMixin of algR by <:].
Canonical algR_porderType := POrderType ring_display algR algR_porderMixin.
Lemma total_algR : totalPOrderMixin [porderType of algR].
Proof. by move=> x y; apply/real_leVge/valP/valP. Qed.
Canonical algR_latticeType := LatticeType algR total_algR.
Canonical algR_distrLatticeType := DistrLatticeType algR total_algR.
Canonical algR_orderType := OrderType algR total_algR.

Lemma algRval_is_rmorphism : rmorphism algRval. Proof. by []. Qed.
Canonical algRval_additive := Additive algRval_is_rmorphism.
Canonical algRval_rmorphism := RMorphism algRval_is_rmorphism.

Definition algR_norm (x : algR) : algR := in_algR (normr_real (val x)).
Lemma algR_ler_norm_add x y : algR_norm (x + y) <= (algR_norm x + algR_norm y).
Proof. exact: ler_norm_add. Qed.
Lemma algR_normr0_eq0 x : algR_norm x = 0 -> x = 0.
Proof. by move=> /(congr1 val)/normr0_eq0 ?; apply/val_inj. Qed.
Lemma algR_normrMn x n : algR_norm (x *+ n) = algR_norm x *+ n.
Proof. by apply/val_inj; rewrite /= !rmorphMn/= normrMn. Qed.
Lemma algR_normrN x : algR_norm (- x) = algR_norm x.
Proof. by apply/val_inj; apply: normrN. Qed.

Section Num.
Definition algR_normedMixin :=
  Num.NormedMixin algR_ler_norm_add algR_normr0_eq0 algR_normrMn algR_normrN.

Section withz.
Let z : algR := 0.
Lemma algR_addr_gt0 (x y : algR) : z < x -> z < y -> z < x + y.
Proof. exact: addr_gt0. Qed.
Lemma algR_ger_leVge (x y : algR) : z <= x -> z <= y -> (x <= y) || (y <= x).
Proof. exact: ger_leVge. Qed.
Lemma algR_normrM : {morph algR_norm : x y / x * y}.
Proof. by move=> *; apply/val_inj; apply: normrM. Qed.
Lemma algR_ler_def (x y : algR) : (x <= y) = (algR_norm (y - x) == y - x).
Proof. by apply: ler_def. Qed.
End withz.

Let algR_ring := (GRing.Ring.Pack (GRing.ComRing.base
  (GRing.ComUnitRing.base (GRing.IntegralDomain.base
     (GRing.IntegralDomain.class [idomainType of algR]))))).
Definition algR_numMixin : @Num.mixin_of algR_ring _ _ :=
    @Num.Mixin _ _ algR_normedMixin
      algR_addr_gt0 algR_ger_leVge algR_normrM algR_ler_def.

Canonical algR_numDomainType  := NumDomainType algR algR_numMixin.
Canonical algR_normedZmodType := NormedZmodType algR algR algR_normedMixin.
Canonical algR_numFieldType := [numFieldType of algR].
Canonical algR_realDomainType := [realDomainType of algR].
Canonical algR_realFieldType := [realFieldType of algR].
End Num.

Definition algR_archiFieldMixin : Num.archimedean_axiom [numDomainType of algR].
Proof.
move=> /= x; have /andP[/= _] := floorC_itv (valP `|x|).
set n := floorC _; have [n_lt0|n_ge0] := ltP n 0.
  move=> /(@lt_le_trans _ _ _ _ 0); rewrite lerz0 lez_addr1.
  by move=> /(_ n_lt0); rewrite normr_lt0.
move=> x_lt; exists (`|(n + 1)%R|%N); apply: lt_le_trans x_lt _.
by rewrite /= rmorphMn/= pmulrn gez0_abs// addr_ge0.
Qed.
Canonical algR_archiFieldType := ArchiFieldType algR algR_archiFieldMixin.

Definition algRpfactor (x : algC) : {poly algR} :=
  if x \is Num.real =P true is ReflectT xR then 'X - (in_algR xR)%:P else
  'X^2 - (in_algR (Creal_Re x) *+ 2) *: 'X + ((in_algR (normr_real x))^+2)%:P.
Notation algCpfactor x := (algRpfactor x ^^ algRval).

Lemma algRpfactorRE (x : algC) (xR : x \is Num.real) :
  algRpfactor x = 'X - (in_algR xR)%:P.
Proof.
rewrite /algRpfactor; case: eqP xR => //= p1 p2.
by rewrite (bool_irrelevance p1 p2).
Qed.

Lemma algCpfactorRE (x : algC) : x \is Num.real ->
  algCpfactor x = 'X - x%:P.
Proof. by move=> xR; rewrite algRpfactorRE map_polyXsubC. Qed.

Lemma algRpfactorCE (x : algC) : x \isn't Num.real ->
  algRpfactor x =
  'X^2 - (in_algR (Creal_Re x) *+ 2) *: 'X + ((in_algR (normr_real x))^+2)%:P.
Proof. by rewrite /algRpfactor; case: eqP => // p; rewrite p. Qed.

Lemma algCpfactorCE (x : algC) : x \isn't Num.real ->
  algCpfactor x = ('X - x%:P) * ('X - x^*%:P).
Proof.
move=> xNR; rewrite algRpfactorCE//=.
rewrite rmorphD rmorphB/= !map_polyZ !map_polyXn/= map_polyX.
rewrite (map_polyC [rmorphism of algRval])/=.
rewrite mulrBl !mulrBr -!addrA; congr (_ + _).
rewrite opprD addrA opprK -opprD -rmorphM/= -normCK; congr (- _ + _).
rewrite mulrC !mul_polyC -scalerDl.
rewrite [x in RHS]algCrect conjC_rect ?Creal_Re ?Creal_Im//.
by rewrite addrACA addNr addr0.
Qed.

Lemma algCpfactorE x :
  algCpfactor x = ('X - x%:P) * ('X - x^*%:P) ^+ (x \isn't Num.real).
Proof.
by have [/algCpfactorRE|/algCpfactorCE] := boolP (_ \is _); rewrite ?mulr1.
Qed.

Lemma size_algCpfactor x : size (algCpfactor x) = (x \isn't Num.real).+2.
Proof.
have [xR|xNR] := boolP (_ \is _); first by rewrite algCpfactorRE// size_XsubC.
by rewrite algCpfactorCE// size_mul ?size_XsubC ?polyXsubC_eq0.
Qed.

Lemma size_algRpfactor x : size (algRpfactor x) = (x \isn't Num.real).+2.
Proof. by have := size_algCpfactor x; rewrite size_map_poly. Qed.

Lemma algCpfactor_eq0 x : (algCpfactor x == 0) = false.
Proof. by rewrite -size_poly_eq0 size_algCpfactor. Qed.

Lemma algRpfactor_eq0 x : (algRpfactor x == 0) = false.
Proof. by rewrite -size_poly_eq0 size_algRpfactor. Qed.

Lemma algCpfactorCgt0 x y : x \isn't Num.real -> y \is Num.real ->
  (algCpfactor x).[y] > 0.
Proof.
move=> xNR yR; rewrite algCpfactorCE// hornerM !hornerXsubC.
rewrite [x]algCrect conjC_rect ?Creal_Re ?Creal_Im// !opprD !addrA opprK.
rewrite -subr_sqr exprMn sqrCi mulN1r opprK ltr_paddl//.
- by rewrite real_exprn_even_ge0// ?rpredB// ?Creal_Re.
by rewrite real_exprn_even_gt0 ?Creal_Im ?orTb//=; apply/eqP/Creal_ImP.
Qed.

Lemma algRpfactorR_mul_gt0 (x a b : algC) :
    x \is Num.real -> a \is Num.real -> b \is Num.real ->
    a <= b ->
    ((algCpfactor x).[a] * (algCpfactor x).[b] <= 0) =
  (a <= x <= b).
Proof.
move=> xR aR bR ab; rewrite !algCpfactorRE// !hornerXsubC.
have [lt_xa|lt_ax|->]/= := real_ltgtP xR aR; last first.
- by rewrite subrr mul0r lexx ab.
- by rewrite nmulr_rle0 ?subr_lt0 ?subr_ge0.
rewrite pmulr_rle0 ?subr_gt0// subr_le0.
by apply: negbTE; rewrite -real_ltNge// (lt_le_trans lt_xa).
Qed.

Lemma monic_algCpfactor x : algCpfactor x \is monic.
Proof. by rewrite algCpfactorE rpredM ?rpredX ?monicXsubC. Qed.

Lemma monic_algRpfactor x : algRpfactor x \is monic.
Proof. by have := monic_algCpfactor x; rewrite map_monic. Qed.

Lemma poly_algR_pfactor (p : {poly algR}) :
  { r : seq algC |
    p ^^ algRval = val (lead_coef p) *: \prod_(z <- r) algCpfactor z }.
Proof.
wlog p_monic : p / p \is monic => [hwlog|].
  have [->|pN0] := eqVneq p 0.
    by exists [::]; rewrite lead_coef0/= rmorph0 scale0r.
  have [|r] := hwlog ((lead_coef p)^-1 *: p).
    by rewrite monicE lead_coefZ mulVf ?lead_coef_eq0//.
  rewrite !lead_coefZ mulVf ?lead_coef_eq0//= scale1r.
  rewrite map_polyZ/= => /(canRL (scalerKV _))->; first by exists r.
  by rewrite fmorph_eq0 lead_coef_eq0.
suff: {r : seq algC | p ^^ algRval = \prod_(z <- r) algCpfactor z}.
  by move=> [r rP]; exists r; rewrite rP (monicP _)// scale1r.
have [/= r pr] := closed_field_poly_normal (p ^^ algRval).
rewrite (monicP _) ?monic_map ?scale1r// {p_monic} in pr *.
have [n] := ubnP (size r).
elim: n r => // n IHn [|x r]/= in p pr *.
 by exists [::]; rewrite pr !big_nil.
rewrite ltnS => r_lt.
have xJxr : x^* \in x :: r.
  rewrite -root_prod_XsubC -pr.
  have /eq_map_poly-> : algRval =1 conjC \o algRval.
    by move=> a /=; rewrite (CrealP (algRvalP _)).
  by rewrite map_poly_comp mapf_root pr root_prod_XsubC mem_head.
have xJr : (x \isn't Num.real) ==> (x^* \in r) by rewrite implyNb CrealE.
have pxdvdC : algCpfactor x %| p ^^ algRval.
  rewrite pr algCpfactorE big_cons/= dvdp_mul2l ?polyXsubC_eq0//.
  by case: (_ \is _) xJr; rewrite ?dvd1p// dvdp_XsubCl root_prod_XsubC.
pose pr'x := p %/ algRpfactor x.
have [||r'] := IHn (if x \is Num.real then r else rem x^* r) pr'x; last 2 first.
- by case: (_ \is _) in xJr *; rewrite ?size_rem// (leq_ltn_trans (leq_pred _)).
- move=> /eqP; rewrite map_divp -dvdp_eq_mul ?algCpfactor_eq0//= => /eqP->.
  by exists (x :: r'); rewrite big_cons mulrC.
rewrite map_divp/= pr big_cons algCpfactorE/=.
rewrite divp_pmul2l ?expf_neq0 ?polyXsubC_eq0//.
case: (_ \is _) => /= in xJr *; first by rewrite divp1//.
by rewrite (big_rem _ xJr)/= mulKp ?polyXsubC_eq0.
Qed.

Definition algR_rcfMixin : Num.real_closed_axiom [numDomainType of algR].
Proof.
move=> p a b le_ab /andP[pa_le0 pb_ge0]/=.
case: ltgtP pa_le0 => //= pa0 _; last first.
  by exists a; rewrite ?lexx// rootE pa0.
case: ltgtP pb_ge0 => //= pb0 _; last first.
  by exists b; rewrite ?lexx ?andbT// rootE -pb0.
have p_neq0 : p != 0 by apply: contraTneq pa0 => ->; rewrite horner0 ltxx.
have {pa0 pb0} pab0 : p.[a] * p.[b] < 0 by rewrite pmulr_llt0.
wlog p_monic : p p_neq0 pab0 / p \is monic => [hwlog|].
  have [|||x axb] := hwlog ((lead_coef p)^-1 *: p).
  - by rewrite scaler_eq0 invr_eq0 lead_coef_eq0 (negPf p_neq0).
  - rewrite !hornerE/= -mulrA mulrACA -expr2 pmulr_rlt0//.
    by rewrite exprn_even_gt0//= invr_eq0 lead_coef_eq0.
  - by rewrite monicE lead_coefZ mulVf ?lead_coef_eq0 ?eqxx.
  by rewrite rootZ ?invr_eq0 ?lead_coef_eq0//; exists x.
have /= [rs prs] := poly_algR_pfactor p.
rewrite (monicP _) ?monic_map// scale1r {p_monic} in prs.
pose ab := [pred x | val a <= x <= val b].
have abR : {subset ab <= Num.real}.
  move=> x /andP[+ _].
  by rewrite -subr_ge0 => /ger0_real; rewrite rpredBr// algRvalP.
wlog : p pab0 {p_neq0 prs} /
    p ^^ algRval = \prod_(x <- rs | x \in ab) ('X - x%:P) => [hw|].
  move: prs; rewrite -!rmorph_prod => /map_poly_inj.
  rewrite (bigID ab)/=; set q := (X in X * _); set u := (X in _ * X) => pqu.
  have [||] := hw q; last first.
  - by move=> x; exists x => //; rewrite pqu rootM q0.
  - by rewrite rmorph_prod/=; under eq_bigr do rewrite algCpfactorRE ?abR//.
  have := pab0; rewrite pqu !hornerM mulrACA [_ * _ * _ < 0]pmulr_llt0//.
  rewrite !horner_prod -big_split/= prodr_gt0// => x.
  have [xR|xNR] := boolP (x \is Num.real); last first.
    by rewrite ?ltEsub/= -!horner_map/= mulr_gt0 ?algCpfactorCgt0 ?algRvalP.
  apply: contraNT; rewrite -leNgt ?leEsub/= -!horner_map/=.
  by rewrite algRpfactorR_mul_gt0 ?algRvalP.
rewrite -big_filter; have := filter_all ab rs.
set rsab := filter _ _.
have: all (mem Num.real) rsab.
  by apply/allP => x; rewrite mem_filter => /andP[/abR].
case: rsab => [_ _|x rsab]/=; rewrite (big_nil, big_cons).
  move=> pval1; move: pab0.
  have /map_poly_inj-> : p ^^ algRval = 1 ^^ algRval by rewrite rmorph1.
  by rewrite !hornerE ltr10.
move=> /andP[xR rsabR] /andP[axb arsb] prsab.
exists (in_algR xR) => //=.
by rewrite -(mapf_root [rmorphism of algRval])//= prsab rootM root_XsubC eqxx.
Qed.
Canonical algR_rcfType := RcfType algR algR_rcfMixin.
