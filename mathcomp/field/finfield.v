(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype div tuple bigop prime finset fingroup.
From mathcomp Require Import ssralg poly polydiv morphism action finalg zmodp.
From mathcomp Require Import cyclic center pgroup abelian matrix mxpoly vector.
From mathcomp Require Import falgebra fieldext separable galois.
From mathcomp Require ssrnum ssrint algC cyclotomic.

(******************************************************************************)
(*  Additional constructions and results on finite fields.                    *)
(*                                                                            *)
(*         FinFieldExtType L == A FinFieldType structure on the carrier of L, *)
(*                              where L IS a fieldExtType F structure for an  *)
(*                              F that has a finFieldType structure. This     *)
(*                              does not take any existing finType structure  *)
(*                              on L; this should not be made canonical.      *)
(* FinSplittingFieldType F L == A SplittingFieldType F structure on the       *)
(*                              carrier of L, where L IS a fieldExtType F for *)
(*                              an F with a finFieldType structure; this      *)
(*                              should not be made canonical.                 *)
(*          Import FinVector :: Declares canonical default finType, finRing,  *)
(*                              etc structures (including FinFieldExtType     *)
(*                              above) for abstract vectType, FalgType and    *)
(*                              fieldExtType over a finFieldType. This should *)
(*                              be used with caution (e.g., local to a proof) *)
(*                              as the finType so obtained may clash with the *)
(*                              canonical one for standard types like matrix. *)
(*      PrimeCharType charRp == The carrier of a ringType R such that         *)
(*                              charRp : p \in [char R] holds. This type has  *)
(*                              canonical ringType, ..., fieldType structures *)
(*                              compatible with those of R, as well as        *)
(*                              canonical lmodType 'F_p, ..., algType 'F_p    *)
(*                              structures, plus an FalgType structure if R   *)
(*                              is a finUnitRingType and a splittingFieldType *)
(*                              struture if R is a finFieldType.              *)
(* FinSplittingFieldFor nz_p == sigma-pair whose sval is a splittingFieldType *)
(*                              that is the splitting field for p : {poly F}  *)
(*                              over F : finFieldType, given nz_p : p != 0.   *)
(* PrimePowerField pr_p k_gt0 == sigma2-triple whose s2val is a finFieldType  *)
(*                              of characteristic p and order m = p ^ k,      *)
(*                              given pr_p : prime p and k_gt0 : k > 0.       *)
(*   FinDomainFieldType domR == A finFieldType structure on a finUnitRingType *)
(*                              R, given domR : GRing.IntegralDomain.axiom R. *)
(*                              This is intended to be used inside proofs,    *)
(*                              where one cannot declare Canonical instances. *)
(*                              Otherwise one should construct explicitly the *)
(*                              intermediate structures using the ssralg and  *)
(*                              finalg constructors, and finDomain_mulrC domR *)
(*                              finDomain_fieldP domR to prove commutativity  *)
(*                              and field axioms (the former is Wedderburn's  *)
(*                              little theorem).                              *)
(* FinDomainSplittingFieldType domR charRp == A splittingFieldType structure  *)
(*                              that repackages the two constructions above.  *)
(*                                                                            *)
(* This file also defines the explicit construction of finite fields via      *)
(* quotienting by an irreducible polynomial.                                  *)
(*                   qpoly p ==  the type of polynomials of size < deg p      *)
(*          primitive_poly p <-> p (of degree m) has a root alpha which       *)
(*                               generates the field F_(p^m)                  *)
(*                   dlog q  == the discrete log of element q (n such that    *)
(*                              x ^+ n = q)                                   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory FinRing.Theory.
Local Open Scope ring_scope.

Section FinRing.

Variable R : finRingType.

Lemma finRing_nontrivial : [set: R] != 1%g.
Proof. by apply/trivgPn; exists 1; rewrite ?inE ?oner_neq0. Qed.

Lemma finRing_gt1 : 1 < #|R|.
Proof. by rewrite -cardsT cardG_gt1 finRing_nontrivial. Qed.

End FinRing.

Section FinField.

Variable F : finFieldType.

Lemma card_finField_unit : #|[set: {unit F}]| = #|F|.-1.
Proof.
by rewrite -(cardC1 0) cardsT card_sub; apply: eq_card => x; rewrite unitfE.
Qed.

Definition finField_unit x (nz_x : x != 0) :=
  FinRing.unit F (etrans (unitfE x) nz_x).

Lemma expf_card x : x ^+ #|F| = x :> F.
Proof.
rewrite -[RHS]mulr1 -(ltn_predK (finRing_gt1 F)) exprS.
apply/eqP; rewrite -subr_eq0 -mulrBr mulf_eq0 subr_eq0 -implyNb -unitfE.
apply/implyP=> Ux; rewrite -(val_unitX _ (Sub x _)) -val_unit1 val_eqE.
by rewrite -order_dvdn -card_finField_unit order_dvdG ?inE.
Qed.

Lemma finField_genPoly : 'X^#|F| - 'X = \prod_x ('X - x%:P) :> {poly F}.
Proof.
set n := #|F|; set oppX := - 'X; set pF := LHS.
have le_oppX_n: size oppX <= n by rewrite size_opp size_polyX finRing_gt1.
have: size pF = (size (enum F)).+1 by rewrite -cardE size_addl size_polyXn.
move/all_roots_prod_XsubC->; last by rewrite uniq_rootsE enum_uniq.
  by rewrite big_enum lead_coefDl ?size_polyXn // lead_coefXn scale1r.
by apply/allP=> x _; rewrite rootE !hornerE hornerXn expf_card subrr.
Qed.

Lemma finCharP : {p | prime p & p \in [char F]}.
Proof.
pose e := exponent [set: F]; have e_gt0: e > 0 by apply: exponent_gt0.
have: e%:R == 0 :> F by rewrite -zmodXgE expg_exponent // inE.
by case/natf0_char/sigW=> // p charFp; exists p; rewrite ?(charf_prime charFp).
Qed.

Lemma finField_is_abelem : is_abelem [set: F].
Proof.
have [p pr_p charFp] := finCharP.
by apply/is_abelemP; exists p; last apply: fin_ring_char_abelem.
Qed.

Lemma card_finCharP p n : #|F| = (p ^ n)%N -> prime p -> p \in [char F].
Proof.
move=> oF pr_p; rewrite inE pr_p -order_dvdn.
rewrite (abelem_order_p finField_is_abelem) ?inE ?oner_neq0 //=.
have n_gt0: n > 0 by rewrite -(ltn_exp2l _ _ (prime_gt1 pr_p)) -oF finRing_gt1.
by rewrite cardsT oF -(prednK n_gt0) pdiv_pfactor.
Qed.

End FinField.

Section CardVspace.

Variables (F : finFieldType) (T : finType).

Section Vector.

Variable cvT : Vector.class_of F T.
Let vT := Vector.Pack (Phant F) cvT.

Lemma card_vspace (V : {vspace vT}) : #|V| = (#|F| ^ \dim V)%N.
Proof.
set n := \dim V; pose V2rV v := \row_i coord (vbasis V) i v.
pose rV2V (rv : 'rV_n) := \sum_i rv 0 i *: (vbasis V)`_i.
have rV2V_K: cancel rV2V V2rV.
  have freeV: free (vbasis V) := basis_free (vbasisP V).
  by move=> rv; apply/rowP=> i; rewrite mxE coord_sum_free.
rewrite -[n]mul1n -card_mx -(card_imset _ (can_inj rV2V_K)).
apply: eq_card => v; apply/idP/imsetP=> [/coord_vbasis-> | [rv _ ->]].
  by exists (V2rV v) => //; apply: eq_bigr => i _; rewrite mxE.
by apply: (@rpred_sum vT) => i _; rewrite rpredZ ?vbasis_mem ?memt_nth.
Qed.

Lemma card_vspacef : #|{: vT}%VS| = #|T|.
Proof. by apply: eq_card => v; rewrite (@memvf _ vT). Qed.

End Vector.

Variable caT : Falgebra.class_of F T.
Let aT := Falgebra.Pack (Phant F) caT.

Lemma card_vspace1 : #|(1%VS : {vspace aT})| = #|F|.
Proof. by rewrite card_vspace (dimv1 aT). Qed.

End CardVspace.

Lemma VectFinMixin (R : finRingType) (vT : vectType R) : Finite.mixin_of vT.
Proof.
have v2rK := @Vector.InternalTheory.v2rK R vT.
exact: CanFinMixin (v2rK : @cancel _ (CountType vT (CanCountMixin v2rK)) _ _).
Qed.

(* These instancces are not exported by default because they conflict with    *)
(* existing finType instances such as matrix_finType or primeChar_finType.    *)
Module FinVector.
Section Interfaces.

Variable F : finFieldType.
Implicit Types (vT : vectType F) (aT : FalgType F) (fT : fieldExtType F).

Canonical vect_finType vT := FinType vT (VectFinMixin vT).
Canonical Falg_finType aT := FinType aT (VectFinMixin aT).
Canonical fieldExt_finType fT := FinType fT (VectFinMixin fT).

Canonical Falg_finRingType aT := [finRingType of aT].
Canonical fieldExt_finRingType fT := [finRingType of fT].
Canonical fieldExt_finFieldType fT := [finFieldType of fT].

Lemma finField_splittingField_axiom fT : SplittingField.axiom fT.
Proof.
exists ('X^#|fT| - 'X); first by rewrite rpredB 1?rpredX ?polyOverX.
exists (enum fT); first by rewrite big_enum finField_genPoly eqpxx.
by apply/vspaceP=> x; rewrite memvf seqv_sub_adjoin ?mem_enum.
Qed.

End Interfaces.
End FinVector.

Notation FinFieldExtType := FinVector.fieldExt_finFieldType.
Notation FinSplittingFieldAxiom := (FinVector.finField_splittingField_axiom _).
Notation FinSplittingFieldType F L :=
  (SplittingFieldType F L FinSplittingFieldAxiom).

Section PrimeChar.

Variable p : nat.

Section PrimeCharRing.

Variable R0 : ringType.

Definition PrimeCharType of p \in [char R0] : predArgType := R0.

Hypothesis charRp : p \in [char R0].
Local Notation R := (PrimeCharType charRp).
Implicit Types (a b : 'F_p) (x y : R).

Canonical primeChar_eqType := [eqType of R].
Canonical primeChar_choiceType := [choiceType of R].
Canonical primeChar_zmodType := [zmodType of R].
Canonical primeChar_ringType := [ringType of R].

Definition primeChar_scale a x := a%:R * x.
Local Infix "*p:" := primeChar_scale (at level 40).

Let natrFp n : (inZp n : 'F_p)%:R = n%:R :> R.
Proof.
rewrite [in RHS](divn_eq n p) natrD mulrnA (mulrn_char charRp) add0r.
by rewrite /= (Fp_cast (charf_prime charRp)).
Qed.

Lemma primeChar_scaleA a b x : a *p: (b *p: x) = (a * b) *p: x.
Proof. by rewrite /primeChar_scale mulrA -natrM natrFp. Qed.

Lemma primeChar_scale1 : left_id 1 primeChar_scale.
Proof. by move=> x; rewrite /primeChar_scale mul1r. Qed.

Lemma primeChar_scaleDr : right_distributive primeChar_scale +%R.
Proof. by move=> a x y /=; rewrite /primeChar_scale mulrDr. Qed.

Lemma primeChar_scaleDl x : {morph primeChar_scale^~ x: a b / a + b}.
Proof. by move=> a b; rewrite /primeChar_scale natrFp natrD mulrDl. Qed.

Definition primeChar_lmodMixin :=
  LmodMixin primeChar_scaleA primeChar_scale1
            primeChar_scaleDr primeChar_scaleDl.
Canonical primeChar_lmodType := LmodType 'F_p R primeChar_lmodMixin.

Lemma primeChar_scaleAl : GRing.Lalgebra.axiom ( *%R : R -> R -> R).
Proof. by move=> a x y; apply: mulrA. Qed.
Canonical primeChar_LalgType := LalgType 'F_p R primeChar_scaleAl.

Lemma primeChar_scaleAr : GRing.Algebra.axiom primeChar_LalgType.
Proof. by move=> a x y; rewrite ![a *: _]mulr_natl mulrnAr. Qed.
Canonical primeChar_algType := AlgType 'F_p R primeChar_scaleAr.

End PrimeCharRing.

Local Notation type := @PrimeCharType.

Canonical primeChar_unitRingType (R : unitRingType) charRp :=
  [unitRingType of type R charRp].
Canonical primeChar_unitAlgType (R : unitRingType) charRp :=
  [unitAlgType 'F_p of type R charRp].
Canonical primeChar_comRingType (R : comRingType) charRp :=
  [comRingType of type R charRp].
Canonical primeChar_comUnitRingType (R : comUnitRingType) charRp :=
  [comUnitRingType of type R charRp].
Canonical primeChar_idomainType (R : idomainType) charRp :=
  [idomainType of type R charRp].
Canonical primeChar_fieldType (F : fieldType) charFp :=
  [fieldType of type F charFp].

Section FinRing.

Variables (R0 : finRingType) (charRp : p \in [char R0]).
Local Notation R := (type _ charRp).

Canonical primeChar_finType := [finType of R].
Canonical primeChar_finZmodType := [finZmodType of R].
Canonical primeChar_baseGroupType := [baseFinGroupType of R for +%R].
Canonical primeChar_groupType := [finGroupType of R for +%R].
Canonical primeChar_finRingType := [finRingType of R].
Canonical primeChar_finLmodType := [finLmodType 'F_p of R].
Canonical primeChar_finLalgType := [finLalgType 'F_p of R].
Canonical primeChar_finAlgType := [finAlgType 'F_p of R].

Let pr_p : prime p. Proof. exact: charf_prime charRp. Qed.

Lemma primeChar_abelem : p.-abelem [set: R].
Proof. exact: fin_Fp_lmod_abelem. Qed.

Lemma primeChar_pgroup : p.-group [set: R].
Proof. by case/and3P: primeChar_abelem. Qed.

Lemma order_primeChar x : x != 0 :> R -> #[x]%g = p.
Proof. by apply: (abelem_order_p primeChar_abelem); rewrite inE. Qed.

Let n := logn p #|R|.

Lemma card_primeChar : #|R| = (p ^ n)%N.
Proof. by rewrite /n -cardsT {1}(card_pgroup primeChar_pgroup). Qed.

Lemma primeChar_vectAxiom : Vector.axiom n (primeChar_lmodType charRp).
Proof.
have /isog_isom/=[f /isomP[injf im_f]]: [set: R] \isog [set: 'rV['F_p]_n].
  rewrite (@isog_abelem_card _ _ p) fin_Fp_lmod_abelem //=.
  by rewrite !cardsT card_primeChar card_mx mul1n card_Fp.
exists f; last by exists (invm injf) => x; rewrite ?invmE ?invmK ?im_f ?inE.
move=> a x y; rewrite [a *: _]mulr_natl morphM ?morphX ?inE // zmodXgE.
by congr (_ + _); rewrite -scaler_nat natr_Zp.
Qed.

Definition primeChar_vectMixin := Vector.Mixin primeChar_vectAxiom.
Canonical primeChar_vectType := VectType 'F_p R primeChar_vectMixin.

Lemma primeChar_dimf : \dim {:primeChar_vectType} = n.
Proof. by rewrite dimvf. Qed.

End FinRing.

Canonical primeChar_finUnitRingType (R : finUnitRingType) charRp :=
  [finUnitRingType of type R charRp].
Canonical primeChar_finUnitAlgType (R : finUnitRingType) charRp :=
  [finUnitAlgType 'F_p of type R charRp].
Canonical primeChar_FalgType (R : finUnitRingType) charRp :=
  [FalgType 'F_p of type R charRp].
Canonical primeChar_finComRingType (R : finComRingType) charRp :=
  [finComRingType of type R charRp].
Canonical primeChar_finComUnitRingType (R : finComUnitRingType) charRp :=
  [finComUnitRingType of type R charRp].
Canonical primeChar_finIdomainType (R : finIdomainType) charRp :=
  [finIdomainType of type R charRp].

Section FinField.

Variables (F0 : finFieldType) (charFp : p \in [char F0]).
Local Notation F := (type _ charFp).

Canonical primeChar_finFieldType := [finFieldType of F].
(* We need to use the eta-long version of the constructor here as projections *)
(* of the Canonical fieldType of F cannot be computed syntactically.          *)
Canonical primeChar_fieldExtType := [fieldExtType 'F_p of F for F0].
Canonical primeChar_splittingFieldType := FinSplittingFieldType 'F_p F.

End FinField.

End PrimeChar.

Section FinSplittingField.

Variable F : finFieldType.

(* By card_vspace order K = #|K| for any finType structure on L; however we   *)
(* do not want to impose the FinVector instance here.                         *)
Let order (L : vectType F) (K : {vspace L}) := (#|F| ^ \dim K)%N.

Section FinGalois.

Variable L : splittingFieldType F.
Implicit Types (a b : F) (x y : L) (K E : {subfield L}).

Let galL K : galois K {:L}.
Proof.
without loss {K} ->: K / K = 1%AS.
  by move=> IH_K; apply: galoisS (IH_K _ (erefl _)); rewrite sub1v subvf.
apply/splitting_galoisField; pose finL := FinFieldExtType L.
exists ('X^#|finL| - 'X); split; first by rewrite rpredB 1?rpredX ?polyOverX.
  rewrite (finField_genPoly finL) -big_enum /=.
  by rewrite separable_prod_XsubC ?(enum_uniq finL).
exists (enum finL).
  by rewrite (@big_enum _ _ _ _ finL) (finField_genPoly finL) eqpxx.
by apply/vspaceP=> x; rewrite memvf seqv_sub_adjoin ?(mem_enum finL).
Qed.

Fact galLgen K :
  {alpha | generator 'Gal({:L} / K) alpha & forall x, alpha x = x ^+ order K}.
Proof.
without loss{K} ->: K / K = 1%AS; last rewrite /order dimv1 expn1.
  case/(_ 1%AS)=> // alpha /eqP-defGalL; rewrite /order dimv1 expn1 => Dalpha.
  exists (alpha ^+ \dim K)%g => [|x]; last first.
    elim: (\dim K) => [|n IHn]; first by rewrite gal_id.
    by rewrite expgSr galM ?memvf // IHn Dalpha expnSr exprM.
  have sGalLK: 'Gal({:L} / K) \subset <[alpha]> by rewrite -defGalL galS ?sub1v.
  rewrite /generator {sGalLK}(eq_subG_cyclic _ sGalLK) ?cycle_cyclic ?cycleX //.
  rewrite -orderE orderXdiv orderE -defGalL -?{1}galois_dim ?dimv1 ?divn1 //.
  by rewrite field_dimS ?subvf.
pose f x := x ^+ #|F|.
have idfP x: reflect (f x = x) (x \in 1%VS).
  apply: (iffP (vlineP _ _)) => [[a ->] | xFx].
    by rewrite -in_algE -[LHS]rmorphX expf_card.
  pose q := map_poly (in_alg L) ('X^#|F| - 'X).
  have: root q x.
    rewrite /q rmorphB /= map_polyXn map_polyX.
    by rewrite rootE !(hornerE, hornerXn) [x ^+ _]xFx subrr.
  have{q} ->: q = \prod_(z <- [seq b%:A | b : F]) ('X - z%:P).
    rewrite /q finField_genPoly rmorph_prod big_image /=.
    by apply: eq_bigr => b _; rewrite rmorphB /= map_polyX map_polyC.
  by rewrite root_prod_XsubC => /mapP[a]; exists a.
have fM: rmorphism f.
  rewrite /f; do 2?split=> [x y|]; rewrite ?exprMn ?expr1n //.
  have [p _ charFp] := finCharP F; rewrite (card_primeChar charFp).
  elim: (logn _ _) => // n IHn; rewrite expnSr !exprM {}IHn.
  by rewrite -(char_lalg L) in charFp; rewrite -Frobenius_autE rmorphB.
have fZ: linear f.
  move=> a x y; rewrite -mulr_algl [f _](rmorphD (RMorphism fM)) rmorphM /=.
  by rewrite (idfP _ _) ?mulr_algl ?memvZ // memv_line.
have /kAut_to_gal[alpha galLalpha Dalpha]: kAut 1 {:L} (linfun (Linear fZ)).
  rewrite kAutfE; apply/kHomP; split=> [x y _ _ | x /idfP]; rewrite !lfunE //=.
  exact: (rmorphM (RMorphism fM)).
have{} Dalpha: alpha =1 f by move=> a; rewrite -Dalpha ?memvf ?lfunE.
suffices <-: fixedField [set alpha] = 1%AS.
  by rewrite gal_generated /generator; exists alpha.
apply/vspaceP=> x; apply/fixedFieldP/idfP; rewrite ?memvf // => id_x.
  by rewrite -Dalpha id_x ?set11.
by move=> _ /set1P->; rewrite Dalpha.
Qed.

Lemma finField_galois K E : (K <= E)%VS -> galois K E.
Proof.
move=> sKE; have /galois_fixedField <- := galL E.
rewrite normal_fixedField_galois // -sub_abelian_normal ?galS //.
apply: abelianS (galS _ (sub1v _)) _.
by have [alpha /('Gal(_ / _) =P _)-> _] := galLgen 1; apply: cycle_abelian.
Qed.

Lemma finField_galois_generator K E :
   (K <= E)%VS ->
 {alpha | generator 'Gal(E / K) alpha
        & {in E, forall x, alpha x = x ^+ order K}}.
Proof.
move=> sKE; have [alpha defGalLK Dalpha] := galLgen K.
have inKL_E: (K <= E <= {:L})%VS by rewrite sKE subvf.
have nKE: normalField K E by have/and3P[] := finField_galois sKE.
have galLKalpha: alpha \in 'Gal({:L} / K).
  by rewrite (('Gal(_ / _) =P _) defGalLK) cycle_id.
exists (normalField_cast _ alpha) => [|x Ex]; last first.
  by rewrite (normalField_cast_eq inKL_E).
rewrite /generator -(morphim_cycle (normalField_cast_morphism inKL_E nKE)) //.
by rewrite -((_ =P <[alpha]>) defGalLK) normalField_img.
Qed.

End FinGalois.

Lemma Fermat's_little_theorem (L : fieldExtType F) (K : {subfield L}) a :
  (a \in K) = (a ^+ order K == a).
Proof.
move: K a; wlog [{}L -> K a]: L / exists galL : splittingFieldType F, L = galL.
  by pose galL := (FinSplittingFieldType F L) => /(_ galL); apply; exists galL.
have /galois_fixedField fixLK := finField_galois (subvf K).
have [alpha defGalLK Dalpha] := finField_galois_generator (subvf K).
rewrite -Dalpha ?memvf // -{1}fixLK (('Gal(_ / _) =P _) defGalLK).
rewrite /cycle -gal_generated (galois_fixedField _) ?fixedField_galois //.
by apply/fixedFieldP/eqP=> [|-> | alpha_x _ /set1P->]; rewrite ?memvf ?set11.
Qed.

End FinSplittingField.

Section FinFieldExists.
(* While the existence of finite splitting fields and of finite fields of     *)
(* arbitrary prime power order is mathematically straightforward, it is       *)
(* technically challenging to formalize in Coq. The Coq typechecker performs  *)
(* poorly for some of the deeply nested dependent types used in the           *)
(* construction, such as polynomials over extensions of extensions of finite  *)
(* fields. Any conversion in a nested structure parameter incurs a huge       *)
(* overhead as it is shared across term comparison by call-by-need evalution. *)
(* The proof of FinSplittingFieldFor is contrived to mitigate this effect:    *)
(* the abbreviation map_poly_extField alone divides by 3 the proof checking   *)
(* time, by reducing the number of occurrences of field(Ext)Type structures   *)
(* in the subgoals; the succesive, apparently redundant 'suffices' localize   *)
(* some of the conversions to smaller subgoals, yielding a further 8-fold     *)
(* time gain. In particular, we construct the splitting field as a subtype    *)
(* of a recursive construction rather than prove that the latter yields       *)
(* precisely a splitting field.                                               *)

(* The apparently redundant type annotation reduces checking time by 30%.     *)
Let map_poly_extField (F : fieldType) (L : fieldExtType F) :=
  map_poly (in_alg L) : {poly F} -> {poly L}.
Local Notation "p ^%:A" := (map_poly_extField _ p)
  (at level 2, format "p ^%:A") : ring_scope.

Lemma FinSplittingFieldFor (F : finFieldType) (p : {poly F}) :
  p != 0 -> {L : splittingFieldType F | splittingFieldFor 1 p^%:A {:L}}.
Proof.
have mapXsubC (f : {rmorphism _}) x: map_poly f ('X - x%:P) = 'X - (f x)%:P.
  by rewrite rmorphB /= map_polyX map_polyC.
move=> nz_p; pose splits q := {zs | q %= \prod_(z <- zs) ('X - z%:P)}.
suffices [L splitLp]: {L : fieldExtType F | splittingFieldFor 1 p^%:A {:L}}.
  by exists (FinSplittingFieldType F L).
suffices [L [ys Dp]]: {L : fieldExtType F & splits L p^%:A}.
  pose Lp := subvs_of <<1 & ys>>; pose toL := linfun (vsval : Lp -> L).
  have [zs Dys]: {zs | map toL zs = ys}.
    exists (map (vsproj _) ys); rewrite -map_comp map_id_in // => y ys_y.
    by rewrite /= lfunE /= vsprojK ?seqv_sub_adjoin.
  exists [fieldExtType F of Lp], zs.
    set lhs := (lhs in lhs %= _); set rhs := (rhs in _ %= rhs).
    suffices: map_poly toL lhs %= map_poly toL rhs by rewrite eqp_map.
    rewrite -Dys big_map in Dp; apply: etrans Dp; apply: congr2.
      by rewrite -map_poly_comp; apply/eq_map_poly=> x; apply: rmorph_alg.
    by rewrite rmorph_prod; apply/eq_bigr=> z _; apply mapXsubC.
  set Lzs := LHS; pose Lys := (toL @: Lzs)%VS; apply/vspaceP=> u.
  have: val u \in Lys by rewrite /Lys aimg_adjoin_seq aimg1 Dys (valP u).
  by case/memv_imgP=> v Lzs_v; rewrite memvf lfunE => /val_inj->.
move: {2}_.+1 (ltnSn (size p)) => n; elim: n => // n IHn in F p nz_p * => lbn.
have [Cp|C'p] := leqP (size p) 1.
  pose L := [fieldExtType F of F^o for F]; exists L, [::].
  by rewrite big_nil -size_poly_eq1 size_map_poly eqn_leq Cp size_poly_gt0.
have [r r_dv_p irr_r]: {r | r %| p & irreducible_poly r}.
  pose rVp (v : 'rV_n) (r := rVpoly v) := (1 < size r) && (r %| p).
  have [v0 Dp]: {v0 | rVpoly v0 = p & rVp v0}.
    by exists (poly_rV p); rewrite /rVp poly_rV_K ?C'p /=.
  case/(arg_minnP (size \o rVpoly))=> /= v; set r := rVpoly v.
  case/andP=> C'r r_dv_p min_r; exists r => //; split=> // q C'q q_dv_r.
  have nz_r: r != 0 by rewrite -size_poly_gt0 ltnW.
  have le_q_r: size q <= size r by rewrite dvdp_leq.
  have [u Dq]: {u : 'rV_n | rVpoly u = q}.
    by exists (poly_rV q); rewrite poly_rV_K ?(leq_trans le_q_r) ?size_poly.
  rewrite -dvdp_size_eqp // eqn_leq le_q_r -Dq min_r // /rVp Dq.
  rewrite ltn_neqAle eq_sym C'q size_poly_gt0 (dvdpN0 q_dv_r) //=.
  exact: dvdp_trans q_dv_r r_dv_p.
have{irr_r} [K _ [x rx0 defK]] := irredp_FAdjoin irr_r.
have{r rx0 r_dv_p} /factor_theorem/sig_eqW[q Dp]: root p^%:A x.
  by rewrite -(divpK r_dv_p) [_^%:A]rmorphM rootM rx0 orbT.
have Dszp: size p = size (q * ('X - x%:P)) by rewrite -Dp size_map_poly.
have nz_q: q != 0.
  by move: nz_p; rewrite -size_poly_eq0 Dszp size_poly_eq0 mulf_eq0 => /norP[].
have [L [zs Dq]]: {L : fieldExtType K & splits L q^%:A}.
  apply: (IHn (FinFieldExtType K) q nz_q).
  by rewrite ltnS Dszp size_mul ?polyXsubC_eq0 ?size_XsubC ?addn2 in lbn.
suffices: splits L p^%:A^%:A.
  rewrite -[_^%:A]map_poly_comp -(eq_map_poly (fun a => baseField_scaleE a 1)).
  by exists [fieldExtType F of baseFieldType L].
exists (x%:A :: zs); rewrite big_cons; set rhs := _ * _.
by rewrite Dp mulrC [_^%:A]rmorphM /= mapXsubC /= eqp_mull.
Qed.

Lemma PrimePowerField p k (m := (p ^ k)%N) :
  prime p -> 0 < k -> {Fm : finFieldType | p \in [char Fm] & #|Fm| = m}.
Proof.
move=> pr_p k_gt0; have m_gt1: m > 1 by rewrite (ltn_exp2l 0) ?prime_gt1.
have m_gt0 := ltnW m_gt1; have m1_gt0: m.-1 > 0 by rewrite -ltnS prednK.
pose q := 'X^m - 'X; have Dq R: q R = ('X^m.-1 - 1) * ('X - 0).
  by rewrite subr0 mulrBl mul1r -exprSr prednK.
have /FinSplittingFieldFor[/= L splitLq]: q [ringType of 'F_p] != 0.
  by rewrite Dq monic_neq0 ?rpredM ?monicXsubC ?monic_Xn_sub_1.
rewrite [_^%:A]rmorphB rmorphX /= map_polyX -/(q L) in splitLq.
have charL: p \in [char L] by rewrite char_lalg char_Fp.
pose Fm := FinFieldExtType L; exists Fm => //.
have /finField_galois_generator[/= a _ Da]: (1 <= {:L})%VS by apply: sub1v.
pose Em := fixedSpace (a ^+ k)%g; rewrite card_Fp //= dimv1 expn1 in Da.
have{splitLq} [zs DqL defL] := splitLq.
have Uzs: uniq zs.
  rewrite -separable_prod_XsubC -(eqp_separable DqL) Dq separable_root andbC.
  rewrite /root !hornerE subr_eq0 eq_sym hornerXn expr0n gtn_eqF ?oner_eq0 //=.
  rewrite cyclotomic.separable_Xn_sub_1 // -subn1 natrB // subr_eq0.
  by rewrite natrX charf0 // expr0n gtn_eqF // eq_sym oner_eq0.
suffices /eq_card->: Fm =i zs.
  apply: succn_inj; rewrite (card_uniqP _) //= -(size_prod_XsubC _ id).
  by rewrite -(eqp_size DqL) size_addl size_polyXn // size_opp size_polyX.
have in_zs: zs =i Em.
  move=> z; rewrite -root_prod_XsubC -(eqp_root DqL) (sameP fixedSpaceP eqP).
  rewrite /root !hornerE subr_eq0 /= hornerXn /m; congr (_ == z).
  elim: (k) => [|i IHi]; first by rewrite gal_id.
  by rewrite expgSr expnSr exprM IHi galM ?Da ?memvf.
suffices defEm: Em = {:L}%VS by move=> z; rewrite in_zs defEm memvf.
apply/eqP; rewrite eqEsubv subvf -defL -[Em]subfield_closed agenvS //.
by rewrite subv_add sub1v; apply/span_subvP=> z; rewrite in_zs.
Qed.

End FinFieldExists.

Section FinDomain.

Import order ssrnum ssrint algC cyclotomic Order.TTheory Num.Theory.
Local Infix "%|" := dvdn. (* Hide polynomial divisibility. *)

Variable R : finUnitRingType.

Hypothesis domR : GRing.IntegralDomain.axiom R.
Implicit Types x y : R.

Let lregR x : x != 0 -> GRing.lreg x.
Proof. by move=> xnz; apply: mulrI0_lreg => y /domR/orP[/idPn | /eqP]. Qed.

Lemma finDomain_field : GRing.Field.mixin_of R.
Proof.
move=> x /lregR-regx; apply/unitrP; exists (invF regx 1).
by split; first apply: (regx); rewrite ?mulrA f_invF // mulr1 mul1r.
Qed.

(* This is Witt's proof of Wedderburn's little theorem. *)
Theorem finDomain_mulrC : @commutative R R *%R.
Proof.
have fieldR := finDomain_field.
have [p p_pr charRp]: exists2 p, prime p & p \in [char R].
  have [e /prod_prime_decomp->]: {e | (e > 0)%N & e%:R == 0 :> R}.
    by exists #|[set: R]%G|; rewrite // -order_dvdn order_dvdG ?inE.
  rewrite big_seq; elim/big_rec: _ => [|[p m] /= n]; first by rewrite oner_eq0.
  case/mem_prime_decomp=> p_pr _ _ IHn.
  elim: m => [|m IHm]; rewrite ?mul1n {IHn}// expnS -mulnA natrM.
  by case/eqP/domR/orP=> //; exists p; last apply/andP.
pose Rp := PrimeCharType charRp; pose L : {vspace Rp} := fullv.
pose G := [set: {unit R}]; pose ofG : {unit R} -> Rp := val.
pose projG (E : {vspace Rp}) := [preim ofG of E].
have inG t nzt: Sub t (finDomain_field nzt) \in G by rewrite inE.
have card_projG E: #|projG E| = (p ^ \dim E - 1)%N.
  transitivity #|E|.-1; last by rewrite subn1 card_vspace card_Fp.
  rewrite (cardD1 0) mem0v (card_preim val_inj) /=.
  apply: eq_card => x; congr (_ && _); rewrite [LHS]codom_val.
  by apply/idP/idP=> [/(memPn _ _)-> | /fieldR]; rewrite ?unitr0.
pose C u := 'C[ofG u]%AS; pose Q := 'C(L)%AS; pose q := (p ^ \dim Q)%N.
have defC u: 'C[u] =i projG (C u).
  by move=> v; rewrite cent1E !inE (sameP cent1vP eqP).
have defQ: 'Z(G) =i projG Q.
  move=> u /[!inE].
  apply/centP/centvP=> cGu v _; last exact/val_inj/cGu/memvf.
  by have [-> | /inG/cGu[]] := eqVneq v 0; first by rewrite commr0.
have q_gt1: (1 < q)%N by rewrite (ltn_exp2l 0) ?prime_gt1 ?adim_gt0.
pose n := \dim_Q L; have oG: #|G| = (q ^ n - 1)%N.
  rewrite -expnM mulnC divnK ?skew_field_dimS ?subvf // -card_projG.
  by apply: eq_card => u; rewrite !inE memvf.
have oZ: #|'Z(G)| = (q - 1)%N by rewrite -card_projG; apply: eq_card.
suffices n_le1: (n <= 1)%N.
  move=> u v; apply/centvsP: (memvf (u : Rp)) (memvf (v : Rp)) => {u v}.
  rewrite -(geq_leqif (dimv_leqif_sup (subvf Q))) -/L.
  by rewrite leq_divLR ?mul1n ?skew_field_dimS ?subvf in n_le1.
without loss n_gt1: / (1 < n)%N by rewrite ltnNge; apply: wlog_neg.
have [q_gt0 n_gt0] := (ltnW q_gt1, ltnW n_gt1).
have [z z_prim] := C_prim_root_exists n_gt0.
have zn1: z ^+ n = 1 by apply: prim_expr_order.
have /eqP-n1z: `|z| == 1 by rewrite -(pexpr_eq1 n_gt0) // -normrX zn1 normr1.
suffices /eqP/normC_sub_eq[t n1t [Dq Dz]]:
  `|q%:R - z : algC| == `|q%:R : algC| - `|z|.
  suffices z1: z == 1 by rewrite leq_eqVlt -dvdn1 (prim_order_dvd z_prim) z1.
  by rewrite Dz n1z mul1r -(eqr_pmuln2r q_gt0) Dq normr_nat mulr_natl.
pose aq d : algC := (cyclotomic (z ^+ (n %/ d)) d).[q%:R].
suffices: `|aq n| <= (q - 1)%:R.
  rewrite eq_le ler_sub_dist andbT n1z normr_nat natrB //; apply: le_trans.
  rewrite {}/aq horner_prod divnn n_gt0 expr1 normr_prod.
  rewrite (bigD1 (Ordinal n_gt1)) ?coprime1n //= !hornerE ler_pemulr //.
  elim/big_ind: _ => // [|d _]; first exact: mulr_ege1.
  rewrite !hornerE; apply: le_trans (ler_sub_dist _ _).
  by rewrite normr_nat normrX n1z expr1n ler_subr_addl (leC_nat 2).
have Zaq d: d %| n -> aq d \in Cint.
  move/(dvdn_prim_root z_prim)=> zd_prim.
  rewrite rpred_horner ?rpred_nat //= -Cintr_Cyclotomic //.
  by apply/polyOverP=> i; rewrite coef_map ?rpred_int.
suffices: (aq n %| (q - 1)%:R)%C.
  rewrite {1}[aq n]CintEsign ?Zaq // -(rpredMsign _ (aq n < 0)%R).
  rewrite dvdC_mul2l ?signr_eq0 //.
  have /CnatP[m ->]: `|aq n| \in Cnat by rewrite Cnat_norm_Cint ?Zaq.
  by rewrite leC_nat dvdC_nat; apply: dvdn_leq; rewrite subn_gt0.
have prod_aq m: m %| n -> \prod_(d < n.+1 | d %| m) aq d = (q ^ m - 1)%:R.
  move=> m_dv_n; transitivity ('X^m - 1).[q%:R : algC]; last first.
    by rewrite !hornerE hornerXn -natrX natrB ?expn_gt0 ?prime_gt0.
  rewrite (prod_cyclotomic (dvdn_prim_root z_prim m_dv_n)).
  have def_divm: perm_eq (divisors m) [seq d <- index_iota 0 n.+1 | d %| m].
    rewrite uniq_perm ?divisors_uniq ?filter_uniq ?iota_uniq // => d.
    rewrite -dvdn_divisors ?(dvdn_gt0 n_gt0) // mem_filter mem_iota ltnS /=.
    by apply/esym/andb_idr=> d_dv_m; rewrite dvdn_leq ?(dvdn_trans d_dv_m).
  rewrite (perm_big _ def_divm) big_filter big_mkord horner_prod.
  by apply: eq_bigr => d d_dv_m; rewrite -exprM muln_divA ?divnK.
have /rpredBl<-: (aq n %| #|G|%:R)%C.
  rewrite oG -prod_aq // (bigD1 ord_max) //= dvdC_mulr //.
  by apply: rpred_prod => d /andP[/Zaq].
rewrite center_class_formula addrC oZ natrD addKr natr_sum /=.
apply: rpred_sum => _ /imsetP[u /setDP[_ Z'u] ->]; rewrite -/G /=.
have sQC: (Q <= C u)%VS by apply/subvP=> v /centvP-cLv; apply/cent1vP/cLv/memvf.
have{sQC} /dvdnP[m Dm]: \dim Q %| \dim (C u) by apply: skew_field_dimS.
have m_dv_n: m %| n by rewrite dvdn_divRL // -?Dm ?skew_field_dimS ?subvf.
have m_gt0: (0 < m)%N := dvdn_gt0 n_gt0 m_dv_n.
have{Dm} oCu: #|'C[u]| = (q ^ m - 1)%N.
  by rewrite -expnM mulnC -Dm (eq_card (defC u)) card_projG.
have ->: #|u ^: G|%:R = \prod_(d < n.+1 | d %| n) (aq d / aq d ^+ (d %| m)).
  rewrite -index_cent1 natf_indexg ?subsetT //= setTI prodf_div prod_aq // -oG.
  congr (_ / _); rewrite big_mkcond oCu -prod_aq //= big_mkcond /=.
  by apply: eq_bigr => d _; case: ifP => [/dvdn_trans->| _]; rewrite ?if_same.
rewrite (bigD1 ord_max) //= [n %| m](contraNF _ Z'u) => [|n_dv_m]; last first.
  rewrite -sub_cent1 subEproper eq_sym eqEcard subsetT oG oCu leq_sub2r //.
  by rewrite leq_exp2l // dvdn_leq.
rewrite divr1 dvdC_mulr //; apply/rpred_prod => d /andP[/Zaq-Zaqd _].
have [-> | nz_aqd] := eqVneq (aq d) 0; first by rewrite mul0r.
by rewrite -[aq d]expr1 -exprB ?leq_b1 ?unitfE ?rpredX.
Qed.

Definition FinDomainFieldType : finFieldType :=
  let fin_unit_class := FinRing.UnitRing.class R in
  let com_class := GRing.ComRing.Class finDomain_mulrC in
  let com_unit_class := @GRing.ComUnitRing.Class R com_class fin_unit_class in
  let dom_class := @GRing.IntegralDomain.Class R com_unit_class domR in
  let field_class := @GRing.Field.Class R dom_class finDomain_field in
  let finfield_class := @FinRing.Field.Class R field_class fin_unit_class in
  FinRing.Field.Pack finfield_class.

Definition FinDomainSplittingFieldType p (charRp : p \in [char R]) :=
   let RoverFp := @primeChar_splittingFieldType p FinDomainFieldType charRp in
   [splittingFieldType 'F_p of R for RoverFp].

End FinDomain.

(* Construction of finite fields via irreducible polynomials *)

Section FieldConstr.

Local Open Scope ring_scope.

(*Some needed results about the Poly constructor - not general-purpose*)
Section MorePoly.

Variable R: ringType.

Lemma Poly_nil (s: seq R):
  (all (eq_op^~0) s) = (polyseq (Poly s) == nil).
Proof.
elim: s => [/=| h t /= IHs].
  by rewrite polyseq0.
rewrite polyseq_cons. 
have->: nilp (Poly t) = (polyseq (Poly t) == [::])
  by apply /nilP; case : (polyseq (Poly t) == [::]) /eqP. 
rewrite -IHs. 
case Allt: (all (eq_op^~ 0) t) =>/=; last by rewrite andbF.
case: (h == 0) /eqP => [ eq_h0 | /eqP neq_h0].
  by rewrite eq_h0 polyseqC eq_refl.
by rewrite polyseqC/= neq_h0.
Qed.

Lemma Poly_split (s: seq R):
  ~~(all (eq_op^~ 0) s) ->
  exists s1, (s == Poly s ++ s1) && (all (eq_op^~ 0) s1).
Proof.
elim: s => [//| h t/= IHs].
case Allt: (all (eq_op^~ 0) t) =>/=.
  move=> /nandP[eq_h0 | //]; exists t.
  rewrite polyseq_cons polyseqC eq_h0. 
  move: Allt; rewrite Poly_nil => /eqP->/=.
  by rewrite eq_refl. 
move=> _. rewrite polyseq_cons. 
have->/=: nilp (Poly t) = false
  by apply /nilP /eqP; rewrite -Poly_nil Allt.
apply negbT, IHs in Allt.
case: Allt => [s1 /andP[/eqP t_eq all_s1]].
exists s1.
by rewrite {1}t_eq all_s1 eq_refl.
Qed.

Lemma Poly_cat (s1 s2 : seq R):
  all (eq_op^~0) s2 ->
  Poly (s1 ++ s2) = Poly s1.
Proof.
elim: s1 => [/= all_s2| h t /= IHs all_s2].
  by apply poly_inj; rewrite polyseq0; apply /eqP; rewrite -Poly_nil.
by move: IHs => /(_ all_s2) ->.
Qed.

End MorePoly.

(* We require that the type is finite so that the resulting field is finite. *)
(* We need an integral domain for [irreducible_poly].                        *)
(* Every finite integral domain is a (finite) field.                         *)
Variable F : finFieldType.

Variable p : {poly F}.
Variable p_irred: irreducible_poly p.

(*A polynomial quotiented by p*)
Inductive qpoly : predArgType := Qpoly (qp : {poly F}) of (size qp < size p).

Coercion qp (q: qpoly) : {poly F} := let: Qpoly x _ := q in x.
Definition qsz (q: qpoly) : size q < size p := let: Qpoly _ x := q in x.

Canonical qpoly_subType := [subType for qp].
Definition qpoly_eqMixin := Eval hnf in [eqMixin of qpoly by <:].
Canonical qpoly_eqType := Eval hnf in EqType qpoly qpoly_eqMixin.

Definition qpoly_choiceMixin := [choiceMixin of qpoly by <:].
Canonical qpoly_choiceType := Eval hnf in ChoiceType qpoly qpoly_choiceMixin.

Definition qpoly_countMixin := [countMixin of qpoly by <:].
Canonical qpoly_countType := Eval hnf in CountType qpoly qpoly_countMixin.
Canonical qpoly_subCountType := [subCountType of qpoly].

Lemma qpoly_inj: injective qp. Proof. exact: val_inj. Qed.

(* Size of the Finite Field *)

(* We prove the cardinality of this set by giving a mapping from qpolys to    *)
(* tuples of length (size).-1                                                 *)

Definition qpoly_seq (q: qpoly) : seq F :=
  q ++ nseq ((size p).-1 - size q) 0.

Lemma p_gt_0: 0 < size p.
Proof.
have lt_01 : 0 < 1 by [].
apply (ltn_trans lt_01).
by apply p_irred.
Qed.

Lemma qpoly_seq_size q: size (qpoly_seq q) == (size p).-1.
Proof.
apply /eqP; rewrite /qpoly_seq size_cat size_nseq subnKC //.
case : q => [x Szx /=].
by rewrite leq_predR // p_gt_0. 
Qed.

Definition qpoly_tuple q : ((size p).-1).-tuple F := Tuple (qpoly_seq_size q).

Definition tuple_poly (t: ((size p).-1).-tuple F) : {poly F} := Poly t.

Lemma tuple_poly_size t: 
  size (tuple_poly t) < size p.
Proof.
have szt: size t = ((size p).-1) by apply size_tuple.
have lt_tp: size t < size p by rewrite szt ltn_predL p_gt_0.
by apply (leq_ltn_trans (size_Poly t)).
Qed.

Definition tuple_qpoly (t: ((size p).-1).-tuple F) : qpoly := 
  Qpoly (tuple_poly_size t).

Lemma tuple_qpoly_cancel: cancel tuple_qpoly qpoly_tuple.
Proof. 
move=> [t sz_t]; rewrite /qpoly_tuple /tuple_qpoly/=.
apply val_inj=>/=.
rewrite /tuple_poly/qpoly_seq/=.
move: sz_t => /eqP sz_t.
case Allt: (all (eq_op^~0) t). 
  have nseqt:=Allt; move: Allt.  
  rewrite Poly_nil => /eqP->/=.
  symmetry; rewrite subn0 -sz_t; apply /all_pred1P.
  exact: nseqt.
apply negbT, Poly_split in Allt.
case : Allt => [tl /andP[/eqP t_eq tl_all]]. 
rewrite {3}t_eq; f_equal. 
have <-: size tl = ((size p).-1 - size (Poly t))%N
  by rewrite -sz_t {1}t_eq size_cat -addnBAC // subnn.
by symmetry; apply /all_pred1P.
Qed.

Lemma qpoly_tuple_cancel: cancel qpoly_tuple tuple_qpoly.
Proof. 
move=> [q q_sz]; rewrite /qpoly_tuple /tuple_qpoly/=.
apply val_inj=>/=.
rewrite /tuple_poly /qpoly_seq /=. 
rewrite Poly_cat //; first by apply polyseqK. 
by apply /all_pred1P; rewrite size_nseq.
Qed.

Lemma qpoly_tuple_bij: bijective qpoly_tuple.
Proof.
  apply (Bijective qpoly_tuple_cancel tuple_qpoly_cancel).
Qed.

Definition qpoly_finMixin := CanFinMixin qpoly_tuple_cancel.
Canonical qpoly_finType := Eval hnf in FinType qpoly qpoly_finMixin. 

Lemma qpoly_size: #|qpoly| = (#|F|^((size p).-1))%N.
Proof.
by rewrite (bij_eq_card qpoly_tuple_bij) card_tuple.
Qed.

(* Algebraic Structures*)

(* Z Module *)

Lemma q0_size: size (0 : {poly F}) < size p.
Proof. 
by rewrite size_poly0 p_gt_0.
Qed.

Lemma q1_size : size (1 : {poly F}) < size p.
Proof. 
by rewrite size_poly1 p_irred.
Qed.

Definition q0 : qpoly := Qpoly q0_size.
Definition q1 : qpoly := Qpoly q1_size.

Lemma qadd_size (q1 q2: qpoly) : size (val q1 + val q2) < size p.
Proof.
apply (leq_ltn_trans (size_add q1 q2)).
rewrite gtn_max. 
by apply /andP; split; apply qsz.
Qed.

Definition qadd (q1 q2: qpoly) : qpoly := Qpoly (qadd_size q1 q2).

Lemma qopp_size (q: qpoly) : size (-(val q)) < size p.
Proof. 
by rewrite size_opp; apply qsz.
Qed.

Definition qopp (q: qpoly) := Qpoly (qopp_size q).

Lemma qaddA : associative qadd.
Proof.
move=> q1 q2 q3; rewrite /qadd; apply qpoly_inj=>/=.
by rewrite GRing.addrA. 
Qed.

Lemma qaddC : commutative qadd.
Proof. 
move=> q1 q2; rewrite /qadd; apply qpoly_inj=>/=. 
by rewrite GRing.addrC.
Qed.

Lemma qaddFq : left_id q0 qadd.
Proof. 
move=> q; rewrite /qadd /q0; apply qpoly_inj=>/=.
by rewrite GRing.add0r.
Qed.

Lemma qaddqq : left_inverse q0 qopp qadd.
Proof. 
move=> q; rewrite /qadd /qopp /q0; apply qpoly_inj=>/=.
by rewrite GRing.addrC GRing.subrr.
Qed.

Definition qpoly_zmodMixin := ZmodMixin qaddA qaddC qaddFq qaddqq.
Canonical qpoly_zmodType := ZmodType qpoly qpoly_zmodMixin.

(* Ring *)

Lemma qmul_size (p1 p2: {poly F}) : size ((p1 * p2) %% p) < size p.
Proof. 
by rewrite ltn_modp; apply irredp_neq0.
Qed.

Definition qmul (q1 q2 : qpoly) : qpoly := Qpoly (qmul_size q1 q2).

Lemma qpoly_mulA : associative qmul.
Proof. 
move=> q1 q2 q3; rewrite /qmul; apply qpoly_inj=>/=.
by rewrite (GRing.mulrC ((qp q1 * qp q2) %% p)) !modp_mul
  (GRing.mulrC _ (qp q1 * qp q2)) GRing.mulrA.
Qed.

Lemma qpoly_mulC: commutative qmul.
Proof.
move=> q1 q2; rewrite /qmul; apply qpoly_inj=>/=.
by rewrite GRing.mulrC.
Qed.

Lemma qpoly_mul1q: left_id q1 qmul.
Proof.
move=> q. rewrite /qmul /q1; apply qpoly_inj=>/=. 
by rewrite GRing.mul1r modp_small //; apply qsz.
Qed.

Lemma qpoly_mulD : left_distributive qmul qadd.
Proof. 
move=>q1 q2 q3; rewrite /qmul /qadd; apply qpoly_inj=>/=.
by rewrite -modpD GRing.mulrDl. 
Qed.

Lemma qpoly_1not0: q1 != q0.
Proof. 
case: (q1 == q0) /eqP => //.
rewrite /q0 /q1 /= => [[eq_1_0]].
have neq_1_0:=(GRing.oner_neq0 (poly_ringType F)).
move: neq_1_0.
by rewrite eq_1_0 eq_refl.
Qed. 

Definition qpoly_comRingMixin := ComRingMixin 
  qpoly_mulA qpoly_mulC qpoly_mul1q qpoly_mulD qpoly_1not0.
Canonical qpoly_ringType := RingType qpoly qpoly_comRingMixin.
Canonical qpoly_comRingType := ComRingType qpoly qpoly_mulC.

(* Now we want to show that inverses exist and are computable. *)
(* We do this in several steps                                 *)
Definition prime_poly (p: {poly F}) : Prop :=
  forall (q r : {poly F}), p %| (q * r) -> (p %| q) || (p %| r).

Lemma irred_is_prime (r : {poly F}):
  irreducible_poly r -> prime_poly r.
Proof.
move=> r_irred s t r_div_st.
have [[u v]/= bez] := (Bezoutp r s).
case r_div_s: (r %| s) =>//=.
have rs_coprime: size (gcdp r s) == 1%N; last by 
  rewrite -(Gauss_dvdpr _ rs_coprime). 
case gcd_sz: (size (gcdp r s) == 1%N) => //.
have gcd_div := (dvdp_gcdl r s). 
apply r_irred in gcd_div; last by apply negbT.
move: gcd_div.
by rewrite /eqp dvdp_gcd r_div_s !andbF.
Qed.

Lemma qpoly_zero (q: qpoly) : (q == 0) = (qp q %% p == 0).
Proof.
case: q => [q q_sz]/=. 
have->: 0 = q0 by [].
by rewrite /q0 modp_small.
Qed.

(* The following actually shows that any finite integral domain is a field *)
Lemma qpoly_mulf_eq0 (q1 q2: qpoly) : (q1 * q2) = 0 -> (q1 == 0) || (q2 == 0).
Proof.
have->:(q1 * q2) = qmul q1 q2 by [].
have->:0 = q0 by [].
rewrite /qmul /= => [[/ modp_eq0P p_div_q12]].
rewrite !qpoly_zero.
by apply irred_is_prime.
Qed. 

Lemma qpoly_cancel (q1 q2 q3: qpoly): q1 != 0 -> q1 * q2 = q1 * q3 -> q2 = q3.
Proof.
move=> q1_neq0 q12_13.
have q1_sub_q23: q1 * (q2 - q3) = 0 by rewrite GRing.mulrBr q12_13 GRing.subrr.
apply qpoly_mulf_eq0 in q1_sub_q23.
move: q1_sub_q23 => /orP[ /eqP q1_eq0 | /eqP eq_q23].
  by move: q1_neq0; rewrite q1_eq0 eq_refl.
by apply GRing.subr0_eq.
Qed.

(* To show that inverses exist, we define the map f_q(x) = q * x and we show *)
(* that this is injective (and thus bijective since the set is finite)       *)
(* if q != 0 *)
Definition qmul_map (q: qpoly) := qmul q.

Lemma qmul_map_inj (q: qpoly) : 
  q != 0 ->
  injective (qmul_map q).
Proof.
move=> q_neq_0 q1 q2.
by apply qpoly_cancel.
Qed.

Lemma mul_map_bij (q: qpoly): 
  q != 0 ->
  bijective (qmul_map q).
Proof.
move=> q_neq_0.
by apply injF_bij, qmul_map_inj.
Qed.

Lemma qpoly_inv_exist (q: qpoly):
  q != 0 ->
  exists (inv: qpoly), inv * q = 1.
Proof.
move=> q_neq_0. apply mul_map_bij in q_neq_0.
case : q_neq_0 => g can1 can2.
exists (g 1). 
move: can2 => /( _ 1).
by rewrite GRing.mulrC.
Qed.

(* A (slow) computable inverse function from the above *)
Definition qinv (q: qpoly) :=
  nth q0 (enum qpoly) (find (fun x => x * q == 1) (enum qpoly)).

Lemma qinv_correct (q: qpoly):
  q != 0 ->
  (qinv q) * q = 1.
Proof.
move=>q_neq_0.  
apply /eqP; rewrite /qinv.
have has_inv: has (fun x => x * q == 1) (enum qpoly); 
  last by apply (nth_find q0) in has_inv.
apply /hasP.
apply qpoly_inv_exist in q_neq_0.
case: q_neq_0 => [inv inv_correct].
exists inv; last by apply /eqP. 
have inv_count: count_mem inv (enum qpoly) = 1%N 
  by rewrite enumT; apply enumP.
apply /count_memPn.
by rewrite inv_count.
Qed.

Lemma qinv_zero: qinv 0 = 0.
Proof.
have not_has: ~~ has (fun x => x * 0 == 1) (enum qpoly).
  apply /hasP. 
  by move=>[r _ ]; rewrite GRing.mulr0 eq_sym GRing.oner_eq0.
by rewrite /qinv hasNfind // nth_default.
Qed.

(* The rest of the algebraic structures: *)

(* ComUnitRing *)

Definition qunit : pred qpoly :=
  fun x => x != q0.

Lemma qpoly_mulVr : {in qunit, left_inverse q1 qinv qmul}.
Proof.
move=> q q_in.
by apply qinv_correct.
Qed.

Lemma qpoly_mulrV : {in qunit, right_inverse q1 qinv qmul}.
Proof.
move=>q q_in.
by rewrite qpoly_mulC; apply qpoly_mulVr.
Qed. 

Lemma qpoly_unitP (q1 q2: qpoly): (q2 * q1) = 1 /\ (q1 * q2) = 1 -> qunit q1.
Proof.
move=> [q21_1 q12_1]. 
rewrite /qunit; apply /eqP => q1_eq_0.
move: q12_1; rewrite q1_eq_0.
by rewrite GRing.mul0r => /eqP; rewrite eq_sym GRing.oner_eq0.
Qed.

Lemma qpoly_inv0id : {in [predC qunit], qinv =1 id}.
Proof.
move=>q q_unit.
have: ~~ (q != 0) by []. 
rewrite negbK => /eqP->.
by rewrite qinv_zero.
Qed.

Definition qpoly_unitringmixin := 
  UnitRingMixin qpoly_mulVr qpoly_mulrV qpoly_unitP qpoly_inv0id.
Canonical qpoly_unitringtype := UnitRingType qpoly qpoly_unitringmixin.
Canonical qpoly_comunitring := [comUnitRingType of qpoly].

(*Integral Domain *)

Canonical qpoly_idomaintype := IdomainType qpoly qpoly_mulf_eq0.

(* Field *)

Lemma qpoly_mulVf : GRing.Field.axiom qinv.
Proof.
move=> q q_neq_0.
by apply qpoly_mulVr.
Qed.

Lemma qpoly_inv0: qinv 0%R = 0%R.
Proof.
exact: qinv_zero.
Qed.

Definition qpoly_fieldmixin := FieldMixin qpoly_mulVf qpoly_inv0.
Canonical qpoly_fieldType := FieldType qpoly qpoly_fieldmixin.
Canonical qpoly_finFieldType := Eval hnf in [finFieldType of qpoly].

(* Fields over primitive polynomials *)

Section Primitive.

Definition primitive_poly (p: {poly F}) : Prop := 
  irreducible_poly p /\ p %| 'X^((#|F|^((size p).-1)).-1) - 1 /\
  (forall n, p %| 'X^n - 1 -> (n == 0%N) || (((#|F|^((size p).-1)).-1) <= n)).

Variable p_prim: primitive_poly p.

(* We want to prove that discrete logs exist for all nonzero elements.   *)
(* We do not consider the trivial case where p = cx for constant c.      *)
(* This case is not very interesting, since F[X]/(x) is isomorphic to F. *)

Variable p_notx: 2 < size p.

Lemma qx_size: size (polyX F) < size p.
Proof.
by rewrite size_polyX.
Qed.

(* The primitive element x *)
Definition qx : qpoly := Qpoly qx_size.

Lemma qx_exp (n: nat): qp (qx ^+ n) = ('X^n) %% p.
Proof.
elim: n => [/= | n /= IHn]. 
  by rewrite GRing.expr0 modp_small // size_poly1; apply p_irred.
rewrite !GRing.exprSr.
have->: qx ^+ n * qx = qmul (qx ^+ n) qx by [].
by rewrite /qmul/= IHn GRing.mulrC modp_mul GRing.mulrC.
Qed.

(* To show that discrete logs exist, we use the following map and show that is *)
(* is bijective.                                                               *)

Section DlogEx.

Lemma qx_neq0: qx != 0.
Proof.
have->: 0 = q0 by [].
rewrite /qx/q0/=.
case: (Qpoly qx_size == Qpoly q0_size) /eqP => // [[/eqP eq_x0]].
by rewrite polyX_eq0 in eq_x0.
Qed.

Lemma qxn_neq0 (n: nat): qx ^+ n != 0.
Proof.
by apply expf_neq0, qx_neq0.
Qed.

Definition dlog_ord := 'I_((#|F|^((size p).-1)).-1).

(*Logs only exist for nonzero (or unit) qpolys*)
Inductive qpolyNZ : predArgType := Qnz (qq: qpoly) of (qunit qq).
Coercion qq (q: qpolyNZ) : qpoly := let: Qnz x _ := q in x.
Definition qun (q: qpolyNZ) : qunit q := let: Qnz _ x := q in x.

Canonical qpolyNZ_subType := [subType for qq].

Definition qpolyNZ_eqMixin := Eval hnf in [eqMixin of qpolyNZ by <:].
Canonical qpolyNZ_eqType := Eval hnf in EqType qpolyNZ qpolyNZ_eqMixin.
Definition qpolyNZ_choiceMixin := [choiceMixin of qpolyNZ by <:].
Canonical qpolyNZ_choiceType := Eval hnf in ChoiceType qpolyNZ qpolyNZ_choiceMixin.
Definition qpolyNZ_countMixin := [countMixin of qpolyNZ by <:].
Canonical qpolyNZ_countType := Eval hnf in CountType qpolyNZ qpolyNZ_countMixin.
Canonical qpolyNZ_subCountType := [subCountType of qpolyNZ].

Definition qpolyNZ_finMixin := Eval hnf in [finMixin of qpolyNZ by <:].
Canonical qpolyNZ_finType := Eval hnf in FinType qpolyNZ qpolyNZ_finMixin.
Canonical subFinType := [subFinType of qpolyNZ].

Lemma qpolyNZ_card: #|qpolyNZ| = #|qpoly|.-1.
Proof.
have uniq_sz:=(card_finField_unit qpoly_finFieldType).
move: uniq_sz; rewrite cardsT/= => <-.
by rewrite !card_sub.
Qed.

Lemma qx_unit : qunit qx.
Proof.
by rewrite /qunit qx_neq0.
Qed.

Lemma qpow_unit (n: nat) : qunit (qx ^+ n).
Proof.
by rewrite /qunit qxn_neq0.
Qed.

Definition qpow_map (i: dlog_ord) : qpolyNZ :=
  Qnz (qpow_unit i).

(* We need to know that p does not divide x^n for any n *)
Lemma irred_dvdn_Xn (r: {poly F}) (n: nat):
  irreducible_poly r ->
  2 < size r ->
  ~~ (r %| 'X^n).
Proof.
move=> r_irred r_size.
elim: n => [| n /= IHn].
  rewrite GRing.expr0 dvdp1.
  by apply /eqP => r_eq_1; rewrite r_eq_1 in r_size.
rewrite GRing.exprS.
case r_div: (r %| 'X * 'X^n) => //.
apply (irred_is_prime r_irred) in r_div.
move: r_div => /orP[r_divx | r_divxn]; last by rewrite r_divxn in IHn.
apply dvdp_leq in r_divx; last by rewrite polyX_eq0.
by move: r_divx; rewrite size_polyX leqNgt r_size.
Qed.

(* A weaker lemma than [modpD] *)
Lemma modpD_wk (d q r : {poly F}): 
  d != 0 -> (q + r) %% d = (q %% d + r %% d) %% d.
Proof.
move=> d_neq0; rewrite modpD.
by rewrite (@modp_small _ (_ + _)) // -modpD ltn_modp.
Qed.

Lemma qpow_map_bij: bijective qpow_map.
Proof.
apply inj_card_bij; last by rewrite qpolyNZ_card qpoly_size card_ord leqnn.
move=> n1 n2; rewrite /qpow_map/= => [[]].
wlog: n1 n2 / (n1 <= n2).
  move=> all_eq.
  case: (orP (leq_total n1 n2)) => [n1_leqn2 | n2_leqn1].
    by apply all_eq.
  by move=> qx_n12; symmetry; apply all_eq.
move=> n1_leqn2 qx_n12.
have: (qx ^+ n2 - qx ^+ n1 = 0) by rewrite qx_n12 GRing.subrr.
rewrite -(subnKC n1_leqn2) GRing.exprD.
rewrite -{2}(GRing.mulr1 (qx ^+ n1)) -GRing.mulrBr.
move=> /eqP; rewrite mulf_eq0 => /orP[/eqP xn_eq0|].
  by have /eqP qn1_x := (negbTE (qxn_neq0 n1)).
rewrite qpoly_zero/= qx_exp GRing.addrC modpD_wk; last by apply irredp_neq0.
rewrite modp_mod GRing.addrC -modpD modp_mod => n21_div_p.
apply p_prim in n21_div_p.
move: n21_div_p => /orP[| n12_big].
  rewrite subn_eq0 => n2_leqn1; apply ord_inj; apply /eqP; rewrite eqn_leq.
  by rewrite n1_leqn2 n2_leqn1.
have n2_bound: n2 < (#|F| ^ (size p).-1).-1 by [].
have n12_bound: n2 - n1 <= n2 by rewrite leq_subr.
have lt_contra:= (leq_ltn_trans (leq_trans n12_big n12_bound) n2_bound).
by rewrite ltnn in lt_contra.
Qed.

(* The inverse map (discrete log)*)

Lemma field_gt0: 
  0 < (#|F|^((size p).-1)).-1.
Proof.
rewrite -qpoly_size -qpolyNZ_card; apply /card_gt0P.
by exists (Qnz qx_unit).
Qed.

Definition dlog_map (q : qpolyNZ) : dlog_ord :=
  nth (Ordinal field_gt0) (enum dlog_ord)
    (find (fun i => (qx ^+ (nat_of_ord i) == q)) (enum dlog_ord)).

Lemma dlog_map_exist (q: qpolyNZ):
  exists (i: dlog_ord), (qx ^+ i == q).
Proof.
case: (qpow_map_bij) => g canqg cangq.
exists (g q).
move: cangq => /(_ q)/=; rewrite /qpow_map => q_eq.
apply (f_equal val) in q_eq. 
by move: q_eq =>/=->; rewrite eq_refl.
Qed. 

Lemma dlog_map_correct (q: qpolyNZ):
  (qx ^+ (dlog_map q) = q).
Proof.
rewrite /dlog_map.
have has_dlog: has 
  (fun i =>(qx ^+ (nat_of_ord i) == q)) 
  (enum dlog_ord);
  last by apply /eqP; apply (nth_find (Ordinal field_gt0)) in has_dlog.
apply /hasP.
have [n n_log]:=(dlog_map_exist q).
exists n => //.
have n_count: count_mem n (enum dlog_ord) = 1%N
  by rewrite enumT; apply enumP.
apply /count_memPn.
by rewrite n_count.
Qed.

Lemma dlog_map_can: cancel dlog_map qpow_map.
Proof.
move=> q; rewrite /qpow_map; apply val_inj=>/=.
by rewrite dlog_map_correct.
Qed.

Lemma qpow_map_can: cancel qpow_map dlog_map.
Proof.
rewrite -bij_can_sym.
  exact: dlog_map_can.
exact: qpow_map_bij.
Qed.

Lemma dlog_map_bij: bijective dlog_map.
Proof.
exact: (bij_can_bij qpow_map_bij qpow_map_can).
Qed.

Lemma dlog_map_inj: injective dlog_map.
Proof.
exact: (bij_inj dlog_map_bij).
Qed.

End DlogEx.

(* The full discrete log function, with dlog(0) = 0 *)

Definition dlog (q: qpoly) : dlog_ord :=
(match (qunit q) as u return (qunit q = u -> dlog_ord) with
| true => fun q_unit => dlog_map (Qnz q_unit)
| false => fun _ => (Ordinal field_gt0)
end) erefl.

Lemma exp_dlog (q: qpoly):
  q != 0 ->
  qx ^+ (dlog q) = q.
Proof.
move=> q_neq0.
have q_unit: qunit q by [].
rewrite /dlog; move: erefl.
case: {2 3}(qunit q); last by rewrite q_unit.
by move=> q_unit'/=; rewrite dlog_map_correct.
Qed.

Lemma dlog0: nat_of_ord (dlog 0) = 0%N.
Proof.
rewrite /dlog; move: erefl.
have unit_zero: qunit 0 = false by rewrite /qunit eq_refl.
case: {2 3}(qunit 0) => //.
move=> zero_unit.
have: qunit 0 = true by [].
by rewrite unit_zero.
Qed.

Lemma dlog_exp (i: dlog_ord):
  dlog(qx ^+ i) = i.
Proof.
have->:qx ^+ i = qpow_map i by [].
have->: dlog (qpow_map i) = dlog_map (qpow_map i); 
  last by rewrite qpow_map_can.
rewrite /dlog; move: erefl.
case: {2 3}(qunit (qpow_map i)) => //.
move=> qpow_nunit.
have: qunit (qpow_map i) = true by apply qun.
by rewrite {1}qpow_nunit.
Qed.

(* From definition of primitive poly *)
Lemma qx_field_sz1: qx ^+ (#|F| ^ (size p).-1).-1 = 1.
Proof.
apply qpoly_inj =>/=; rewrite qx_exp.
case p_prim => [_ [p_div _]].
move: p_div.
rewrite /dvdp modpD modNp (@modp_small _ 1); 
  last by rewrite size_poly1 (ltn_trans _ p_notx).
by rewrite GRing.subr_eq0 => /eqP.
Qed.

Lemma qpoly_exp_modn (m n: nat) :
  m = n %[mod (#|F| ^ (size p).-1).-1] ->
  qx ^+ m = qx ^+ n.
Proof.
move=> mn_eqmod.
rewrite (divn_eq m (#|F| ^ (size p).-1).-1) 
  (divn_eq n (#|F| ^ (size p).-1).-1).
rewrite !GRing.exprD !(mulnC _ ((#|F| ^ (size p).-1).-1)).
rewrite !GRing.exprM !qx_field_sz1 !GRing.expr1n !GRing.mul1r.
by rewrite mn_eqmod.
Qed.

End Primitive.

End FieldConstr.