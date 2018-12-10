(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype div.
From mathcomp
Require Import tuple bigop prime finset fingroup ssralg poly polydiv.
From mathcomp
Require Import morphism action finalg zmodp cyclic center pgroup abelian.
From mathcomp
Require Import matrix mxpoly vector falgebra fieldext separable galois.
From mathcomp
Require ssrnum ssrint algC cyclotomic.

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
  by rewrite enumT lead_coefDl ?size_polyXn // lead_coefXn scale1r.
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
rewrite -[n]mul1n -card_matrix -(card_imset _ (can_inj rV2V_K)).
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
exists (enum fT); first by rewrite enumT finField_genPoly eqpxx.
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
  by rewrite !cardsT card_primeChar card_matrix mul1n card_Fp.
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
  rewrite (finField_genPoly finL) -big_filter.
  by rewrite separable_prod_XsubC ?(enum_uniq finL).
exists (enum finL); first by rewrite enumT (finField_genPoly finL) eqpxx.
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
    rewrite /q finField_genPoly rmorph_prod big_map enumT.
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
have{Dalpha} Dalpha: alpha =1 f by move=> a; rewrite -Dalpha ?memvf ?lfunE.
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
move: K a; wlog [{L}L -> K a]: L / exists galL : splittingFieldType F, L = galL.
  by pose galL := (FinSplittingFieldType F L) => /(_ galL); apply; exists galL.
have /galois_fixedField fixLK := finField_galois (subvf K).
have [alpha defGalLK Dalpha] := finField_galois_generator (subvf K).
rewrite -Dalpha ?memvf // -{1}fixLK (('Gal(_ / _) =P _) defGalLK).
rewrite /cycle -gal_generated (galois_fixedField _) ?fixedField_galois //.
by apply/fixedFieldP/eqP=> [|-> | alpha_x _ /set1P->]; rewrite ?memvf ?set11.
Qed.

End FinSplittingField.

Section FinFieldExists.
(* While he existence of finite splitting fields and of finite fields of      *)
(* arbitrary prime power order is mathematically straightforward, it is       *)
(* technically challenging to formalize in Coq. The Coq typechecker performs  *)
(* poorly for the spme of the deeply nested dependent types used in the       *)
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
  case/(arg_minP (size \o rVpoly))=> /= v; set r := rVpoly v.
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

Import ssrnum ssrint algC cyclotomic Num.Theory.
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
  move=> u; rewrite !inE.
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
have /eqP-n1z: `|z| == 1.
  by rewrite -(pexpr_eq1 n_gt0) ?normr_ge0 // -normrX zn1 normr1.
suffices /eqP/normC_sub_eq[t n1t [Dq Dz]]: `|q%:R - z| == `|q%:R| - `|z|.
  suffices z1: z == 1 by rewrite leq_eqVlt -dvdn1 (prim_order_dvd z_prim) z1.
  by rewrite Dz n1z mul1r -(eqr_pmuln2r q_gt0) Dq normr_nat mulr_natl.
pose aq d : algC := (cyclotomic (z ^+ (n %/ d)) d).[q%:R].
suffices: `|aq n| <= (q - 1)%:R.
  rewrite eqr_le ler_sub_dist andbT n1z normr_nat natrB //; apply: ler_trans.
  rewrite {}/aq horner_prod divnn n_gt0 expr1 normr_prod.
  rewrite (bigD1 (Ordinal n_gt1)) ?coprime1n //= !hornerE ler_pemulr //.
  elim/big_ind: _ => // [|d _]; first exact: mulr_ege1.
  rewrite !hornerE; apply: ler_trans (ler_sub_dist _ _).
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
    rewrite uniq_perm_eq ?divisors_uniq ?filter_uniq ?iota_uniq // => d.
    rewrite -dvdn_divisors ?(dvdn_gt0 n_gt0) // mem_filter mem_iota ltnS /=.
    by apply/esym/andb_idr=> d_dv_m; rewrite dvdn_leq ?(dvdn_trans d_dv_m).
  rewrite (eq_big_perm _ def_divm) big_filter big_mkord horner_prod.
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
