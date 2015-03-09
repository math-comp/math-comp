(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
Require Import fingroup morphism perm automorphism quotient action finalg zmodp.
Require Import gfunctor gproduct cyclic commutator nilpotent pgroup.
Require Import sylow hall abelian maximal frobenius.
Require Import matrix mxalgebra mxrepresentation vector.
Require Import BGsection1 BGsection3 BGsection7 BGsection10.
Require Import BGsection14 BGsection15 BGsection16.
Require ssrnum.
Require Import algC classfun character inertia vcharacter.
Require Import PFsection1 PFsection2 PFsection3 PFsection4 PFsection5.

(******************************************************************************)
(* This file covers Peterfalvi, Section 8: Structure of a Minimal Simple      *)
(* Group of Odd Order. Actually, most Section 8 definitions can be found in   *)
(* BGsection16, which holds the conclusions of the Local Analysis part of the *)
(* proof, as the B & G text has been adapted to fit the usage in Section 8.   *)
(* Most of the definitions of Peterfalvi Section 8 are covered in BGsection7, *)
(* BGsection15 and BGsection16; we only give here:                            *)
(*   FT_Pstructure S T defW <-> the groups W, W1, W2, S, and T satisfy the    *)
(*                    conclusion of Theorem (8.8)(b), in particular, S and T  *)
(*                    are of type P, S = S^(1) ><| W1, and T = T^`(1) ><| W2. *)
(*                    The assumption defW : W1 \x W2 = W is a parameter.      *)
(*           'R[x] == the "signalizer" group of x \in 'A1(M) for the Dade     *)
(*                    hypothesis of M (note: this is only extensionally equal *)
(*                    to the 'R[x] defined in BGsection14).                   *)
(*            'R_M == the signalizer functor for the Dade hypothesis of M.    *)
(*                    Note that this only maps x to 'R[x] for x in 'A1(M).    *)
(*                    The casual use of the R(x) in Peterfalvi is improper,   *)
(*                    as its meaning depends on which maximal group is        *)
(*                    considered.                                             *)
(*       'A~(M, A) == the support of the image of 'CF(M, A) under the Dade    *)
(*                    isometry of a maximal group M.                          *)
(*         'A1~(M) := 'A~(M, 'A1(M)).                                         *)
(*          'A~(M) := 'A~(M, 'A(M)).                                          *)
(*         'A0~(M) := 'A~(M, 'A0(M)).                                         *)
(*  FT_Dade maxM, FT_Dade0 maxM, FT_Dade1 maxM, FT_DadeF maxM                 *)
(*  FT_Dade_hyp maxM, FT_Dade0_hyp maxM, FT_Dade1_hyp maxM, FT_DadeF_hyp maxM *)
(*                 == for maxM : M \in 'M, the Dade isometry of M, with       *)
(*                    domain 'A(M), 'A0(M), 'A1(M) and M`_\F^#, respectively, *)
(*                    and the proofs of the corresponding Dade hypotheses.    *)
(*                    Note that we use an additional restriction (to M`_\F^#) *)
(*                    to fit better with the conventions of PFsection7.       *)
(*  FTsupports M L <-> L supports M in the sense of (8.14) and (8.18). This   *)
(*                    definition is not used outside this file.               *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory.

Local Open Scope ring_scope.

(* Supercedes the notation in BGsection14. *)
Notation "''R' [ x ]" := 'C_((gval 'N[x])`_\F)[x]
 (at level 8, format "''R' [ x ]")  : group_scope.
Notation "''R' [ x ]" := 'C_('N[x]`_\F)[x]%G : Group_scope.

Section Definitions.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).
Implicit Types L M X : {set gT}.

(* These cover Peterfalvi, Definition (8.14). *)
Definition FTsignalizer M x := if 'C[x] \subset M then 1%G else 'R[x]%G.

Definition FTsupports M L :=
  [exists x in 'A(M), ~~ ('C[x] \subset M) && ('C[x] \subset L)].

Definition FT_Dade_support M X :=
  \bigcup_(x in X) class_support (FTsignalizer M x :* x) G.

End Definitions.

Notation "''R_' M" := (FTsignalizer M)
 (at level 8, M at level 2, format "''R_' M") : group_scope.

Notation "''A~' ( M , A )" := (FT_Dade_support M A)
  (at level 8, format "''A~' ( M ,  A )").

Notation "''A1~' ( M )" := 'A~(M, 'A1(M)) (at level 8, format "''A1~' ( M )").
Notation "''A~' ( M )" := 'A~(M, 'A(M)) (at level 8, format "''A~' ( M )").
Notation "''A0~' ( M )" := 'A~(M, 'A0(M)) (at level 8, format "''A0~' ( M )").

Section Eight.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).
Implicit Types (p q : nat) (x y z : gT) (A B : {set gT}).
Implicit Types H K L M N P Q R S T U V W : {group gT}.

(* Peterfalvi, Definition (8.1) is covered by BGsection16.of_typeF. *)

(* This is the remark following Definition (8.1). *)
Remark compl_of_typeF M U V (H := M`_\F) :
  H ><| U = M -> of_typeF M V -> of_typeF M U.
Proof.
move=> defM_U [[]]; rewrite -/H => ntH ntV defM part_b part_c.
have oU: #|U| = #|V|.
  apply/eqP; rewrite -(@eqn_pmul2l #|H|) ?cardG_gt0 //.
  by rewrite (sdprod_card defM) (sdprod_card defM_U).
have [x Mx defU]: exists2 x, x \in M & U :=: V :^ x.
  pose pi := \pi(V); have hallV: pi.-Hall(M) V.
    by rewrite Hall_pi // -(sdprod_Hall defM) (pHall_Hall (Fcore_Hall M)).
  apply: Hall_trans (hallV).
    rewrite mFT_sol // (sub_proper_trans _ (mFT_norm_proper ntH _)) ?gFnorm //.
    rewrite (proper_sub_trans _ (subsetT M)) // properEcard gFsub.
    by rewrite -(sdprod_card defM) ltn_Pmulr ?cardG_gt0 ?cardG_gt1.
  rewrite pHallE -(card_Hall hallV) oU eqxx andbT.
  by case/sdprod_context: defM_U.
have nHx: x \in 'N(H) by apply: subsetP Mx; rewrite gFnorm.
split; first by rewrite {1}defU conjsg_eq1.
  have [U1 [nsU1U abU1 prU1H]] := part_b.
  rewrite defU; exists (U1 :^ x)%G; split; rewrite ?normalJ ?abelianJ //.
  rewrite -/H -(normP nHx) -conjD1g => _ /imsetP[h Hh ->].
  by rewrite -conjg_set1 normJ -conjIg conjSg prU1H.
have [U0 [sU0V expU0 frobHU0]] := part_c.
have [defHU0 _ ntU0 _ _] := Frobenius_context frobHU0.
rewrite defU; exists (U0 :^ x)%G; split; rewrite ?conjSg ?exponentJ //.
by rewrite -/H -(normP nHx) -conjYg FrobeniusJ.
Qed.

Lemma Frobenius_of_typeF M U (H := M`_\F) :
  [Frobenius M = H ><| U] -> of_typeF M U.
Proof.
move=> frobM; have [defM ntH ntU _ _] := Frobenius_context frobM.
have [_ _ nHU tiHU] := sdprodP defM.
split=> //; last by exists U; split; rewrite // -sdprodEY ?defM.
exists 1%G; split; rewrite ?normal1 ?abelian1 //.
by move=> x /(Frobenius_reg_compl frobM)->.
Qed.

(* This is Peterfalvi (8.2).                                                  *)
Lemma typeF_context M U (H := M`_\F) :
    of_typeF M U ->
  [/\ (*a*) forall U0, is_typeF_complement M U U0 -> #|U0| = exponent U,
      (*b*) [Frobenius M = H ><| U] = Zgroup U
    & (*c*) forall U1 (i : Iirr H),
            is_typeF_inertia M U U1 -> i != 0 -> 'I_U['chi_i] \subset U1].
Proof.
case; rewrite -/H => [[ntH ntM defM] _ exU0]; set part_a := forall U0, _.
have [nsHM sUG mulHU nHU _] := sdprod_context defM.
have oU0: part_a.
  move=> U0 [sU0U <- /Frobenius_reg_ker regU0]; rewrite exponent_Zgroup //.
  apply/forall_inP=> S /SylowP[p _ /and3P[sSU0 pS _]].
  apply: odd_regular_pgroup_cyclic pS (mFT_odd S) ntH _ _.
    by rewrite (subset_trans (subset_trans sSU0 sU0U)).
  by move=> x /setD1P[ntx /(subsetP sSU0) U0x]; rewrite regU0 // !inE ntx.
split=> // [|U1 i [nsU1U abU1 s_cUH_U1] nz_i].
  apply/idP/idP=> [frobU | ZgU].
    apply/forall_inP=> S /SylowP[p _ /and3P[sSU pS _]].
    apply: odd_regular_pgroup_cyclic pS (mFT_odd S) ntH _ _.
      by rewrite (subset_trans sSU).
    move=> x /setD1P[ntx /(subsetP sSU) Ux].
    by rewrite (Frobenius_reg_ker frobU) // !inE ntx.
  have [U0 [sU0U expU0 frobU0]] := exU0; have regU0 := Frobenius_reg_ker frobU0.
  suffices defU0: U0 :=: U by rewrite defU0 norm_joinEr ?mulHU // in frobU0.
  by apply/eqP; rewrite eqEcard sU0U /= (oU0 U0) // exponent_Zgroup.
have itoP: is_action M (fun (j : Iirr H) x => conjg_Iirr j x).
  split=> [x | j x y Mx My].
    apply: can_inj (fun j => conjg_Iirr j x^-1) _ => j.
    by apply: irr_inj; rewrite !conjg_IirrE cfConjgK.
  by apply: irr_inj; rewrite !conjg_IirrE (cfConjgM _ nsHM).
pose ito := Action itoP; pose cto := ('Js \ subsetT M)%act.
have actsMcH: [acts M, on classes H | cto].
  apply/subsetP=> x Mx; rewrite !inE Mx; apply/subsetP=> _ /imsetP[y Hy ->].
  have nHx: x \in 'N(H) by rewrite (subsetP (gFnorm _ _)).
  rewrite !inE /= -class_rcoset norm_rlcoset // class_lcoset mem_classes //.
  by rewrite memJ_norm.
apply/subsetP=> g /setIP[Ug /setIdP[nHg c_i_g]]; have Mg := subsetP sUG g Ug.
apply: contraR nz_i => notU1g; rewrite (sameP eqP set1P).
suffices <-: 'Fix_ito[g] = [set 0 : Iirr H].
  by rewrite !inE sub1set inE -(inj_eq (@irr_inj _ _)) conjg_IirrE.
apply/eqP; rewrite eq_sym eqEcard cards1 !(inE, sub1set) /=.
rewrite -(inj_eq (@irr_inj _ _)) conjg_IirrE irr0 cfConjg_cfun1 eqxx.
rewrite (card_afix_irr_classes Mg actsMcH) => [|j y z Hy /=]; last first.
  case/imsetP=> _ /imsetP[t Ht ->] -> {z}.
  by rewrite conjg_IirrE cfConjgE // conjgK cfunJ.
rewrite -(cards1 [1 gT]) subset_leq_card //= -/H.
apply/subsetP=> _ /setIP[/imsetP[a Ha ->] /afix1P caHg]; rewrite inE classG_eq1.
have{caHg} /imsetP[x Hgx cax]: a \in a ^: (H :* g).
  by rewrite class_rcoset caHg class_refl.
have coHg: coprime #|H| #[g].
  apply: (coprime_dvdr (order_dvdG Ug)).
  by rewrite (coprime_sdprod_Hall_l defM) (pHall_Hall (Fcore_Hall M)).
have /imset2P[z y cHgg_z Hy defx]: x \in class_support ('C_H[g] :* g) H.
  have [/and3P[/eqP defUcHgg _ _] _] := partition_cent_rcoset nHg coHg.
  by rewrite class_supportEr -cover_imset defUcHgg.
rewrite -(can_eq (conjgKV y)) conj1g; apply: contraR notU1g => nt_ay'.
have{nt_ay'} Hay': a ^ y^-1 \in H^# by rewrite !inE nt_ay' groupJ ?groupV.
rewrite (subsetP (s_cUH_U1 _ Hay')) // inE Ug.
have ->: g = z.`_(\pi(H)^').
  have [h /setIP[Hh /cent1P cgh] ->] := rcosetP cHgg_z.
  rewrite consttM // (constt1P _) ?mul1g ?constt_p_elt //.
    by rewrite /p_elt -coprime_pi' ?cardG_gt0.
  by rewrite (mem_p_elt _ Hh) // pgroupNK pgroup_pi.
by rewrite groupX //= -conjg_set1 normJ mem_conjgV -defx !inE conjg_set1 -cax.
Qed.

(* Peterfalvi, Definition (8.3) is covered by BGsection16.of_typeI. *)
(* Peterfalvi, Definition (8.4) is covered by BGsection16.of_typeP. *)

Section TypeP_Remarks.
(* These correspond to the remarks following Definition (8.4). *)

Variables (M U W W1 W2 : {group gT}) (defW : W1 \x W2 = W).
Let H := M`_\F.
Let M' := M^`(1)%g.

Hypothesis MtypeP : of_typeP M U defW.

Remark of_typeP_sol : solvable M.
Proof.
have [_ [nilU _ _ defM'] _ _ _] := MtypeP.
have [nsHM' _ mulHU _ _] := sdprod_context defM'.
rewrite (series_sol (der_normal 1 M)) (abelian_sol (der_abelian 0 M)) andbT.
rewrite (series_sol nsHM') (nilpotent_sol (Fcore_nil M)).
by rewrite -mulHU quotientMidl quotient_sol ?(nilpotent_sol nilU).
Qed.

Remark typeP_cent_compl : 'C_M'(W1) = W2.
Proof.
have [[/cyclicP[x ->] _ ntW1 _] _ _ [_ _ _ _ prM'W1] _] := MtypeP.
by rewrite cent_cycle prM'W1 // !inE cycle_id -cycle_eq1 ntW1.
Qed.

Remark typeP_cent_core_compl : 'C_H(W1) = W2.
Proof.
have [sW2H sHM']: W2 \subset H /\ H \subset M'.
  by have [_ [_ _ _ /sdprodW/mulG_sub[-> _]] _ []] := MtypeP.
by apply/eqP; rewrite eqEsubset subsetI sW2H -typeP_cent_compl ?subsetIr ?setSI.
Qed.

Lemma typePF_exclusion K : ~ of_typeF M K.
Proof.
move=> [[ntH ntU1 defM_K] _ [U0 [sU01 expU0] frobU0]].
have [[cycW1 hallW1 ntW1 defM] [_ _ _ defM'] _ [_]] := MtypeP; case/negP.
pose p := pdiv #|W1|; rewrite -/M' -/H in defM defM' frobU0 *.
have piW1p: p \in \pi(W1) by rewrite pi_pdiv cardG_gt1.
have piU0p: p \in \pi(U0).
  rewrite -pi_of_exponent expU0 pi_of_exponent (pi_of_dvd _ _ piW1p) //=.
  rewrite -(@dvdn_pmul2l #|H|) ?cardG_gt0 // (sdprod_card defM_K).
  rewrite -(sdprod_card defM) dvdn_pmul2r ?cardSg //.
  by case/sdprodP: defM' => _ <- _ _; exact: mulG_subl.
have [|X EpX]:= @p_rank_geP _ p 1 U0 _; first by rewrite p_rank_gt0.
have [ntX [sXU0 abelX _]] := (nt_pnElem EpX isT, pnElemP EpX).
have piW1_X: \pi(W1).-group X by apply: pi_pgroup piW1p; case/andP: abelX.
have sXM: X \subset M.
  by rewrite -(sdprodWY defM_K) joingC sub_gen ?subsetU // (subset_trans sXU0).
have nHM: M \subset 'N(H) by apply: gFnorm.
have [regU0 solM] := (Frobenius_reg_ker frobU0, of_typeP_sol).
have [a Ma sXaW1] := Hall_Jsub solM (Hall_pi hallW1) sXM piW1_X.
rewrite -subG1 -(conjs1g a) -(cent_semiregular regU0 sXU0 ntX) conjIg -centJ.
by rewrite (normsP nHM) // -typeP_cent_core_compl ?setIS ?centS.
Qed.

Remark of_typeP_compl_conj W1x : M' ><| W1x = M -> W1x \in W1 :^: M.
Proof.
case/sdprodP=> [[{W1x}_ W1x _ ->] mulM'W1x _ tiM'W1x].
have [[_ /Hall_pi hallW1 _ defM] _ _ _ _] := MtypeP.
apply/imsetP; apply: Hall_trans of_typeP_sol _ (hallW1).
rewrite pHallE -(card_Hall hallW1) -(@eqn_pmul2l #|M'|) ?cardG_gt0 //.
by rewrite (sdprod_card defM) -mulM'W1x mulG_subr /= TI_cardMg.
Qed.

Remark conj_of_typeP x :
  {defWx : W1 :^ x \x W2 :^ x = W :^ x | of_typeP (M :^ x) (U :^ x) defWx}.
Proof.
have defWx: W1 :^ x \x W2 :^ x = W :^ x by rewrite -dprodJ defW.
exists defWx; rewrite /of_typeP !derJ FcoreJ FittingJ centJ -conjIg normJ.
rewrite !cyclicJ !conjsg_eq1 /Hall !conjSg indexJg cardJg -[_ && _]/(Hall M W1).
rewrite -(isog_nil (conj_isog U x)) -!sdprodJ -conjsMg -conjD1g.
rewrite -(conjGid (in_setT x)) -conjUg -conjDg normedTI_J.
have [[-> -> -> ->] [-> -> -> ->] [-> -> -> ->] [-> -> -> -> prW1] ->]:= MtypeP.
by do 2![split]=> // _ /imsetP[y /prW1<- ->]; rewrite cent1J -conjIg.
Qed.

(* This is Peterfalvi (8.5), with an extra clause in anticipation of (8.15). *)
Lemma typeP_context :
  [/\ (*a*) H \x 'C_U(H) = 'F(M),
      (*b*) U^`(1)%g \subset 'C(H) /\ (U :!=: 1%g -> ~~ (U \subset 'C(H))),
      (*c*) normedTI (cyclicTIset defW) G W
    & cyclicTI_hypothesis G defW].
Proof.
have defW2 := typeP_cent_core_compl.
case: MtypeP; rewrite /= -/H => [] [cycW1 hallW1 ntW1 defM] [nilU _ _ defM'].
set V := W :\: _ => [] [_ sM''F defF sFM'] [cycW2 ntW2 sW2H _ _] TI_V.
have [/andP[sHM' nHM'] sUM' mulHU _ tiHU] := sdprod_context defM'.
have sM'M : M' \subset M by apply: der_sub.
have hallM': \pi(M').-Hall(M) M' by rewrite Hall_pi // (sdprod_Hall defM).
have hallH_M': \pi(H).-Hall(M') H := pHall_subl sHM' sM'M (Fcore_Hall M).
have{defF} defF: (H * 'C_U(H))%g = 'F(M).
  rewrite -(setIidPl sFM') -defF -group_modl //= -/H.
  rewrite setIAC (setIidPr (der_sub 1 M)).
  rewrite -(coprime_mulG_setI_norm mulHU) ?norms_cent //; last first.
    by rewrite (coprime_sdprod_Hall_l defM') (pHall_Hall hallH_M').
  by rewrite mulgA (mulGSid (subsetIl _ _)).
have coW12: coprime #|W1| #|W2|.
  rewrite coprime_sym (coprimeSg (subset_trans sW2H sHM')) //.
  by rewrite (coprime_sdprod_Hall_r defM).
have cycW: cyclic W by rewrite (cyclic_dprod defW).
have ctiW: cyclicTI_hypothesis G defW by split; rewrite ?mFT_odd.
split=> //; first by rewrite dprodE ?subsetIr //= setIA tiHU setI1g.
split.
  apply: subset_trans (_ : U :&: 'F(M) \subset _).
    by rewrite subsetI der_sub (subset_trans (dergS 1 sUM')).
  by rewrite -defF -group_modr ?subsetIl // setIC tiHU mul1g subsetIr.
apply: contra => cHU; rewrite -subG1 -tiHU subsetIidr (subset_trans sUM') //.
by rewrite (Fcore_max hallM') ?der_normal // -mulHU mulg_nil ?Fcore_nil.
Qed.

End TypeP_Remarks.

Remark FTtypeP_witness M :
  M \in 'M -> FTtype M != 1%N -> exists_typeP (of_typeP M).
Proof.
move=> maxM /negbTE typeMnot1.
have:= FTtype_range M; rewrite -mem_iota !inE typeMnot1 /=.
by case/or4P=> /FTtypeP[//|U W W1 W2 defW [[]]]; exists U W W1 W2 defW.
Qed.

(* Peterfalvi, Definition (8.6) is covered by BGsection16.of_typeII_IV et al. *)
(* Peterfalvi, Definition (8.7) is covered by BGsection16.of_typeV. *)

Section FTypeP_Remarks.
(* The remarks for Definition (8.4) also apply to (8.6) and (8.7). *)

Variables (M U W W1 W2 : {group gT}) (defW : W1 \x W2 = W).
Let H := M`_\F.
Let M' := M^`(1)%g.

Hypotheses (maxM : M \in 'M) (MtypeP : of_typeP M U defW).

Remark of_typeP_conj (Ux W1x W2x Wx : {group gT}) (defWx : W1x \x W2x = Wx) :
    of_typeP M Ux defWx ->
  exists x,
     [/\ x \in M, U :^ x = Ux, W1 :^ x = W1x, W2 :^ x = W2x & W :^ x = Wx].
Proof.
move=> MtypePx; have [[_ _ _ defMx] [_ _ nUW1x defM'x] _ _ _] := MtypePx.
have [[_ hallW1 _ defM] [_ _ nUW1 defM'] _ _ _] := MtypeP.
have [/mulG_sub[/= sHM' sUM'] [_ _ nM'W1 _]] := (sdprodW defM', sdprodP defM).
rewrite -/M' -/H in defMx defM'x defM defM' sHM' sUM' nM'W1.
have /imsetP[x2 Mx2 defW1x2] := of_typeP_compl_conj MtypeP defMx.
have /andP[sM'M nM'M]: M' <| M by apply: der_normal.
have solM': solvable M' := solvableS sM'M (of_typeP_sol MtypeP).
have [hallU hallUx]: \pi(H)^'.-Hall(M') U /\ \pi(H)^'.-Hall(M') (Ux :^ x2^-1).
  have hallH: \pi(H).-Hall(M') H by apply: pHall_subl (Fcore_Hall M).
  rewrite pHallJnorm ?(subsetP nM'M) ?groupV // -!(compl_pHall _ hallH).
  by rewrite (sdprod_compl defM') (sdprod_compl defM'x).
have coM'W1: coprime #|M'| #|W1| by rewrite (coprime_sdprod_Hall_r defM).
have nUxW1: W1 \subset 'N(Ux :^ x2^-1) by rewrite normJ -sub_conjg -defW1x2.
have [x1] := coprime_Hall_trans nM'W1 coM'W1 solM' hallUx nUxW1 hallU nUW1.
case/setIP=> /(subsetP sM'M) My /(normsP (cent_sub _)) nW1x1 defUx1.
pose x := (x1 * x2)%g; have Mx: x \in M by rewrite groupM.
have defW1x: W1 :^ x = W1x by rewrite conjsgM nW1x1.
have defW2x: W2 :^ x = W2x.
  rewrite -(typeP_cent_compl MtypeP) -(typeP_cent_compl MtypePx).
  by rewrite conjIg -centJ defW1x (normsP nM'M).
by exists x; rewrite -defW dprodJ defW1x defW2x conjsgM -defUx1 conjsgKV.
Qed.

Lemma FTtypeP_neq1 : FTtype M != 1%N.
Proof. by apply/FTtypeP=> // [[V [/(typePF_exclusion MtypeP)]]]. Qed.

Remark compl_of_typeII_IV : FTtype M != 5 -> of_typeII_IV M U defW.
Proof.
move=> Mtype'5.
have [Ux Wx W1x W2x defWx Mtype24]: exists_typeP (of_typeII_IV M).
  have:= FTtype_range M; rewrite leq_eqVlt eq_sym (leq_eqVlt _ 5).
  rewrite (negPf FTtypeP_neq1) (negPf Mtype'5) /= -mem_iota !inE.
  by case/or3P=> /FTtypeP[]// Ux Wx W1x W2x dWx []; exists Ux Wx W1x W2x dWx.
have [MtypePx ntUx prW1x tiFM] := Mtype24.
have [x [Mx defUx defW1x _ _]] := of_typeP_conj MtypePx.
by rewrite -defUx -defW1x cardJg conjsg_eq1 in ntUx prW1x.
Qed.

Remark compl_of_typeII : FTtype M == 2 -> of_typeII M U defW.
Proof.
move=> Mtype2.
have [Ux Wx W1x W2x defWx [[MtypePx _ _ _]]] := FTtypeP 2 maxM Mtype2.
have [x [Mx <- _ _ _]] := of_typeP_conj MtypePx; rewrite -/M' -/H.
rewrite abelianJ normJ -{1}(conjGid Mx) conjSg => cUU not_sNUM M'typeF defH.
split=> //; first by apply: compl_of_typeII_IV; rewrite // (eqP Mtype2).
by apply: compl_of_typeF M'typeF; rewrite defH; have [_ []] := MtypeP.
Qed.

Remark compl_of_typeIII : FTtype M == 3 -> of_typeIII M U defW.
Proof.
move=> Mtype3.
have [Ux Wx W1x W2x defWx [[MtypePx _ _ _]]] := FTtypeP 3 maxM Mtype3.
have [x [Mx <- _ _ _]] := of_typeP_conj MtypePx; rewrite -/M' -/H.
rewrite abelianJ normJ -{1}(conjGid Mx) conjSg.
by split=> //; apply: compl_of_typeII_IV; rewrite // (eqP Mtype3).
Qed.

Remark compl_of_typeIV : FTtype M == 4 -> of_typeIV M U defW.
Proof.
move=> Mtype4.
have [Ux Wx W1x W2x defWx [[MtypePx _ _ _]]] := FTtypeP 4 maxM Mtype4.
have [x [Mx <- _ _ _]] := of_typeP_conj MtypePx; rewrite -/M' -/H.
rewrite abelianJ normJ -{1}(conjGid Mx) conjSg.
by split=> //; apply: compl_of_typeII_IV; rewrite // (eqP Mtype4).
Qed.

Remark compl_of_typeV : FTtype M == 5 -> of_typeV M U defW.
Proof.
move=> Mtype5.
have [Ux Wx W1x W2x defWx [[MtypePx /eqP]]] := FTtypeP 5 maxM Mtype5.
have [x [Mx <- <- _ _]] := of_typeP_conj MtypePx; rewrite -/M' -/H.
by rewrite cardJg conjsg_eq1 => /eqP.
Qed.

End FTypeP_Remarks.

(* This is the statement of Peterfalvi, Theorem (8.8)(a). *)
Definition all_FTtype1 := [forall M : {group gT} in 'M, FTtype M == 1%N].

(* This is the statement of Peterfalvi, Theorem (8.8)(b). *)
Definition typeP_pair S T (W W1 W2 : {set gT}) (defW : W1 \x W2 = W) :=
 [/\      [/\ cyclicTI_hypothesis G defW, S \in 'M & T \in 'M],
   (*b1*) [/\ S^`(1) ><| W1 = S, T^`(1) ><| W2 = T & S :&: T = W]%g,
   (*b2*) (FTtype S == 2) || (FTtype T == 2),
   (*b3*) (1 < FTtype S <= 5 /\ 1 < FTtype T <= 5)%N
 & (*b4*) {in 'M, forall M, FTtype M != 1%N -> gval M \in S :^: G :|: T :^: G}].

Lemma typeP_pair_sym S T W W1 W2 (defW : W1 \x W2 = W) (xdefW : W2 \x W1 = W) :
  typeP_pair S T defW -> typeP_pair T S xdefW.
Proof.
by case=> [[/cyclicTIhyp_sym ? ? ?] [? ?]]; rewrite setIC setUC orbC => ? ? [].
Qed.

(* This is Peterfalvi, Theorem (8.8). *)
Lemma FTtypeP_pair_cases : 
     (*a*) {in 'M, forall M, FTtype M == 1%N}
  \/ (*b*) exists S, exists T, exists_typeP (fun _ => typeP_pair S T).
Proof.
have [_ [| [[S T] [[maxS maxT] [[W1 W2] /=]]]]] := BGsummaryI gT; first by left.
set W := W1 <*> W2; set V := W :\: (W1 :|: W2).
case=> [[cycW tiV _] [defS defT tiST]] b4 /orP b2 b3.
have [cWW /joing_sub[sW1W sW2W]] := (cyclic_abelian cycW, erefl W).
have ntV: V != set0 by have [] := andP tiV.
suffices{tiST tiV cWW sW1W sW2W b3 b4} tiW12: W1 :&: W2 = 1%g.
  have defW: W1 \x W2 = W by rewrite dprodEY ?(centSS _ _ cWW).
  right; exists S, T; exists S _ _ _ defW; split=> // [|M _ /b4[] // x].
    by do 2?split; rewrite ?mFT_odd // /normedTI tiV nVW setTI /=.
  by case=> <-; rewrite inE mem_orbit ?orbT.
wlog {b2 T defT maxT} Stype2: S W1 W2 @W @V maxS defS cycW ntV / FTtype S == 2.
  move=> IH; case/orP: b2 cycW ntV => /IH; first exact.
  by rewrite setIC /V /W /= joingC setUC; apply.
have{maxS Stype2 defS} prW1: prime #|W1|.
  have [U ? W1x ? ? [[StypeP _ prW1x _] _ _ _ _]] := FTtypeP 2 maxS Stype2.
  by have /imsetP[x _ ->] := of_typeP_compl_conj StypeP defS; rewrite cardJg.
rewrite prime_TIg //; apply: contra ntV => sW12.
by rewrite setD_eq0 (setUidPr sW12) join_subG sW12 /=.
Qed.

(* This is Peterfalvi (8.9). *)
(* We state the lemma using the of_typeP predicate, as it is the Skolemised  *)
(* form of Peterfalvi, Definition (8.4).                                     *)
Lemma typeP_pairW S T W W1 W2 (defW : W1 \x W2 = W) :
  typeP_pair S T defW -> exists U : {group gT}, of_typeP S U defW.
Proof.
case=> [[[cycW _ /and3P[_ _ /eqP nVW]] maxS _] [defS _ defST] _ [Stype25 _] _].
set S' := S^`(1)%g in defS; have [nsS'S _ _ _ tiS'W1] := sdprod_context defS.
have{Stype25} Stype'1: FTtype S != 1%N by apply: contraTneq Stype25 => ->.
have [/mulG_sub[sW1W sW2W] [_ mulW12 cW12 _]] := (dprodW defW, dprodP defW).
have [cycW1 cycW2] := (cyclicS sW1W cycW, cyclicS sW2W cycW).
have{cycW1 cycW2} coW12: coprime #|W1| #|W2| by rewrite -(cyclic_dprod defW).
have{maxS Stype'1} [Ux Wx W1x W2x defWx StypeP] := FTtypeP_witness maxS Stype'1.
have /imsetP[y Sy defW1] := of_typeP_compl_conj StypeP defS.
suffices defW2: W2 :=: W2x :^ y.
  have [] := conj_of_typeP StypeP y; rewrite -defWx dprodJ -defW1 -defW2.
  by rewrite (conjGid Sy) {-1}defW; exists (Ux :^ y)%G.
have [[_ hallW1x _ defSx] _ _ [/cyclic_abelian abW2x _ _ _ _] _] := StypeP.
have{Sy} nS'y: y \in 'N(S') by rewrite (subsetP (normal_norm nsS'S)).
have{nS'y} defW2xy: W2x :^ y = 'C_S'(W1).
  by rewrite -(typeP_cent_compl StypeP) conjIg -centJ -defW1 (normP nS'y).
have{nsS'S} sW2S': W2 \subset S'.
  have sW2S: W2 \subset S by rewrite (subset_trans sW2W) // -defST subsetIl.
  have{hallW1x} hallW1: \pi(W1).-Hall(S) W1x by rewrite defW1 /= cardJg Hall_pi.
  have hallS': \pi(W1)^'.-Hall(S) S' by apply/(sdprod_normal_pHallP _ hallW1).
  by rewrite coprime_pi' // (sub_normal_Hall hallS') in coW12 *.
have sW2xy: W2 \subset W2x :^ y by rewrite defW2xy subsetI sW2S'.
have defW2: W2 :=: S' :&: W by rewrite -mulW12 -group_modr ?tiS'W1 ?mul1g.
apply/eqP; rewrite eqEsubset sW2xy defW2 subsetI {1}defW2xy subsetIl /=.
rewrite -nVW /= setTI cents_norm // (centsS (subsetDl _ _)) // -mulW12.
by rewrite centM subsetI {1}defW2xy subsetIr sub_abelian_cent // abelianJ.
Qed.

Section OneMaximal.

Variable M U W W1 W2 : {group gT}. (* W, W1 and W2 are only used later. *)
Hypothesis maxM : M \in 'M.

(* Peterfalvi, Definition (8.10) is covered in BGsection16. *)

(* This is Peterfalvi (8.11). *)
Lemma FTcore_facts :
 [/\ Hall G M`_\F, Hall G M`_\s
   & forall S, Sylow M`_\s S -> S :!=: 1%g -> 'N(S) \subset M].
Proof.
have hallMs := Msigma_Hall_G maxM; have [_ sMs _] := and3P hallMs.
rewrite def_FTcore // (pHall_Hall hallMs).
split=> // [|S /SylowP[p _ sylS] ntS].
  have sMF_Ms:= Fcore_sub_Msigma maxM.
  apply: (@pHall_Hall _ \pi(M`_\F)); apply: (subHall_Hall hallMs).
    by move=> p /(piSg sMF_Ms)/(pnatPpi sMs).
  exact: pHall_subl (pcore_sub _ M) (Fcore_Hall M).
have s_p: p \in \sigma(M).
  by rewrite (pnatPpi sMs) // -p_rank_gt0 -(rank_Sylow sylS) rank_gt0.
by apply: (norm_sigma_Sylow s_p); exact: (subHall_Sylow (Msigma_Hall maxM)).
Qed.

(* This is Peterfalvi (8.12). *)
(* (b) could be stated for subgroups of U wlog -- usage should be checked.   *)
Lemma FTtypeI_II_facts n (H := M`_\F) :
    FTtype M == n -> H ><| U = M ^`(n.-1)%g ->
  if 0 < n <= 2 then
  [/\ (*a*) forall p S, p.-Sylow(U) S -> abelian S /\ ('r(S) <= 2)%N,
      (*b*) forall X, X != set0 -> X \subset U^# -> 'C_H(X) != 1%g ->
            'M('C(X)) = [set M]
    & (*c*) let B := 'A(M) :\: 'A1(M) in B != set0 -> normedTI B G M
  ] else True.
Proof.
move=> typeM defMn; have [n12 | //] := ifP; rewrite -mem_iota !inE in n12.
have defH: H = M`_\sigma.
  by rewrite -def_FTcore -?(Fcore_eq_FTcore _ _) // (eqP typeM) !inE orbA n12.
have [K complU]: exists K : {group gT}, kappa_complement M U K.
  have [[V K] /= complV] := kappa_witness maxM.
  have [[hallV hallK gVK] [_ sUMn _ _ _]] := (complV, sdprod_context defMn).
  have hallU: \sigma_kappa(M)^'.-Hall(M) U.
    rewrite pHallE -(card_Hall hallV) (subset_trans sUMn) ?der_sub //=.
    rewrite -(@eqn_pmul2l #|H|) ?cardG_gt0 // (sdprod_card defMn) defH.
    rewrite (sdprod_card (sdprod_FTder maxM complV)) (eqP typeM).
    by case/pred2P: n12 => ->.
  have [x Mx defU] := Hall_trans (mmax_sol maxM) hallU hallV.
  exists (K :^ x)%G; split; rewrite ?pHallJ // defU -conjsMg.
  by rewrite -(gen_set_id gVK) groupP.
have [part_a _ _ [part_b part_c]] := BGsummaryB maxM complU.
rewrite eqEsubset FTsupp1_sub // andbT -setD_eq0 in part_c.
split=> // X notX0 /subsetD1P[sXU notX1]; rewrite -cent_gen defH.
apply: part_b; rewrite -?subG1 ?gen_subG //.
by rewrite  -setD_eq0 setDE (setIidPl _) // subsetC sub1set inE.
Qed.

(* This is Peterfalvi (8.13). *)
(* We have substituted the B & G notation for the unique maximal supergroup   *)
(* of 'C[x], and specialized the lemma to X := 'A0(M).                        *)
Lemma FTsupport_facts (X := 'A0(M)) (D := [set x in X | ~~('C[x] \subset M)]) :
  [/\ (*a*) {in X &, forall x, {subset x ^: G <= x ^: M}},
      (*b*) D \subset 'A1(M) /\ {in D, forall x, 'M('C[x]) = [set 'N[x]]}
    & (*c*) {in D, forall x (L := 'N[x]) (H := L`_\F),
        [/\ (*c1*) H ><| (M :&: L) = L /\ 'C_H[x] ><| 'C_M[x] = 'C[x],
            (*c2*) {in X, forall y, coprime #|H| #|'C_M[y]| },
            (*c3*) x \in 'A(L) :\: 'A1(L)
          & (*c4*) 1 <= FTtype L <= 2
                /\ (FTtype L == 2 -> [Frobenius M with kernel M`_\F])]}].
Proof.
have defX: X \in pred2 'A(M) 'A0(M) by rewrite !inE eqxx orbT.
have [sDA1 part_a part_c] := BGsummaryII maxM defX.
have{part_a} part_a: {in X &, forall x, {subset x ^: G <= x ^: M}}.
  move=> x y A0x A0y /= /imsetP[g Gg def_y]; rewrite def_y.
  by apply/imsetP/part_a; rewrite -?def_y.
do [split=> //; first split=> //] => x /part_c[_ ] //.
rewrite /= -(mem_iota 1) !inE => -> [-> ? -> -> L2_frob].
by do 2![split=> //] => /L2_frob[E /FrobeniusWker].
Qed.

(* A generic proof of the first assertion of Peterfalvi (8.15). *)
Let norm_FTsuppX A :
  M \subset 'N(A) -> 'A1(M) \subset A -> A \subset 'A0(M) -> 'N(A) = M.
Proof.
move=> nAM sA1A sAA0; apply: mmax_max => //.
rewrite (sub_proper_trans (norm_gen _)) ?mFT_norm_proper //; last first.
  rewrite (sub_proper_trans _ (mmax_proper maxM)) // gen_subG.
  by rewrite (subset_trans sAA0) // (subset_trans (FTsupp0_sub M)) ?subsetDl.
rewrite (subG1_contra (genS sA1A)) //= genD1 ?group1 //.
by rewrite genGid /= def_FTcore ?Msigma_neq1.
Qed.

Lemma norm_FTsupp1 : 'N('A1(M)) = M.
Proof. exact: norm_FTsuppX (FTsupp1_norm M) _ (FTsupp1_sub0 maxM). Qed.

Lemma norm_FTsupp : 'N('A(M)) = M.
Proof. exact: norm_FTsuppX (FTsupp_norm M) (FTsupp1_sub _) (FTsupp_sub0 M). Qed.

Lemma norm_FTsupp0 : 'N('A0(M)) = M.
Proof. exact: norm_FTsuppX (FTsupp0_norm M) (FTsupp1_sub0 _) _. Qed.

Lemma FTsignalizerJ x y : 'R_(M :^ x) (y ^ x) :=: 'R_M y :^ x.
Proof.
rewrite /'R__ /= {1}cent1J conjSg; case: ifP => _ /=; first by rewrite conjs1g.
by rewrite cent1J FT_signalizer_baseJ FcoreJ -conjIg.
Qed.

Let is_FTsignalizer : is_Dade_signalizer G M 'A0(M) 'R_M.
Proof.
rewrite /'R_M => x A0x /=; rewrite setTI.
case: ifPn => [sCxM | not_sCxM]; first by rewrite sdprod1g (setIidPr sCxM).
by have [_ _ /(_ x)[| [] //]] := FTsupport_facts; exact/setIdP.
Qed.

(* This is Peterfalvi (8.15), second assertion. *)
Lemma FT_Dade0_hyp : Dade_hypothesis G M 'A0(M).
Proof.
have [part_a _ parts_bc] := FTsupport_facts.
have /subsetD1P[sA0M notA0_1] := FTsupp0_sub M.
split; rewrite // /normal ?sA0M ?norm_FTsupp0 //=.
exists 'R_M => [|x y A0x A0y]; first exact: is_FTsignalizer.
rewrite /'R_M; case: ifPn => [_ | not_sCxM]; first by rewrite cards1 coprime1n.
rewrite (coprimeSg (subsetIl _ _)) //=.
by have [| _ -> //] := parts_bc x; apply/setIdP.
Qed.

Definition FT_Dade_hyp :=
  restr_Dade_hyp FT_Dade0_hyp (FTsupp_sub0 M) (FTsupp_norm M).

Definition FT_Dade1_hyp :=
  restr_Dade_hyp FT_Dade0_hyp (FTsupp1_sub0 maxM) (FTsupp1_norm M).

Definition FT_DadeF_hyp :=
  restr_Dade_hyp FT_Dade0_hyp (Fcore_sub_FTsupp0 maxM) (normsD1 (gFnorm _ _)).

Lemma def_FTsignalizer0 : {in 'A0(M), Dade_signalizer FT_Dade0_hyp =1 'R_M}.
Proof. exact: def_Dade_signalizer. Qed.

Lemma def_FTsignalizer : {in 'A(M), Dade_signalizer FT_Dade_hyp =1 'R_M}.
Proof. exact: restr_Dade_signalizer def_FTsignalizer0. Qed.

Lemma def_FTsignalizer1 : {in 'A1(M), Dade_signalizer FT_Dade1_hyp =1 'R_M}.
Proof. exact: restr_Dade_signalizer def_FTsignalizer0. Qed.

Lemma def_FTsignalizerF : {in M`_\F^#, Dade_signalizer FT_DadeF_hyp =1 'R_M}.
Proof. exact: restr_Dade_signalizer def_FTsignalizer0. Qed.

Local Notation tau := (Dade FT_Dade0_hyp).
Local Notation FT_Dade := (Dade FT_Dade_hyp).
Local Notation FT_Dade1 := (Dade FT_Dade1_hyp).
Local Notation FT_DadeF := (Dade FT_DadeF_hyp).

Lemma FT_DadeE : {in 'CF(M, 'A(M)), FT_Dade =1 tau}.
Proof. exact: restr_DadeE. Qed.

Lemma FT_Dade1E : {in 'CF(M, 'A1(M)), FT_Dade1 =1 tau}.
Proof. exact: restr_DadeE. Qed.

Lemma FT_DadeF_E : {in 'CF(M, M`_\F^#), FT_DadeF =1 tau}.
Proof. exact: restr_DadeE. Qed.

Lemma FT_Dade_supportS A B : A \subset B -> 'A~(M, A) \subset 'A~(M, B).
Proof.
by move/subsetP=> sAB; apply/bigcupsP=> x Ax; rewrite (bigcup_max x) ?sAB.
Qed.

Lemma FT_Dade0_supportE : Dade_support FT_Dade0_hyp = 'A0~(M).
Proof. by apply/eq_bigr=> x /def_FTsignalizer0 <-. Qed.

Let defA A (sAA0 : A \subset 'A0(M)) (nAM : M \subset 'N(A)) :
  Dade_support (restr_Dade_hyp FT_Dade0_hyp sAA0 nAM) = 'A~(M, A).
Proof.
by apply/eq_bigr=> x /(restr_Dade_signalizer sAA0 nAM def_FTsignalizer0) <-.
Qed.

Lemma FT_Dade_supportE : Dade_support FT_Dade_hyp = 'A~(M).
Proof. exact: defA. Qed.

Lemma FT_Dade1_supportE : Dade_support FT_Dade1_hyp = 'A1~(M).
Proof. exact: defA. Qed.

Lemma FT_DadeF_supportE : Dade_support FT_DadeF_hyp = 'A~(M, M`_\F^#).
Proof. exact: defA. Qed.

Lemma FT_Dade0_supportJ x : 'A0~(M :^ x) = 'A0~(M).
Proof.
rewrite /'A0~(_) FTsupp0J big_imset /=; last exact: in2W (conjg_inj x).
apply: eq_bigr => y _; rewrite FTsignalizerJ -conjg_set1 -conjsMg.
by rewrite class_supportGidl ?inE.
Qed.

Lemma FT_Dade1_supportJ x : 'A1~(M :^ x) = 'A1~(M).
Proof.
rewrite /'A1~(_) FTsupp1J big_imset /=; last exact: in2W (conjg_inj x).
apply: eq_bigr => y _; rewrite FTsignalizerJ -conjg_set1 -conjsMg.
by rewrite class_supportGidl ?inE.
Qed.

Lemma FT_Dade_supportJ x : 'A~(M :^ x) = 'A~(M).
Proof.
rewrite /'A~(_) FTsuppJ big_imset /=; last exact: in2W (conjg_inj x).
apply: eq_bigr => y _; rewrite FTsignalizerJ -conjg_set1 -conjsMg.
by rewrite class_supportGidl ?inE.
Qed.

(* Subcoherence and cyclicTI properties of type II-V subgroups. *)
Hypotheses (defW : W1 \x W2 = W) (MtypeP : of_typeP M U defW).
Let H := M`_\F%G.
Let K := M^`(1)%G.

Lemma FT_cyclicTI_hyp : cyclicTI_hypothesis G defW.
Proof. by case/typeP_context: MtypeP. Qed.
Let ctiW := FT_cyclicTI_hyp.

(* This is a useful combination of Peterfalvi (8.8) and (8.9). *)
Lemma FTtypeP_pair_witness :
  exists2 T, typeP_pair M T defW
     & exists xdefW : W2 \x W1 = W, exists V : {group gT}, of_typeP T V xdefW.
Proof.
have Mtype'1 := FTtypeP_neq1 maxM MtypeP.
case: FTtypeP_pair_cases => [/(_ M maxM)/idPn[] // | [S [T]]].
case=> _ Wx W1x W2x defWx pairST.
without loss /imsetP[y2 _ defSy]: S T W1x W2x defWx pairST / gval M \in S :^: G.
  have [_ _ _ _ coverST] := pairST => IH.
  have /setUP[] := coverST M maxM Mtype'1; first exact: IH pairST.
  by apply: IH (typeP_pair_sym _ pairST); rewrite dprodC.
have [U_S StypeP] := typeP_pairW pairST.
have [[_ maxS maxT] [defS defT defST] b2 b3 b4] := pairST.
have [[[_ _ _ defM] _ _ _ _] defW2] := (MtypeP, typeP_cent_compl MtypeP).
have /imsetP[y1 Sy1 /(canRL (conjsgKV _)) defW1]: W1 :^ y2^-1 \in W1x :^: S.
  apply: (of_typeP_compl_conj StypeP).
  by rewrite -(conjsgK y2 S) -defSy derJ -sdprodJ defM.
pose y := (y1 * y2)%g; rewrite -conjsgM -/y in defW1.
have{defSy} defSy: S :^ y = M by rewrite conjsgM (conjGid Sy1).
have{defW2} defW2: W2 :=: W2x :^ y.
  by rewrite -(typeP_cent_compl StypeP) conjIg -derJ -centJ defSy -defW1.
suffices pairMTy: typeP_pair M (T :^ y) defW.
  exists (T :^ y)%G => //; have xdefW: W2 \x W1 = W by rewrite dprodC.
  by exists xdefW; apply: typeP_pairW (typeP_pair_sym xdefW pairMTy).
do [split; rewrite ?defM -?defSy ?mmaxJ ?FTtypeJ //] => [|L maxL /(b4 L maxL)].
  by rewrite -defW defW1 defW2 derJ -sdprodJ -dprodJ -conjIg defT defST defWx.
by rewrite !conjugates_conj lcoset_id // inE.
Qed.

(* A converse to the above. *)
Lemma of_typeP_pair (xdefW : W2 \x W1 = W) T V :
  T \in 'M -> of_typeP T V xdefW -> typeP_pair M T defW.
Proof.
have [S pairMS [xdefW' [V1 StypeP]]] := FTtypeP_pair_witness => maxT TtypeP.
have [[cycW2 /andP[sW2T _] ntW2 _] _ _ [cycW1 _ _ sW1T'' _] _] := TtypeP.
have{sW1T'' sW2T} sWT: W \subset T.
  by rewrite -(dprodW defW) mul_subG ?(subset_trans sW1T'') ?gFsub.
have [cycW _ /and3P[_ _ /eqP defNW]] := ctiW.
rewrite (@group_inj _ T S) //; have{pairMS} [_ _ _ _ defT] := pairMS.
have /defT/setUP[] := FTtypeP_neq1 maxT TtypeP => {defT}// /imsetP[x _ defT].
  have [defWx] := conj_of_typeP MtypeP x; rewrite -defT.
  case/(of_typeP_conj TtypeP)=> y [_ _ _ defW1y _].
  have /idP[]:= negbF cycW; rewrite (cyclic_dprod defW) // /coprime.
  by rewrite -(cardJg _ y) defW1y cardJg gcdnn -trivg_card1.
have [defWx] := conj_of_typeP StypeP x; rewrite -defT.
case/(of_typeP_conj TtypeP)=> y [Ty _ defW2y defW1y defWy].
have Wyx: (y * x^-1)%g \in W.
  by rewrite -defNW !inE /= conjDg conjUg !conjsgM defW2y defW1y defWy !conjsgK.
by rewrite -(conjGid (subsetP sWT _ Wyx)) conjsgM (conjGid Ty) defT conjsgK.
Qed.

Lemma FT_primeTI_hyp : primeTI_hypothesis M K defW.
Proof.
have [[cycW1 ntW1 hallW1 defM] _ _ [cycW2 ntW2 _ sW2M'' prM'W1] _] := MtypeP.
by split; rewrite ?mFT_odd // (subset_trans sW2M'') ?der_subS.
Qed.
Let ptiWM := FT_primeTI_hyp.

Lemma FTtypeP_supp0_def :
  'A0(M) = 'A(M) :|: class_support (cyclicTIset defW) M.
Proof.
rewrite -(setID 'A0(M) 'A(M)) (FTsupp0_typeP maxM MtypeP) (setIidPr _) //.
exact: FTsupp_sub0.
Qed.

Fact FT_Fcore_prime_Dade_def : prime_Dade_definition M K H 'A(M) 'A0(M) defW.
Proof.
have [_ [_ _ _ /sdprodW/mulG_sub[sHK _]] _ [_ _ sW2H _ _] _] := MtypeP.
split; rewrite ?gFnormal //; last exact: FTtypeP_supp0_def.
rewrite /normal FTsupp_norm andbT /'A(M) (FTtypeP_neq1 maxM MtypeP) /=.
do ?split=> //; apply/bigcupsP=> x A1x; last by rewrite setSD ?subsetIl.
  by rewrite setDE -setIA subIset // gFsub.
by rewrite (bigcup_max x) // (subsetP _ x A1x) // setSD ?Fcore_sub_FTcore.
Qed.

Definition FT_prDade_hypF : prime_Dade_hypothesis _ M K H 'A(M) 'A0(M) defW :=
  PrimeDadeHypothesis ctiW ptiWM FT_Dade0_hyp FT_Fcore_prime_Dade_def.

Fact FT_core_prime_Dade_def : prime_Dade_definition M K M`_\s 'A(M) 'A0(M) defW.
Proof.
have [[_ sW2H sHK] [nsAM sCA sAK] defA0] := FT_Fcore_prime_Dade_def.
have [_ [_ sW2K _ _] _] := ptiWM.
split=> //=; first by rewrite FTcore_normal /M`_\s; case: ifP.
rewrite nsAM /= /'A(M) /M`_\s (FTtypeP_neq1 maxM MtypeP); split=> //=.
by apply/bigcupsP=> x _; rewrite setSD ?subsetIl.
Qed.

Definition FT_prDade_hyp : prime_Dade_hypothesis _ M K M`_\s 'A(M) 'A0(M) defW
  := PrimeDadeHypothesis ctiW ptiWM FT_Dade0_hyp FT_core_prime_Dade_def.

Let calS := seqIndD K M M`_\s 1.

Fact FTtypeP_cohererence_base_subproof : cfConjC_subset calS calS.
Proof. exact: seqInd_conjC_subset1. Qed.

Fact FTtypeP_cohererence_nonreal_subproof : ~~ has cfReal calS.
Proof. by rewrite seqInd_notReal ?mFT_odd ?FTcore_sub_der1 ?der_normal. Qed.

Definition FTtypeP_coh_base_sig :=
  prDade_subcoherent FT_prDade_hyp
    FTtypeP_cohererence_base_subproof FTtypeP_cohererence_nonreal_subproof.

Definition FTtypeP_coh_base := sval FTtypeP_coh_base_sig.

Local Notation R := FTtypeP_coh_base.

Lemma FTtypeP_subcoherent : subcoherent calS tau R.
Proof. by rewrite /R; case: FTtypeP_coh_base_sig => R1 []. Qed.
Let scohS := FTtypeP_subcoherent.

Let w_ i j := cyclicTIirr defW i j.
Let sigma := cyclicTIiso ctiW.
Let eta_ i j := sigma (w_ i j).
Let mu_ := primeTIred ptiWM.
Let delta_ := fun j => primeTIsign ptiWM j.

Lemma FTtypeP_base_ortho :
  {in [predI calS & irr M] & irr W, forall phi w, orthogonal (R phi) (sigma w)}.
Proof. by rewrite /R; case: FTtypeP_coh_base_sig => R1 []. Qed.

Lemma FTtypeP_base_TIred :
  let dsw j k := [seq delta_ j *: eta_ i k | i : Iirr W1] in
  let Rmu j := dsw j j ++ map -%R (dsw j (conjC_Iirr j)) in
  forall j, R (mu_ j) = Rmu j.
Proof. by rewrite /R; case: FTtypeP_coh_base_sig => R1 []. Qed.

Lemma coherent_ortho_cycTIiso calS1 (tau1 : {additive 'CF(M) -> 'CF(G)}) :
    cfConjC_subset calS1 calS -> coherent_with calS1 M^# tau tau1 ->
  forall chi i j, chi \in calS1 -> chi \in irr M -> '[tau1 chi, eta_ i j] = 0.
Proof.
move=> ccsS1S cohS1 chi i j S1chi chi_irr; have [_ sS1S _] := ccsS1S.
have [e /mem_subseq Re ->] := mem_coherent_sum_subseq scohS ccsS1S cohS1 S1chi.
rewrite cfdot_suml big1_seq // => xi /Re; apply: orthoPr.
by apply: FTtypeP_base_ortho (mem_irr _); rewrite !inE sS1S.
Qed.

Import ssrnum Num.Theory.

(* A reformuation of Peterfalvi (5.8) for the Odd Order proof context. *)
Lemma FTtypeP_coherent_TIred calS1 tau1 zeta j :
    cfConjC_subset calS1 calS -> coherent_with calS1 M^# tau tau1 ->
    zeta \in irr M -> zeta \in calS1 -> mu_ j \in calS1 ->
    let d := primeTI_Isign ptiWM j in let k := conjC_Iirr j in
  {dk : bool * Iirr W2 | tau1 (mu_ j) = (-1) ^+ dk.1 *: (\sum_i eta_ i dk.2)
    &   dk.1 = d /\ dk.2 = j
    \/  [/\ dk.1 = ~~ d, dk.2 = k
        & forall l, mu_ l \in calS1 -> mu_ l 1%g = mu_ j 1%g -> pred2 j k l]}.
Proof.
move=> ccsS1S cohS1 irr_zeta S1zeta S1mu_j d k.
have irrS1: [/\ ~~ has cfReal calS1, has (mem (irr M)) calS1 & mu_ j \in calS1].
  have [[_ -> _] _ _ _ _] := subset_subcoherent scohS ccsS1S.
  by split=> //; apply/hasP; exists zeta.
have Dmu := coherent_prDade_TIred FT_prDade_hyp ccsS1S irrS1 cohS1.
rewrite -/mu_ -/d in Dmu; pose mu_sum d1 k1 := (-1) ^+ d1 *: (\sum_i eta_ i k1).
have mu_sumK (d1 d2 : bool) k1 k2:
  ('[mu_sum d1 k1, (-1) ^+ d2 *: eta_ 0 k2] > 0) = (d1 == d2) && (k1 == k2).
- rewrite cfdotZl cfdotZr rmorph_sign mulrA -signr_addb cfdot_suml.
  rewrite (bigD1 0) //= cfdot_cycTIiso !eqxx big1 => [|i nz_i]; last first.
    by rewrite cfdot_cycTIiso (negPf nz_i).
  rewrite addr0 /= andbC; case: (k1 == k2); rewrite ?mulr0 ?ltrr //=.
  by rewrite mulr1 signr_gt0 negb_add.
have [dk tau1mu_j]: {dk : bool * Iirr W2 | tau1 (mu_ j) = mu_sum dk.1 dk.2}.
  apply: sig_eqW; case: Dmu => [-> | [-> _]]; first by exists (d, j).
  by exists (~~ d, k); rewrite -signrN.
exists dk => //; have:= mu_sumK dk.1 dk.1 dk.2 dk.2; rewrite !eqxx -tau1mu_j.
case: Dmu => [-> | [-> all_jk]];
  rewrite -?signrN mu_sumK => /andP[/eqP <- /eqP <-]; [by left | right].
by split=> // j1 S1j1 /(all_jk j1 S1j1)/pred2P.
Qed.

Lemma size_red_subseq_seqInd_typeP (calX : {set Iirr K}) calS1 :
    uniq calS1 -> {subset calS1 <= seqInd M calX} ->
    {subset calS1 <= [predC irr M]} ->
  size calS1 = #|[set i : Iirr K | 'Ind 'chi_i \in calS1]|.
Proof.
move=> uS1 sS1S redS1; pose h s := 'Ind[M, K] 'chi_s.
apply/eqP; rewrite cardE -(size_map h) -uniq_size_uniq // => [|xi]; last first.
  apply/imageP/idP=> [[i] | S1xi]; first by rewrite inE => ? ->.
  by have /seqIndP[s _ Dxi] := sS1S _ S1xi; exists s; rewrite ?inE -?Dxi.
apply/dinjectiveP; pose h1 xi := cfIirr (#|W1|%:R^-1 *: 'Res[K, M] xi).
apply: can_in_inj (h1) _ => s; rewrite inE => /redS1 red_s.
have cycW1: cyclic W1 by have [[]] := MtypeP.
have [[j /irr_inj->] | [/idPn[]//]] := prTIres_irr_cases ptiWM s.
by rewrite /h cfInd_prTIres /h1 cfRes_prTIred scalerK ?neq0CG ?irrK.
Qed.

End OneMaximal.

(* This is Peterfalvi (8.16). *)
Lemma FTtypeII_ker_TI M :
   M \in 'M -> FTtype M == 2 ->
 [/\ normedTI 'A0(M) G M, normedTI 'A(M) G M & normedTI 'A1(M) G M].
Proof.
move=> maxM typeM; have [sA1A sAA0] := (FTsupp1_sub maxM, FTsupp_sub0 M).
have [sA10 sA0M] := (subset_trans sA1A sAA0, FTsupp0_sub M).
have nzA1: 'A1(M) != set0 by rewrite setD_eq0 def_FTcore ?subG1 ?Msigma_neq1.
have [nzA nzA0] := (subset_neq0 sA1A nzA1, subset_neq0 sA10 nzA1).
suffices nTI_A0: normedTI 'A0(M) G M.
  by rewrite nTI_A0 !(normedTI_S _ _ _ nTI_A0) // ?FTsupp_norm ?FTsupp1_norm.
have [U W W1 W2 defW [[MtypeP _ _ tiFM] _ _ _ _]] := FTtypeP 2 maxM typeM.
apply/(Dade_normedTI_P (FT_Dade0_hyp maxM)); split=> // x A0x.
rewrite /= def_FTsignalizer0 /'R_M //=; have [// | not_sCxM] := ifPn.
have [y cxy /negP[]] := subsetPn not_sCxM.
apply: subsetP cxy; rewrite -['C[x]]setTI (cent1_normedTI tiFM) //.
have /setD1P[ntx Ms_x]: x \in 'A1(M).
  by have [_ [/subsetP-> // ]] := FTsupport_facts maxM; apply/setIdP.
rewrite !inE ntx (subsetP (Fcore_sub_Fitting M)) //.
by rewrite (Fcore_eq_FTcore _ _) ?(eqP typeM).
Qed.

(* This is Peterfalvi, Theorem (8.17). *)
Theorem FT_Dade_support_partition :
  [/\ (*a1*)
           \pi(G) =i [pred p | [exists M : {group gT} in 'M, p \in \pi(M`_\s)]],
      (*a2*) {in 'M &, forall M L,
                gval L \notin M :^: G -> coprime #|M`_\s| #|L`_\s| },
      (*b*) {in 'M, forall M, #|'A1~(M)| = (#|M`_\s|.-1 * #|G : M|)%N}
    & (*c*) let PG := [set 'A1~(Mi) | Mi : {group gT} in 'M^G] in
       [/\ {in 'M^G &, injective (fun M => 'A1~(M))},
           all_FTtype1 -> partition PG G^#
         & forall S T W W1 W2 (defW : W1 \x W2 = W),
             let VG := class_support (cyclicTIset defW) G in
           typeP_pair S T defW -> partition (VG |: PG) G^# /\ VG \notin PG]].
Proof.
have defDsup M: M \in 'M -> class_support M^~~ G = 'A1~(M).
  move=> maxM; rewrite class_supportEr /'A1~(M) /'A1(M) def_FTcore //.
  rewrite -(eq_bigr _ (fun _ _ => bigcupJ _ _ _ _)) exchange_big /=.
  apply: eq_bigr => x Ms_x; rewrite -class_supportEr.
  rewrite -norm_rlcoset ?(subsetP (cent_sub _)) ?cent_FT_signalizer //=.
  congr (class_support (_ :* x) G); rewrite /'R_M.
  have [_ _ /(_ x Ms_x)[_ defCx _] /(_ x Ms_x)defNF]:= BGsummaryD maxM.
  have [sCxM | /defNF[[_ <-]] //] := ifPn.
  apply/eqP; rewrite trivg_card1 -(eqn_pmul2r (cardG_gt0 'C_M[x])).
  by rewrite (sdprod_card defCx) mul1n /= (setIidPr _).
have [b [a1 a2] [/and3P[_ _ not_PG_set0] _ _]] := BGsummaryE gT.
split=> [p | M L maxM maxL /a2 | M maxM | {b a1 a2}PG].
- apply/idP/exists_inP=> [/a1[M maxM sMp] | [M _]].
    by exists M => //; rewrite def_FTcore // pi_Msigma.
  exact: piSg (subsetT _) p.
- move/(_ maxM maxL)=> coML; rewrite coprime_pi' // !def_FTcore //.
  apply: sub_pgroup (pcore_pgroup _ L) => p; apply/implyP.
  by rewrite implybN /= pi_Msigma // implybE -negb_and [_ && _]coML.
- by rewrite -defDsup // def_FTcore // b.
have [/subsetP sMG_M _ injMG sM_MG] := mmax_transversalP gT.
have{PG} ->: PG = [set class_support M^~~ G | M : {group gT} in 'M].
  apply/setP=> AG; apply/imsetP/imsetP=> [] [M maxM ->].
    by move/sMG_M in maxM; exists M; rewrite ?defDsup //.
  have [x MG_Mx] := sM_MG M maxM.
  by exists (M :^ x)%G; rewrite // defDsup ?mmaxJ ?FT_Dade1_supportJ.
have [c1 c2] := mFT_partition gT.
split=> [M H maxM maxH eq_MH | Gtype1 | S T W W1 W2 defW VG pairST].
- apply: injMG => //; move/sMG_M in maxM; move/sMG_M in maxH.
  apply/orbit_transl/idPn => not_HG_M.
  have /negP[]: ~~ [disjoint 'A1~(M) & 'A1~(H)].
   rewrite eq_MH -setI_eq0 setIid -defDsup //.
   by apply: contraNneq not_PG_set0 => <-; exact: mem_imset.
  rewrite -!defDsup // -setI_eq0 class_supportEr big_distrl -subset0.
  apply/bigcupsP=> x /class_supportGidr <- /=; rewrite -conjIg sub_conjg conj0g.
  rewrite class_supportEr big_distrr /=; apply/bigcupsP=> {x}x _.
  rewrite subset0 setI_eq0 -sigma_supportJ sigma_support_disjoint ?mmaxJ //.
  by rewrite (orbit_transr _ (mem_orbit _ _ _)) ?in_setT // orbit_sym.
- rewrite c1 // setD_eq0; apply/subsetP=> M maxM.
  by rewrite FTtype_Fmax ?(forall_inP Gtype1).
have [[[cycW maxS _] _ _ _ _] [U_S StypeP]] := (pairST, typeP_pairW pairST).
have Stype'1 := FTtypeP_neq1 maxS StypeP.
have maxP_S: S \in TypeP_maxgroups _ by rewrite FTtype_Pmax.
have hallW1: \kappa(S).-Hall(S) W1.
  have [[U1 K] /= complU1] := kappa_witness maxS.
  have ntK: K :!=: 1%g by rewrite -(trivgPmax maxS complU1).
  have [[defS_K _ _] [//|defS' _] _ _ _] := kappa_structure maxS complU1.
  rewrite {}defS' in defS_K.
  have /imsetP[x Sx defK] := of_typeP_compl_conj StypeP defS_K.
  by have [_ hallK _] := complU1; rewrite defK pHallJ in hallK.
have{cycW} [[ntW1 ntW2] [cycW _ _]] := (cycTI_nontrivial cycW, cycW).
suffices defW2: 'C_(S`_\sigma)(W1) = W2.
  by have [] := c2 _ _ maxP_S hallW1; rewrite defW2 /= (dprodWY defW).
have [U1 complU1] := ex_kappa_compl maxS hallW1.
have [[_ [_ _ sW2'F] _] _ _ _] := BGsummaryC maxS complU1 ntW1.
rewrite -(setIidPr sW2'F) setIA (setIidPl (Fcore_sub_Msigma maxS)).
exact: typeP_cent_core_compl StypeP.
Qed.

(* This is Peterfalvi (8.18). Note that part (a) is not actually used later. *)
Lemma FT_Dade_support_disjoint S T :
    S \in 'M -> T \in 'M -> gval T \notin S :^: G ->
  [/\ (*a*) FTsupports S T = ~~ [disjoint 'A1(S) & 'A(T)]
         /\ {in 'A1(S) :&: 'A(T), forall x,
               ~~ ('C[x] \subset S) /\ 'C[x] \subset T},
      (*b*) [exists x, FTsupports S (T :^ x)] = ~~ [disjoint 'A1~(S) & 'A~(T)]
    & (*c*) [disjoint 'A1~(S) & 'A~(T)] \/  [disjoint 'A1~(T) & 'A~(S)]].
Proof.
move: S T; pose NC S T := gval T \notin S :^: G.
have part_a2 S T (maxS : S \in 'M) (maxT : T \in 'M) (ncST : NC S T) :
  {in 'A1(S) :&: 'A(T), forall x, ~~ ('C[x] \subset S) /\ 'C[x] \subset T}.
- move=> x /setIP[/setD1P[ntx Ss_x] ATx].
  have coxTs: coprime #[x] #|T`_\s|.
    apply: (coprime_dvdl (order_dvdG Ss_x)).
    by have [_ ->] := FT_Dade_support_partition.
  have [z /setD1P[ntz Ts_z] /setD1P[_ /setIP[Tn_x czx]]] := bigcupP ATx.
  set n := FTtype T != 1%N in Tn_x.
  have typeT: FTtype T == n.+1.
    have notTs_x: x \notin T`_\s.
      apply: contra ntx => Ts_x.
      by rewrite -order_eq1 -dvdn1 -(eqnP coxTs) dvdn_gcd dvdnn order_dvdG.
    apply: contraLR ATx => typeT; rewrite FTsupp_eq1 // ?inE ?ntx //.
    move: (FTtype_range T) typeT; rewrite -mem_iota /n.
    by do 5!case/predU1P=> [-> // | ].
  have defTs: T`_\s = T`_\F.
    by apply/esym/Fcore_eq_FTcore; rewrite // (eqP typeT); case n.
  have [U Ux defTn]: exists2 U : {group gT}, x \in U & T`_\F ><| U = T^`(n)%g.
    have [[U K] /= complU] := kappa_witness maxT.
    have defTn: T`_\s ><| U = T^`(n)%g.
      by rewrite def_FTcore // (sdprod_FTder maxT complU).
    have nsTsTn: T`_\s <| T^`(n)%g by case/sdprod_context: defTn.
    have [sTsTn nTsTn] := andP nsTsTn.
    have hallTs: \pi(T`_\s).-Hall(T^`(n)%g) T`_\s.
      by rewrite defTs (pHall_subl _ (der_sub n T) (Fcore_Hall T)) //= -defTs.
    have hallU: \pi(T`_\s)^'.-Hall(T^`(n)%g) U.
      by apply/sdprod_Hall_pcoreP; rewrite /= (normal_Hall_pcore hallTs).
    have solTn: solvable T^`(n)%g := solvableS (der_sub n T) (mmax_sol maxT).
    rewrite coprime_sym coprime_pi' // in coxTs.
    have [|y Tn_y] := Hall_subJ solTn hallU _ coxTs; rewrite cycle_subG //.
    exists (U :^ y)%G; rewrite // -defTs.
    by rewrite -(normsP nTsTn y Tn_y) -sdprodJ defTn conjGid.
  have uniqCx: 'M('C[x]) = [set T].
    have:= FTtypeI_II_facts maxT typeT defTn; rewrite !ltnS leq_b1 -cent_set1.
    case=> _ -> //; first by rewrite -cards_eq0 cards1.
      by rewrite sub1set !inE ntx.
    by apply/trivgPn; exists z; rewrite //= -defTs inE Ts_z cent_set1 cent1C.
  split; last by case/mem_uniq_mmax: uniqCx.
  by apply: contra ncST => /(eq_uniq_mmax uniqCx maxS)->; exact: orbit_refl.
have part_a1 S T (maxS : S \in 'M) (maxT : T \in 'M) (ncST : NC S T) :
  FTsupports S T = ~~ [disjoint 'A1(S) & 'A(T)].
- apply/existsP/pred0Pn=> [[x /and3P[ASx not_sCxS sCxT]] | [x /andP[A1Sx Atx]]].
    have [_ [/subsetP]] := FTsupport_facts maxS; set D := finset _.
    have Dx: x \in D by rewrite !inE ASx.
    move=> /(_ x Dx) A1x /(_ x Dx)uniqCx /(_ x Dx)[_ _ /setDP[ATx _] _].
    by rewrite (eq_uniq_mmax uniqCx maxT sCxT); exists x; exact/andP.
  exists x; rewrite (subsetP (FTsupp1_sub maxS)) //=.
  by apply/andP/part_a2=> //; exact/setIP.
have part_b S T (maxS : S \in 'M) (maxT : T \in 'M) (ncST : NC S T) :
  [exists x, FTsupports S (T :^ x)] = ~~ [disjoint 'A1~(S) & 'A~(T)].
- apply/existsP/pred0Pn=> [[x] | [y /andP[/= A1GSy AGTy]]].
    rewrite part_a1 ?mmaxJ // => [/pred0Pn[y /andP/=[A1Sy ATyx]]|]; last first.
      by rewrite /NC -(rcoset_id (in_setT x)) orbit_rcoset.
    rewrite FTsuppJ mem_conjg in ATyx; exists (y ^ x^-1); apply/andP; split.
      by apply/bigcupP; exists y => //; rewrite mem_imset2 ?rcoset_refl ?inE.
    apply/bigcupP; exists (y ^ x^-1) => //.
    by rewrite mem_class_support ?rcoset_refl.
  have{AGTy} [x2 ATx2 x2R_yG] := bigcupP AGTy.
  have [sCx2T | not_sCx2T] := boolP ('C[x2] \subset T); last first.
    have [_ _ _ [injA1G pGI pGP]] := FT_Dade_support_partition.
    have{pGI pGP} tiA1g: trivIset [set 'A1~(M) | M : {group gT} in 'M^G].
      case: FTtypeP_pair_cases => [/forall_inP/pGI/and3P[] // | [M [L]]].
      by case=> _ W W1 W2 defW1 /pGP[]/and3P[_ /(trivIsetS (subsetUr _ _))].
    have [_ _ injMG sM_MG] := mmax_transversalP gT.
    have [_ [sDA1T _] _] := FTsupport_facts maxT.
    have [[z1 maxSz] [z2 maxTz]] := (sM_MG S maxS, sM_MG T maxT).
    case/imsetP: ncST; exists (z1 * z2^-1)%g; first by rewrite inE.
    rewrite conjsgM; apply/(canRL (conjsgK _))/congr_group/injA1G=> //.
    apply/eqP/idPn=> /(trivIsetP tiA1g)/pred0Pn[]; try exact: mem_imset.
    exists y; rewrite !FT_Dade1_supportJ /= A1GSy andbT.
    by apply/bigcupP; exists x2; rewrite // (subsetP sDA1T) ?inE ?ATx2.
  have{x2R_yG} /imsetP[z _ def_y]: y \in x2 ^: G.
    by rewrite /'R_T {}sCx2T mul1g class_support_set1l in x2R_yG.
  have{A1GSy} [x1 A1Sx1] := bigcupP A1GSy; rewrite {y}def_y -mem_conjgV.
  rewrite class_supportGidr ?inE {z}//.
  case/imset2P=> _ z /rcosetP[y Hy ->] _ def_x2.
  exists z^-1%g; rewrite part_a1 ?mmaxJ //; last first.
    by rewrite /NC (orbit_transr _ (mem_orbit _ _ _)) ?inE.
  apply/pred0Pn; exists x1; rewrite /= A1Sx1 FTsuppJ mem_conjgV; apply/bigcupP.
  pose ddS := FT_Dade1_hyp maxS; have [/andP[sA1S _] _ notA1_1 _ _] := ddS.
  have [ntx1 Sx1] := (memPn notA1_1 _ A1Sx1, subsetP sA1S _ A1Sx1).
  have [coHS defCx1] := (Dade_coprime ddS A1Sx1 A1Sx1, Dade_sdprod ddS A1Sx1).
  rewrite def_FTsignalizer1 // in coHS defCx1.
  have[u Ts_u /setD1P[_ cT'ux2]] := bigcupP ATx2.
  exists u => {Ts_u}//; rewrite 2!inE -(conj1g z) (can_eq (conjgK z)) ntx1.
  suffices{u cT'ux2} ->: x1 = (y * x1).`_(\pi('R_S x1)^').
    by rewrite -consttJ -def_x2 groupX.
  have /setIP[_ /cent1P cx1y]: y \in 'C_G[x1].
    by case/sdprod_context: defCx1 => /andP[/subsetP->].
  rewrite consttM // (constt1P _) ?p_eltNK ?(mem_p_elt (pgroup_pi _)) // mul1g.
  have piR'_Cx1: \pi('R_S x1)^'.-group 'C_S[x1] by rewrite coprime_pi' in coHS.
  by rewrite constt_p_elt ?(mem_p_elt piR'_Cx1) // inE Sx1 cent1id.
move=> S T maxS maxT ncST; split; first split; auto.
apply/orP/idPn; rewrite negb_or -part_b // => /andP[suppST /negP[]].
without loss{suppST} suppST: T maxT ncST / FTsupports S T.
  move=> IH; case/existsP: suppST => x /IH {IH}.
  rewrite FT_Dade1_supportJ (orbit_transr _ (mem_orbit _ _ _)) ?in_setT //.
  by rewrite mmaxJ => ->.
have{suppST} [y /and3P[ASy not_sCyS sCyT]] := existsP suppST.
have Dy: y \in [set z in 'A0(S) | ~~ ('C[z] \subset S)] by rewrite !inE ASy.
have [_ [_ /(_ y Dy) uCy]  /(_ y Dy)[_ coTcS _ typeT]] := FTsupport_facts maxS.
rewrite  -mem_iota -(eq_uniq_mmax uCy maxT sCyT) !inE in coTcS typeT.
apply/negbNE; rewrite -part_b /NC 1?orbit_sym // negb_exists.
apply/forallP=> x; rewrite part_a1 ?mmaxJ ?negbK //; last first.
  by rewrite /NC (orbit_transr _ (mem_orbit _ _ _)) ?in_setT // orbit_sym.
rewrite -setI_eq0 -subset0 FTsuppJ -bigcupJ big_distrr; apply/bigcupsP=> z Sxz.
rewrite conjD1g /= -setDIl coprime_TIg ?setDv //= cardJg.
rewrite -(Fcore_eq_FTcore maxT _) ?inE ?orbA; last by have [->] := typeT.
by rewrite (coprimegS _ (coTcS z _)) ?(subsetP (FTsupp1_sub0 _)) ?setSI ?gFsub.
Qed.

(* A corollary to the above, which Peterfalvi derives from (8.17a) (i.e.,     *)
(* FT_Dade_support_partition) in the proof of (12.16).                        *)
Lemma FT_Dade1_support_disjoint S T :
  S \in 'M -> T \in 'M -> gval T \notin S :^: G -> [disjoint 'A1~(S) & 'A1~(T)].
Proof.
move=> maxS maxT /FT_Dade_support_disjoint[] // _ _ tiA1A.
without loss{tiA1A maxT}: S T maxS / [disjoint 'A1~(T) & 'A~(S)].
  by move=> IH_ST; case: tiA1A => /IH_ST; first rewrite disjoint_sym; apply.
by rewrite disjoint_sym; apply/disjoint_trans/FT_Dade_supportS/FTsupp1_sub.
Qed.

End Eight.

Notation FT_Dade0 maxM := (Dade (FT_Dade0_hyp maxM)).
Notation FT_Dade maxM := (Dade (FT_Dade_hyp maxM)).
Notation FT_Dade1 maxM := (Dade (FT_Dade1_hyp maxM)).
Notation FT_DadeF maxM := (Dade (FT_DadeF_hyp maxM)).

