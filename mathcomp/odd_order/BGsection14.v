(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div path fintype.
Require Import bigop finset prime fingroup morphism perm automorphism quotient.
Require Import action gproduct gfunctor pgroup cyclic center commutator.
Require Import gseries nilpotent sylow abelian maximal hall frobenius.
Require Import ssralg ssrnum ssrint rat.
Require Import BGsection1 BGsection3 BGsection4 BGsection5 BGsection6.
Require Import BGsection7 BGsection9 BGsection10 BGsection12 BGsection13.

(******************************************************************************)
(*   This file covers B & G, section 14, starting with the definition of the  *)
(* sigma-decomposition of elements, sigma-supergroups, and basic categories   *)
(* of maximal subgroups:                                                      *)
(* sigma_decomposition x == the set of nontrivial constituents x.`_\sigma(M), *)
(*                          with M ranging over maximal sugroups of G.        *)
(*                          (x is the product of these).                      *)
(*        \ell_\sigma[x] == #|sigma_decomposition x|.                         *)
(*          'M_\sigma(X) == the set of maximal subgroups M such that X is a   *)
(*                          a subset of M`_\sigma.                            *)
(*          'M_\sigma[x] := 'M_\sigma(<[x]>)                                  *)
(*             \kappa(M) == the set of primes p in \tau1(M) or \tau3(M), such *)
(*                          that 'C_(M`_\sigma)(P) != 1 for some subgroup of  *)
(*                          M of order p, i.e., the primes for which M fails  *)
(*                          to be a Frobenius group.                          *)
(*  kappa_complement M U K <-> U and K are respectively {kappa, sigma}'- and  *)
(*                          kappa-Hall subgroups of M, whose product is a     *)
(*                          sigma-complement of M. This corresponds to the    *)
(*                          notation introduced at the start of section 15 in *)
(*                          B & G, but is needed here to capture the use of   *)
(*                          bound variables of 14.2(a) in the statement of    *)
(*                          Lemma 14.12.                                      *)
(*                 'M_'F == the set of maximal groups M for which \kappa(M)   *)
(*                          is empty, i.e., the maximal groups of Frobenius   *)
(*                          type (in the final classification, this becomes   *)
(*                          Type I).                                          *)
(*                 'M_'P == the complement to 'M_'F in 'M, i.e., the set of M *)
(*                          for which at least E1 has a proper prime action   *)
(*                          on M`_\sigma.                                     *)
(*                'M_'P1 == the set of maximal subgroups M such that \pi(M)   *)
(*                          is the disjoint union of \sigma(M) and \kappa(M), *)
(*                          i.e., for which the entire complement acts in a   *)
(*                          prime manner (this troublesome subset of 'M_'P is *)
(*                          ultimately refined into Types III-V in the final  *)
(*                          classification).                                  *)
(*                'M_'P2 == the complement to 'M_'P1 in 'M_'P; this becomes   *)
(*                          Type II in the final classification.              *)
(*                 'N[x] == if x != 1 and 'M_\sigma[x] > 1, the unique group  *)
(*                          in 'M('C[x]) (see B & G, Theorem 14.4), and the   *)
(*                          trivial group otherwise.                          *)
(*                 'R[x] := 'C_('N[x]`_\sigma)[x]; if \ell_\sigma[x] == 1,    *)
(*                          this is the normal Hall subgroup of 'C[x] that    *)
(*                          acts sharply transitively by conjugagtion on      *)
(*                          'M`_\sigma[x] (again, by Theorem 14.4).           *)
(*                  M^~~ == the union of all the cosets x *: 'R[x], with x    *)
(*                          ranging over (M`_\sigma)^#. This will become the  *)
(*                          support set for the Dade isometry for M in the    *)
(*                          character theory part of the proof.               *)
(* It seems 'R[x] and 'N[x]`_\sigma play a somewhat the role of a signalizer  *)
(* functor in the FT proof; in particular 'R[x] will be used to construct the *)
(* Dade isometry in the character theory part of the proof.                   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope nat_scope.
Import GRing.Theory Num.Theory GroupScope.

Section Definitons.

Variable gT : minSimpleOddGroupType.
Implicit Type x : gT.
Implicit Type M X : {set gT}.

Definition sigma_decomposition x :=
  [set x.`_\sigma(M) | M : {group gT} in 'M]^#.
Definition sigma_length x := #|sigma_decomposition x|.

Definition sigma_mmax_of X := [set M in 'M | X \subset M`_\sigma].

Definition FT_signalizer_base x :=
  if #|sigma_mmax_of <[x]>| > 1 then odflt 1%G (pick (mem 'M('C[x]))) else 1%G.

Definition FT_signalizer x := 'C_((FT_signalizer_base x)`_\sigma)[x].

Definition sigma_cover M := \bigcup_(x in (M`_\sigma)^#) x *: FT_signalizer x.

Definition tau13 M := [predU \tau1(M) & \tau3(M)].

Fact kappa_key : unit. Proof. by []. Qed.
Definition kappa_def M : nat_pred :=
  [pred p in tau13 M | [exists P in 'E_p^1(M), 'C_(M`_\sigma)(P) != 1]].
Definition kappa := locked_with kappa_key kappa_def.
Canonical kappa_unlockable := [unlockable fun kappa].

Definition sigma_kappa M := [predU \sigma(M) & kappa M].

Definition kappa_complement (M U K : {set gT}) :=
  [/\ (sigma_kappa M)^'.-Hall(M) U, (kappa M).-Hall(M) K & group_set (U * K)].

Definition TypeF_maxgroups := [set M in 'M | (kappa M)^'.-group M].

Definition TypeP_maxgroups := 'M :\: TypeF_maxgroups.

Definition TypeP1_maxgroups :=
  [set M in TypeP_maxgroups | (sigma_kappa M).-group M].

Definition TypeP2_maxgroups := TypeP_maxgroups :\: TypeP1_maxgroups.

End Definitons.

Notation "\ell_ \sigma ( x )" := (sigma_length x)
  (at level 8, format "\ell_ \sigma ( x )") : group_scope.

Notation "''M_' \sigma ( X )" := (sigma_mmax_of X)
  (at level 8, format "''M_' \sigma ( X )") : group_scope.

Notation "''M_' \sigma [ x ]" := (sigma_mmax_of <[x]>)
  (at level 8, format "''M_' \sigma [ x ]") : group_scope.

Notation "''N' [ x ]" := (FT_signalizer_base x)
  (at level 8, format "''N' [ x ]") : group_scope.

Notation "''R' [ x ]" := (FT_signalizer x)
  (at level 8, format "''R' [ x ]") : group_scope.

Notation "M ^~~" := (sigma_cover M)
  (at level 2, format "M ^~~") : group_scope.

Notation "\tau13 ( M )" := (tau13 M)
  (at level 8, format "\tau13 ( M )") : group_scope.

Notation "\kappa ( M )" := (kappa M)
  (at level 8, format "\kappa ( M )") : group_scope.

Notation "\sigma_kappa ( M )" := (sigma_kappa M)
  (at level 8, format "\sigma_kappa ( M )") : group_scope.

Notation "''M_' ''F'" := (TypeF_maxgroups _)
  (at level 2, format "''M_' ''F'") : group_scope.

Notation "''M_' ''P'" := (TypeP_maxgroups _)
  (at level 2, format "''M_' ''P'") : group_scope.

Notation "''M_' ''P1'" := (TypeP1_maxgroups _)
  (at level 2, format "''M_' ''P1'") : group_scope.

Notation "''M_' ''P2'" := (TypeP2_maxgroups _)
  (at level 2, format "''M_' ''P2'") : group_scope.

Section Section14.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).
Implicit Types p q q_star r : nat.
Implicit Types x y z : gT.
Implicit Types A E H K L M Mstar N P Q Qstar R S T U V W X Y Z : {group gT}.

(* Basic properties of the sigma decomposition. *)
Lemma mem_sigma_decomposition x M (xM := x.`_\sigma(M)) :
  M \in 'M -> xM != 1 -> xM \in sigma_decomposition x.
Proof. by move=> maxM nt_xM; rewrite !inE nt_xM; apply: mem_imset. Qed.

Lemma sigma_decompositionJ x z :
  sigma_decomposition (x ^ z) = sigma_decomposition x :^ z.
Proof.
rewrite conjD1g  -[_ :^ z]imset_comp; congr _^#.
by apply: eq_in_imset => M maxM; rewrite /= consttJ.
Qed.

Lemma ell_sigmaJ x z : \ell_\sigma(x ^ z) = \ell_\sigma(x).
Proof. by rewrite /sigma_length sigma_decompositionJ cardJg. Qed.

Lemma sigma_mmaxJ M (X : {set gT}) z :
  ((M :^ z)%G \in 'M_\sigma(X :^ z)) = (M \in 'M_\sigma(X)).
Proof. by rewrite inE mmaxJ MsigmaJ conjSg !inE. Qed.

Lemma card_sigma_mmaxJ (X : {set gT}) z :
  #|'M_\sigma(X :^ z)| = #|'M_\sigma(X)|.
Proof.
rewrite -(card_setact 'JG _ z^-1) setactVin ?inE //.
by apply: eq_card => M; rewrite inE sigma_mmaxJ.
Qed.

Lemma sigma_decomposition_constt' x M (sM := \sigma(M)) :
  M \in 'M -> sigma_decomposition x.`_sM^' = sigma_decomposition x :\ x.`_sM.
Proof.
move=> maxM; apply/setP=> y; rewrite !inE andbCA; apply: andb_id2l => nty.
apply/imsetP/andP=> [ | [neq_y_xM /imsetP]] [L maxL def_y].
  have not_sMy: ~~ sM.-elt y.
    apply: contra nty => sMy; rewrite -order_eq1 (pnat_1 sMy) // def_y.
    by apply: p_eltX; apply: p_elt_constt.
  split; first by apply: contraNneq not_sMy => ->; apply: p_elt_constt.
  have notMGL: gval L \notin M :^: G.
    apply: contra not_sMy; rewrite def_y; case/imsetP=> z _ ->.
    by rewrite (eq_constt _ (sigmaJ M z)) p_elt_constt.
  apply/imsetP; exists L; rewrite // def_y sub_in_constt // => p _ sLp.
  by apply: contraFN (sigma_partition maxM maxL notMGL p) => sMp; apply/andP.
exists L; rewrite ?sub_in_constt // => p _ sLp.
suffices notMGL: gval L \notin M :^: G.
  by apply: contraFN (sigma_partition maxM maxL notMGL p) => sMp; apply/andP.
apply: contra neq_y_xM; rewrite def_y => /imsetP[z _ ->].
by rewrite (eq_constt _ (sigmaJ M z)).
Qed.

(* General remarks about the sigma-decomposition, p. 105 of B & G. *)
Remark sigma_mmax_exists p :
  p \in \pi(G) -> {M : {group gT} | M \in 'M & p \in \sigma(M)}.
Proof.
move=> piGp; have [P sylP] := Sylow_exists p [set: gT].
have ntP: P :!=: 1 by rewrite -rank_gt0 (rank_Sylow sylP) p_rank_gt0.
have ltPG: P \proper G := mFT_pgroup_proper (pHall_pgroup sylP).
have [M maxNM] := mmax_exists (mFT_norm_proper ntP ltPG).
have{maxNM} [maxM sNM] := setIdP maxNM; have sPM := subset_trans (normG P) sNM.
have{sylP} sylP := pHall_subl sPM (subsetT M) sylP.
by exists M => //; apply/exists_inP; exists P.
Qed.

Lemma ell_sigma0P x : reflect (x = 1) (\ell_\sigma(x) == 0).
Proof.
rewrite cards_eq0 setD_eq0.
apply: (iffP idP) => [x1 | ->]; last first.
  by apply/subsetP=> _ /imsetP[M _ ->]; rewrite constt1 inE.
rewrite -(prod_constt x) big1_seq //= => p _; apply: contraTeq x1 => nt_xp.
have piXp: p \in \pi(#[x]) by rewrite -p_part_gt1 -order_constt order_gt1.
have [M maxM sMp] := sigma_mmax_exists (piSg (subsetT _) piXp).
apply/subsetPn; exists (x.`_(\sigma(M))); first exact: mem_imset.
by rewrite (sameP set1P constt1P); apply: contraL sMp => /pnatPpi; apply.
Qed.

Remark sigma_decomposition_subG x H :
  x \in H -> sigma_decomposition x \subset H.
Proof.
by move=> Hx; apply/subsetP=> _ /setD1P[_ /imsetP[M _ ->]]; apply: groupX.
Qed.

Remark prod_sigma_decomposition x :
  \prod_(x_sM in sigma_decomposition x) x_sM = x.
Proof.
rewrite -big_filter filter_index_enum; set e := enum _.
have: uniq e := enum_uniq _; have: e =i sigma_decomposition x := mem_enum _.
elim: {x}e (x) => [|y e IHe] x def_e /= Ue.
  by rewrite big_nil (ell_sigma0P x _) //; apply/pred0P; apply: fsym.
have{Ue} [not_e_y Ue] := andP Ue.
have [nty] := setD1P (etrans (fsym def_e y) (mem_head _ _)).
case/imsetP=> M maxM def_y; rewrite big_cons -(consttC \sigma(M) x) -def_y.
congr (y * _); apply: IHe Ue => z; rewrite sigma_decomposition_constt' //.
rewrite -def_y inE -def_e !inE andb_orr andNb andb_idl //.
by apply: contraTneq => ->.
Qed.

Lemma ell1_decomposition x :
  \ell_\sigma(x) == 1%N -> sigma_decomposition x = [set x].
Proof.
case/cards1P=> y sdx_y.
by rewrite -{2}[x]prod_sigma_decomposition sdx_y big_set1.
Qed.

Lemma Msigma_ell1 M x :
  M \in 'M -> x \in (M`_\sigma)^# -> \ell_\sigma(x) == 1%N.
Proof.
move=> maxM /setD1P[ntx Ms_x]; apply/cards1P.
have sMx: \sigma(M).-elt x := mem_p_elt (pcore_pgroup _ _) Ms_x.
have def_xM: x.`_(\sigma(M)) = x := constt_p_elt sMx.
exists x; apply/eqP; rewrite eqEsubset sub1set !inE ntx -setD_eq0 /=.
rewrite -{2 3}def_xM -sigma_decomposition_constt' // (constt1P _) ?p_eltNK //.
by rewrite -cards_eq0 (sameP (ell_sigma0P 1) eqP) eqxx; apply: mem_imset.
Qed.

Remark ell_sigma1P x :
  reflect (x != 1 /\ 'M_\sigma[x] != set0) (\ell_\sigma(x) == 1%N).
Proof.
apply: (iffP idP) => [ell1x | [ntx]]; last first.
  case/set0Pn=> M /setIdP[maxM]; rewrite cycle_subG => Ms_x.
  by rewrite (Msigma_ell1 maxM) // in_setD1 ntx.
have sdx_x: x \in sigma_decomposition x by rewrite ell1_decomposition ?set11.
have{sdx_x} [ntx sdx_x] := setD1P sdx_x; split=> //; apply/set0Pn.
have{sdx_x} [M maxM def_x] := imsetP sdx_x; rewrite // -cycle_eq1 in ntx.
have sMx: \sigma(M).-elt x by rewrite def_x p_elt_constt.
have [[z sXzMs] _] := sigma_Jsub maxM sMx ntx.
by exists (M :^ z^-1)%G; rewrite inE mmaxJ maxM MsigmaJ -sub_conjg.
Qed.

Remark ell_sigma_le1 x :(\ell_\sigma(x) <= 1) = ('M_\sigma[x] != set0).
Proof.
rewrite -[_ <= 1](mem_iota 0 2) !inE (sameP (ell_sigma0P x) eqP).
rewrite (sameP (ell_sigma1P x) andP); case: eqP => //= ->; symmetry.
have [M max1M] := mmax_exists (mFT_pgroup_proper (@pgroup1 gT 2)).
have [maxM _] := setIdP max1M; apply/set0Pn; exists M.
by rewrite inE maxM cycle1 sub1G.
Qed.

(* Basic properties of \kappa and the maximal group subclasses. *)
Lemma kappaJ M x : \kappa(M :^ x) =i \kappa(M).
Proof.
move=> p; rewrite unlock 3!{1}inE /= tau1J tau3J; apply: andb_id2l => _.
apply/exists_inP/exists_inP=> [] [P EpP ntCMsP].
  rewrite -(conjsgK x M); exists (P :^ x^-1)%G; first by rewrite pnElemJ.
  by rewrite MsigmaJ centJ -conjIg -subG1 sub_conjg conjs1g subG1.
exists (P :^ x)%G; first by rewrite pnElemJ.
by rewrite MsigmaJ centJ -conjIg -subG1 sub_conjg conjs1g subG1.
Qed.

Lemma kappa_tau13 M p : p \in \kappa(M) -> (p \in \tau1(M)) || (p \in \tau3(M)).
Proof. by rewrite unlock => /andP[]. Qed.

Lemma kappa_sigma' M : {subset \kappa(M) <= \sigma(M)^'}.
Proof. by move=> p /kappa_tau13/orP[] /andP[]. Qed.

Remark rank_kappa M p : p \in \kappa(M) -> 'r_p(M) = 1%N.
Proof. by case/kappa_tau13/orP=> /and3P[_ /eqP]. Qed.

Lemma kappa_pi M : {subset \kappa(M) <= \pi(M)}.
Proof. by move=> p kMp; rewrite -p_rank_gt0 rank_kappa. Qed.

Remark kappa_nonregular M p P :
  p \in \kappa(M) -> P \in 'E_p^1(M) -> 'C_(M`_\sigma)(P) != 1.
Proof.
move=> kMp EpP; have rpM := rank_kappa kMp.
have [sPM abelP oP] := pnElemPcard EpP; have [pP _] := andP abelP.
have [Q EpQ nregQ]: exists2 Q, Q \in 'E_p^1(M) & 'C_(M`_\sigma)(Q) != 1.
  by apply/exists_inP; rewrite unlock in kMp; case/andP: kMp.
have [sQM abelQ oQ] := pnElemPcard EpQ; have [pQ _] := andP abelQ.
have [S sylS sQS] := Sylow_superset sQM pQ; have [_ pS _] := and3P sylS.
have [x Mx sPxS] := Sylow_Jsub sylS sPM pP.
rewrite -(inj_eq (@conjsg_inj _ x)) conjs1g conjIg -centJ.
rewrite (normsP (normal_norm (pcore_normal _ _))) // (subG1_contra _ nregQ) //.
rewrite setIS ?centS // -(cardSg_cyclic _ sPxS sQS) ?cardJg ?oP ?oQ //.
by rewrite (odd_pgroup_rank1_cyclic pS) ?mFT_odd // (p_rank_Sylow sylS) rpM.
Qed.

Lemma ex_kappa_compl M K :
    M \in 'M -> \kappa(M).-Hall(M) K ->
  exists U : {group gT}, kappa_complement M U K.
Proof.
move=> maxM hallK; have [sKM kK _] := and3P hallK.
have s'K: \sigma(M)^'.-group K := sub_pgroup (@kappa_sigma' M) kK.
have [E hallE sKE] := Hall_superset (mmax_sol maxM) sKM s'K.
pose sk' := \sigma_kappa(M)^'.
have [U hallU] := Hall_exists sk' (sigma_compl_sol hallE).
exists U; split=> //.
  by apply: subHall_Hall hallE _ hallU => p; case/norP.
suffices ->: U * K = E by apply: groupP.
have [[sUE sk'U _] [sEM s'E _]] := (and3P hallU, and3P hallE).
apply/eqP; rewrite eqEcard mulG_subG sUE sKE /= coprime_cardMg; last first.
  by apply: p'nat_coprime (sub_pgroup _ sk'U) kK => p; case/norP.
rewrite -(partnC \kappa(M) (cardG_gt0 E)) -{2}(part_pnat_id s'E) mulnC.
rewrite -(card_Hall (pHall_subl sKE sEM hallK)) leq_mul // -partnI.
by rewrite -(@eq_partn sk') -?(card_Hall hallU) // => p; apply: negb_or.
Qed.

Lemma FtypeP M : reflect (M \in 'M /\ \kappa(M) =i pred0) (M \in 'M_'F).
Proof.
do [apply: (iffP setIdP) => [] [maxM k'M]; split] => // [p|].
  by apply/idP=> /= kMp; case/negP: (pnatPpi k'M (kappa_pi kMp)).
by apply/pgroupP=> p _ _; rewrite inE /= k'M.
Qed.

Lemma PtypeP M : reflect (M \in 'M /\ exists p, p \in \kappa(M)) (M \in 'M_'P).
Proof.
apply: (iffP setDP) => [[maxM kM] | [maxM [p kMp]]]; split => //.
  rewrite inE maxM !negb_and cardG_gt0 /= all_predC negbK in kM.
  by have [p _ kMp] := hasP kM; exists p.
by apply/FtypeP=> [[_ kM0]]; rewrite kM0 in kMp.
Qed.

Lemma trivg_kappa M K :
  M \in 'M -> \kappa(M).-Hall(M) K -> (K :==: 1) = (M \in 'M_'F).
Proof.
by move=> maxM hallK; rewrite inE maxM trivg_card1 (card_Hall hallK) partG_eq1.
Qed.

(* Could go in Section 10. *)
Lemma not_sigma_mmax M : M \in 'M -> ~~ \sigma(M).-group M.
Proof.
move=> maxM; apply: contraL (mmax_sol maxM); rewrite negb_forall_in => sM.
apply/existsP; exists M; rewrite mmax_neq1 // subsetIidl andbT.
apply: subset_trans (Msigma_der1 maxM).
by rewrite (sub_Hall_pcore (Msigma_Hall maxM)).
Qed.

Lemma trivg_kappa_compl M U K :
  M \in 'M -> kappa_complement M U K -> (U :==: 1) = (M \in 'M_'P1).
Proof.
move=> maxM [hallU _ _]; symmetry.
rewrite 3!inE maxM /= trivg_card1 (card_Hall hallU) partG_eq1 pgroupNK andbT.
apply: andb_idl => skM; apply: contra (not_sigma_mmax maxM).
by apply: sub_in_pnat => p /(pnatPpi skM)/orP[] // kMp /negP.
Qed.

Lemma FtypeJ M x : ((M :^ x)%G \in 'M_'F) = (M \in 'M_'F).
Proof. by rewrite inE mmaxJ pgroupJ (eq_p'group _ (kappaJ M x)) !inE. Qed. 

Lemma PtypeJ M x : ((M :^ x)%G \in 'M_'P) = (M \in 'M_'P).
Proof. by rewrite !in_setD mmaxJ FtypeJ. Qed. 

Lemma P1typeJ M x : ((M :^ x)%G \in 'M_'P1) = (M \in 'M_'P1).
Proof.
rewrite inE PtypeJ pgroupJ [M \in 'M_'P1]inE; congr (_ && _).
by apply: eq_pgroup => p; rewrite inE /= kappaJ sigmaJ.
Qed. 

Lemma P2typeJ M x : ((M :^ x)%G \in 'M_'P2) = (M \in 'M_'P2).
Proof. by rewrite in_setD PtypeJ P1typeJ -in_setD. Qed.

(* This is B & G, Lemma 14.1. *)
Lemma sigma'_kappa'_facts M p S (A := 'Ohm_1(S)) (Ms := M`_\sigma) :
    M \in 'M -> p.-Sylow(M) S ->
   [&& p \in \pi(M), p \notin \sigma(M) & p \notin \kappa(M)] -> 
 [/\ M \in 'M_'F :|: 'M_'P2, logn p #|A| <= 2, 'C_Ms(A) = 1 & nilpotent Ms].
Proof.
move=> maxM sylS /and3P[piMp sM'p kM'p]; have [sSM pS _] := and3P sylS.
rewrite 8!(maxM, inE) /= !andbT negb_and orb_andr orbN andbT negbK.
rewrite (contra (fun skM => pnatPpi skM piMp)) ?orbT; last exact/norP.
rewrite partition_pi_mmax // (negPf sM'p) orbF orbCA in piMp.
have{piMp} [t2p | t13p] := orP piMp.
  rewrite (tau2_Msigma_nil maxM t2p); have [_ rpM] := andP t2p.
  have{rpM} rS: 2 <= 'r_p(S) by rewrite (p_rank_Sylow sylS) (eqP rpM).
  have [B EpB] := p_rank_geP rS; have{EpB} [sBS abelB dimB] := pnElemP EpB.
  have EpB: B \in 'E_p^2(M) by rewrite !inE abelB dimB (subset_trans sBS).
  have [defB _ regB _ _] := tau2_context maxM t2p EpB.
  by rewrite /A -dimB; have [_ [|->]] := defB S sylS.
have [ntS cycS]: S :!=: 1 /\ cyclic S.
  rewrite (odd_pgroup_rank1_cyclic pS) ?mFT_odd // (p_rank_Sylow sylS).
  apply/andP; rewrite -rank_gt0 (rank_Sylow sylS) -eqn_leq eq_sym.
  by rewrite -2!andb_orr orNb andbT inE /= sM'p in t13p.
have [p_pr _ _] := pgroup_pdiv pS ntS.
have oA: #|A| = p by rewrite (Ohm1_cyclic_pgroup_prime cycS pS).
have sAM: A \subset M := subset_trans (Ohm_sub 1 S) sSM.
have regA: 'C_Ms(A) = 1.
  apply: contraNeq kM'p => nregA; rewrite unlock; apply/andP; split=> //.
  by apply/exists_inP; exists [group of A]; rewrite ?p1ElemE // !inE sAM oA /=.
have defMsA: Ms ><| A = Ms <*> A.
  rewrite sdprodEY ?coprime_TIg ?(subset_trans sAM) ?gFnorm // oA.
  by rewrite (pnat_coprime (pcore_pgroup _ _)) ?pnatE.
rewrite (prime_Frobenius_sol_kernel_nil defMsA) ?oA ?(pfactorK 1) //.
by rewrite (solvableS _ (mmax_sol maxM)) // join_subG pcore_sub.
Qed.

Lemma notP1type_Msigma_nil M :
  (M \in 'M_'F) || (M \in 'M_'P2) -> nilpotent M`_\sigma.
Proof.
move=> notP1maxM; suffices [maxM]: M \in 'M /\ ~~ \sigma_kappa(M).-group M.
  rewrite negb_and cardG_gt0 => /allPn[p piMp /norP[s'p k'p]].
  by have [S /sigma'_kappa'_facts[] //] := Sylow_exists p M; apply/and3P.
have [/setIdP[maxM k'M] | /setDP[PmaxM]] := orP notP1maxM; last first.
  by rewrite inE PmaxM; case/setDP: PmaxM.
split=> //; apply: contra (not_sigma_mmax maxM).
by apply: sub_in_pnat => p piMp /orP[] // /idPn[]; exact: (pnatPpi k'M).
Qed.

(* This is B & G, Proposition 14.2. *)
Proposition Ptype_structure M K (Ms := M`_\sigma) (Kstar := 'C_Ms(K)) :
  M \in 'M_'P -> \kappa(M).-Hall(M) K ->
  [/\ (*a*) exists2 U : {group gT},
              kappa_complement M U K /\ Ms ><| (U ><| K) = M
            & [/\ abelian U, semiprime Ms K & semiregular U K],
      (*b*) (*1.2*) K \x Kstar = 'N_M(K)
           /\ {in 'E^1(K), forall X, 
            (*1.1*) 'N_M(X) = 'N_M(K)
           /\ (*2*) {in 'M('N(X)), forall Mstar, X \subset Mstar`_\sigma}},
      (*c*) Kstar != 1 /\ {in 'E^1(Kstar), forall X, 'M('C(X)) = [set M]},
  [/\ (*d*) {in ~: M, forall g, Kstar :&: M :^ g = 1}
         /\ {in M :\: 'N_M(K), forall g, K :&: K :^ g = 1},
      (*e*) {in \pi(Kstar), forall p S,
             p.-Sylow(M) S -> 'M(S) = [set M] /\ ~~ (S \subset Kstar)}
    & (*f*) forall Y, \sigma(M).-group Y -> Y :&: Kstar != 1 -> Y \subset Ms]
    & (*g*) M \in 'M_'P2 ->
            [/\ \sigma(M) =i \beta(M), prime #|K|, nilpotent Ms
              & normedTI Ms^# G M]].
Proof.
move: @Kstar => Ks PmaxM hallK; have [maxM notFmaxM] := setDP PmaxM.
have sMs: \sigma(M).-group M`_\sigma := pcore_pgroup _ M.
have{notFmaxM} ntK: K :!=: 1 by rewrite (trivg_kappa maxM).
have [sKM kK _] := and3P hallK; have s'K := sub_pgroup (@kappa_sigma' M) kK.
have solM := mmax_sol maxM; have [E hallE sKE] := Hall_superset solM sKM s'K.
have [[sEM s'E _] [_ [E3 hallE3]]] := (and3P hallE, ex_tau13_compl hallE).
have [F1 hallF1] := Hall_exists \tau1(M) (solvableS sKM solM).
have [[sF1K t1F1 _] solE] := (and3P hallF1, sigma_compl_sol hallE).
have [E1 hallE1 sFE1] := Hall_superset solE (subset_trans sF1K sKE) t1F1.
have [E2 hallE2 complEi] := ex_tau2_compl hallE hallE1 hallE3.
have [[_ nsE3E] _ [cycE1 _] [defEl defE] _] := sigma_compl_context maxM complEi.
have [sE1E t1E1 _] := and3P hallE1; have sE1M := subset_trans sE1E sEM.
have [sE3E t3E3 _] := and3P hallE3; have sE3M := subset_trans sE3E sEM.
set part_a := exists2 U, _ & _; pose b1_hyp := {in 'E^1(K), forall X, X <| K}.
have [have_a nK1K ntE1 sE1K]: [/\ part_a, b1_hyp, E1 :!=: 1 & E1 \subset K].
  have [t1K | not_t1K] := boolP (\tau1(M).-group K).
    have sKE1: K \subset E1 by rewrite (sub_pHall hallF1 t1K).
    have prE1 := tau1_primact_Msigma maxM hallE hallE1.
    have st1k: {subset \tau1(M) <= \kappa(M)}.
      move=> p t1p; rewrite unlock 3!inE /= t1p /=.
      have [X]: exists X, X \in 'E_p^1(E1).
        apply/p_rank_geP; rewrite p_rank_gt0 /= (card_Hall hallE1).
        by rewrite pi_of_part // inE /= (partition_pi_sigma_compl maxM) ?t1p.
      rewrite -(setIidPr sE1M) pnElemI -setIdE => /setIdP[EpX sXE1].
      pose q := pdiv #|K|; have piKq: q \in \pi(K) by rewrite pi_pdiv cardG_gt1.
      have /p_rank_geP[Y]: 0 < 'r_q(K) by rewrite p_rank_gt0.
      rewrite -(setIidPr sKM) pnElemI -setIdE => /setIdP[EqY sYK].
      have ntCMsY := kappa_nonregular (pnatPpi kK piKq) EqY.
      have [ntY sYE1] := (nt_pnElem EqY isT, subset_trans sYK sKE1).
      apply/exists_inP; exists X; rewrite ?(subG1_contra _ ntCMsY) //=.
      by rewrite (cent_semiprime prE1 sYE1 ntY) ?setIS ?centS.
    have defK := sub_pHall hallK (sub_pgroup st1k t1E1) sKE1 sE1M.
    split=> [|X||]; rewrite ?defK //; last first.
       rewrite -defK; case/nElemP=> p /pnElemP[sXE1 _ _].
       by rewrite char_normal // sub_cyclic_char.
    have [[U _ defU _] _ _ _] := sdprodP defE; rewrite defU in defE.
    have [nsUE _ mulUE1 nUE1 _] := sdprod_context defE.
    have [[_ V _ defV] _] := sdprodP defEl; rewrite defV.
    have [_ <- nE21 _] := sdprodP defV => /mulGsubP[nE32 nE31] _.
    have regUK: semiregular U K.
      move=> y /setD1P[]; rewrite -cycle_subG -cent_cycle -order_gt1.
      rewrite -pi_pdiv; move: (pdiv _) => p pi_y_p Ky.
      have piKp := piSg Ky pi_y_p; have t1p := pnatPpi t1K piKp.
      move: pi_y_p; rewrite -p_rank_gt0 => /p_rank_geP[Y] /=.
      rewrite -{1}(setIidPr (subset_trans Ky sKE)) pnElemI -setIdE.
      case/setIdP=> EpY sYy; have EpMY := subsetP (pnElemS _ _ sEM) Y EpY.
      apply: contraNeq (kappa_nonregular (pnatPpi kK piKp) EpMY).
      move/(subG1_contra (setIS U (centS sYy))).
      have{y sYy Ky} sYE1 := subset_trans sYy (subset_trans Ky sKE1).
      have ntY: Y :!=: 1 by apply: (nt_pnElem EpY). 
      rewrite -subG1 /=; have [_ <- _ tiE32] := sdprodP defU.
      rewrite -subcent_TImulg ?subsetI ?(subset_trans sYE1) // mulG_subG.
      rewrite !subG1 /= => /nandP[nregE3Y | nregE2Y].
        have pr13 := cent_semiprime (tau13_primact_Msigma maxM complEi _).
        rewrite pr13 ?(subset_trans sYE1) ?joing_subr //; last first.
          by move/cent_semiregular=> regE31; rewrite regE31 ?eqxx in nregE3Y.
        pose q := pdiv #|'C_E3(Y)|.
        have piE3q: q \in \pi(E3).
          by rewrite (piSg (subsetIl E3 'C(Y))) // pi_pdiv cardG_gt1.
        have /p_rank_geP[X]: 0 < 'r_q(M :&: E3).
          by rewrite (setIidPr sE3M) p_rank_gt0.
        rewrite pnElemI -setIdE => /setIdP[EqX sXE3].
        rewrite -subG1 -(_ : 'C_Ms(X) = 1) ?setIS ?centS //.
          by rewrite (subset_trans sXE3) ?joing_subl.
        apply: contraTeq (pnatPpi t3E3 piE3q) => nregMsX; apply: tau3'1.
        suffices kq: q \in \kappa(M).
          rewrite (pnatPpi t1K) //= (card_Hall hallK) pi_of_part //.
          by rewrite inE /= kappa_pi.
        rewrite unlock 3!inE /= (pnatPpi t3E3 piE3q) orbT /=.
        by apply/exists_inP; exists X.
      pose q := pdiv #|'C_E2(Y)|; have [sE2E t2E2 _] := and3P hallE2.
      have piCE2Yq: q \in \pi('C_E2(Y)) by rewrite pi_pdiv cardG_gt1.
      have [X]: exists X, X \in 'E_q^1(E :&: 'C_E2(Y)).
        by apply/p_rank_geP; rewrite /= setIA (setIidPr sE2E) p_rank_gt0.
      rewrite pnElemI -setIdE => /setIdP[EqX sXcE2Y].
      have t2q:= pnatPpi t2E2 (piSg (subsetIl _ _) piCE2Yq).
      have [A Eq2A _] := ex_tau2Elem hallE t2q.
      have [[_ defEq1] _ _ _] := tau2_compl_context maxM hallE t2q Eq2A.
      rewrite (tau12_regular maxM hallE t1p EpY t2q Eq2A) //.
      rewrite (subG1_contra _ (nt_pnElem EqX _)) // subsetI.
      rewrite defEq1 in EqX; case/pnElemP: EqX => -> _ _.
      by rewrite (subset_trans sXcE2Y) ?subsetIr.
    have [defM [sUE _]] := (sdprod_sigma maxM hallE, andP nsUE).
    have hallU: \sigma_kappa(M)^'.-Hall(M) U.
      suffices: [predI \sigma(M)^' & \kappa(M)^'].-Hall(M) U.
        by apply: etrans; apply: eq_pHall=> p; rewrite inE /= negb_or.
      apply: subHall_Hall hallE _ _ => [p|]; first by case/andP.
      rewrite pHallE partnI (part_pnat_id s'E) -pHallE.
      have hallK_E: \kappa(M).-Hall(E) K := pHall_subl sKE sEM hallK.
      by apply/(sdprod_normal_pHallP nsUE hallK_E); rewrite -defK.
    exists U; [rewrite -{2}defK defE | rewrite -{1}defK]; split=> //.
      by split; rewrite // -defK mulUE1 groupP.
    apply: abelianS (der_mmax_compl_abelian maxM hallE).
    rewrite -(coprime_cent_prod nUE1) ?(solvableS sUE) //.
      by rewrite {2}defK (cent_semiregular regUK) // mulg1 commgSS.
    by rewrite (coprime_sdprod_Hall_r defE); apply: pHall_Hall hallE1.
  move: not_t1K; rewrite negb_and cardG_gt0 => /allPn[p piKp t1'p].
  have kp := pnatPpi kK piKp; have t3p := kappa_tau13 kp.
  rewrite [p \in _](negPf t1'p) /= in t3p.
  have [X]: exists X, X \in 'E_p^1(K) by apply/p_rank_geP; rewrite p_rank_gt0.
  rewrite -{1}(setIidPr sKM) pnElemI -setIdE => /setIdP[EpX sXK].
  have sXE3: X \subset E3.
    rewrite (sub_normal_Hall hallE3) ?(subset_trans sXK) ?(pi_pgroup _ t3p) //.
    by case/pnElemP: EpX => _ /andP[].
  have [nregX ntX] := (kappa_nonregular kp EpX, nt_pnElem EpX isT).
  have [regE3|ntE1 {defE}defE prE nE1_E] := tau13_nonregular maxM complEi.
    by case/eqP: nregX; rewrite (cent_semiregular regE3).
  have defK: E :=: K.
    apply: (sub_pHall hallK _ sKE sEM); apply/pgroupP=> q q_pr q_dv_E.
    have{q_dv_E} piEq: q \in \pi(E) by rewrite mem_primes q_pr cardG_gt0.
    rewrite unlock; apply/andP; split=> /=.
      apply: pnatPpi piEq; rewrite -pgroupE -(sdprodW defE).
      rewrite pgroupM (sub_pgroup _ t3E3) => [|r t3r]; last by apply/orP; right.
      by rewrite (sub_pgroup _ t1E1) // => r t1r; apply/orP; left.
    have:= piEq; rewrite -p_rank_gt0 => /p_rank_geP[Y].
    rewrite -{1}(setIidPr sEM) pnElemI -setIdE => /setIdP[EqY sYE].
    rewrite (cent_semiprime prE) ?(subset_trans sXK) // in nregX.
    apply/exists_inP; exists Y => //; apply: subG1_contra nregX.
    by rewrite setIS ?centS.
  have defM := sdprod_sigma maxM hallE.
  rewrite /b1_hyp -defK; split=> //; exists 1%G; last first.
    by split; [exact: abelian1 | rewrite -defK | exact: semiregular1l].
  rewrite sdprod1g; do 2?split=> //; rewrite ?mul1g ?groupP -?defK //.
  rewrite pHallE sub1G cards1 eq_sym partG_eq1 pgroupNK /=.
  have{defM} [_ defM _ _] := sdprodP defM; rewrite -{2}defM defK pgroupM.
  rewrite (sub_pgroup _ sMs) => [|r sr]; last by apply/orP; left.
  by rewrite (sub_pgroup _ kK) // => r kr; apply/orP; right.
set part_b := _ /\ _; set part_c := _ /\ _; set part_d := _ /\ _.
have [U [complUK defM] [cUU prMsK regUK]] := have_a.
have [hallU _ _] := complUK; have [sUM sk'U _] := and3P hallU.
have have_b: part_b.
  have coMsU: coprime #|Ms| #|U|.
    by rewrite (pnat_coprime sMs (sub_pgroup _ sk'U)) // => p; case/norP.
  have{defM} [[_ F _ defF]] := sdprodP defM; rewrite defF.
  have [_ <- nUK _] := sdprodP defF; rewrite mulgA mulG_subG => defM.
  case/andP=> nMsU nMsK _.
  have coMsU_K: coprime #|Ms <*> U| #|K|.
    rewrite norm_joinEr // (p'nat_coprime _ kK) // -pgroupE.
    rewrite pgroupM // (sub_pgroup _ sMs) => [|r]; last first.
      by apply: contraL; apply: kappa_sigma'.
    by apply: sub_pgroup _ sk'U => r /norP[].
  have defNK X: X <| K -> X :!=: 1 -> 'N_M(X) = Ks * K.
    case/andP=> sXK nXK ntX; rewrite -defM -(norm_joinEr nMsU).
    rewrite setIC -group_modr // setIC.
    rewrite coprime_norm_cent ?(subset_trans sXK) ?normsY //; last first.
      by rewrite (coprimegS sXK).
    rewrite /= norm_joinEr -?subcent_TImulg ?(coprime_TIg coMsU) //; last first.
      by rewrite subsetI !(subset_trans sXK).
    by rewrite (cent_semiregular regUK) // mulg1 (cent_semiprime prMsK).
  rewrite /part_b dprodE ?subsetIr //; last first.
    rewrite setICA setIA (coprime_TIg (coprimeSg _ coMsU_K)) ?setI1g //.
    by rewrite joing_subl.
  rewrite -centC ?subsetIr // defNK //; split=> // X Eq1X.
  have [q EqX] := nElemP Eq1X; have ntX := nt_pnElem EqX isT.
  have:= EqX; rewrite -{1}(setIidPr sKE) pnElemI -setIdE.
  case/setIdP=> EqEX sXK; split; first by rewrite defNK ?nK1K.
  have [_ abelX dimX] := pnElemP EqX; have [qX _] := andP abelX.
  have kq: q \in \kappa(M).
    by rewrite (pnatPpi kK (piSg sXK _)) // -p_rank_gt0 p_rank_abelem ?dimX.
  have nregX := kappa_nonregular kq (subsetP (pnElemS _ _ sEM) _ EqEX).
  have sq := tau13_nonregular_sigma maxM hallE EqEX (kappa_tau13 kq) nregX.
  move=> H maxNH; have [maxH sNXH] := setIdP maxNH.
  rewrite (sub_Hall_pcore (Msigma_Hall maxH)) ?(subset_trans (normG X)) //.
  exact: pi_pgroup qX (sq H maxNH).
have have_c: part_c.
  pose p := pdiv #|E1|; have piE1p: p \in \pi(E1) by rewrite pi_pdiv cardG_gt1.
  have:= piE1p; rewrite -p_rank_gt0 => /p_rank_geP[Y].
  rewrite -(setIidPr sE1M) pnElemI -setIdE => /setIdP[EpY sYE1].
  have [sYK ntY] := (subset_trans sYE1 sE1K, nt_pnElem EpY isT).
  split=> [|X /nElemP[q]].
    rewrite /Ks -(cent_semiprime prMsK sYK) //.
    exact: kappa_nonregular (pnatPpi kK (piSg sE1K piE1p)) EpY.
  rewrite /= -(cent_semiprime prMsK sYK) // => EqX.
  by have [] := cent_cent_Msigma_tau1_uniq maxM hallE hallE1 sYE1 ntY EqX.
have [[defNK defK1] [_ uniqKs]] := (have_b, have_c).
have have_d: part_d.
  split=> g.
    rewrite inE; apply: contraNeq; rewrite -rank_gt0.
    case/rank_geP=> X; rewrite nElemI -setIdE -groupV => /setIdP[EpX sXMg].
    have [_ sCXMs] := mem_uniq_mmax (uniqKs _ EpX).
    case/nElemP: EpX => p /pnElemP[/subsetIP[sXMs _] abelX dimX].
    have [[pX _] sXM] := (andP abelX, subset_trans sXMs (pcore_sub _ _)).
    have piXp: p \in \pi(X) by rewrite -p_rank_gt0 p_rank_abelem ?dimX.
    have sp := pnatPpi sMs (piSg sXMs piXp).
    have [def_g _ _] := sigma_group_trans maxM sp pX.
    have [|c cXc [m Mm ->]] := def_g g^-1 sXM; first by rewrite sub_conjgV.
    by rewrite groupM // (subsetP sCXMs).
  case/setDP=> Mg; apply: contraNeq; rewrite -rank_gt0 /=.
  case/rank_geP=> X; rewrite nElemI -setIdE => /setIdP[EpX sXKg].
  have [<- _] := defK1 X EpX; rewrite 2!inE Mg /=.
  have{EpX} [p EpX] := nElemP EpX; have [_ abelX dimX] := pnElemP EpX.
  have defKp1: {in 'E_p^1(K), forall Y, 'Ohm_1('O_p(K)) = Y}.
    move=> Y EpY; have E1K_Y: Y \in 'E^1(K) by apply/nElemP; exists p.
    have piKp: p \in \pi(K) by rewrite -p_rank_gt0; apply/p_rank_geP; exists Y.
    have [pKp sKpK] := (pcore_pgroup p K, pcore_sub p K).
    have cycKp: cyclic 'O_p(K).
      rewrite (odd_pgroup_rank1_cyclic pKp) ?mFT_odd //.
      by rewrite -(rank_kappa (pnatPpi kK piKp)) p_rankS ?(subset_trans sKpK).
    have [sYK abelY oY] := pnElemPcard EpY; have [pY _] := andP abelY.
    have sYKp: Y \subset 'O_p(K) by rewrite pcore_max ?nK1K.
    apply/eqP; rewrite eq_sym eqEcard -{1}(Ohm1_id abelY) OhmS //= oY.
    rewrite (Ohm1_cyclic_pgroup_prime cycKp pKp) ?(subG1_contra sYKp) //=.
    exact: nt_pnElem EpY _.
  rewrite sub_conjg -[X :^ _]defKp1 ?(defKp1 X) //.
  by rewrite !inE sub_conjgV sXKg abelemJ abelX cardJg dimX.
split=> {part_a part_b part_c have_a have_b have_c}//; first split=> //.
- move=> q; rewrite /Ks -(cent_semiprime prMsK sE1K ntE1) => picMsE1q.
  have sq := pnatPpi (pcore_pgroup _ M) (piSg (subsetIl _ _) picMsE1q).
  move: picMsE1q; rewrite -p_rank_gt0; case/p_rank_geP=> y EqY S sylS.
  have [sSM qS _] := and3P sylS.
  have sSMs: S \subset M`_\sigma.
    by rewrite (sub_Hall_pcore (Msigma_Hall maxM)) ?(pi_pgroup qS).
  have sylS_Ms: q.-Sylow(M`_\sigma) S := pHall_subl sSMs (pcore_sub _ M) sylS.
  have [_]:= cent_cent_Msigma_tau1_uniq maxM hallE hallE1 (subxx _) ntE1 EqY.
  move/(_ S sylS_Ms) => uniqS; split=> //; rewrite subsetI sSMs /=.
  pose p := pdiv #|E1|; have piE1p: p \in \pi(E1) by rewrite pi_pdiv cardG_gt1.
  have [s'p _] := andP (pnatPpi t1E1 piE1p).
  have [P sylP] := Sylow_exists p E1; have [sPE1 pP _] := and3P sylP.
  apply: contra (s'p) => cE1S; apply/exists_inP; exists P.
    exact: subHall_Sylow s'p (subHall_Sylow hallE1 (pnatPpi t1E1 piE1p) sylP).
  apply: (sub_uniq_mmax uniqS); first by rewrite cents_norm // (centsS sPE1).
  apply: mFT_norm_proper (mFT_pgroup_proper pP).
  by rewrite -rank_gt0 (rank_Sylow sylP) p_rank_gt0.
- move=> Y sY ntYKs; have ntY: Y :!=:1 := subG1_contra (subsetIl _ _) ntYKs.
  have [[x sYxMs] _] := sigma_Jsub maxM sY ntY; rewrite sub_conjg in sYxMs.
  suffices Mx': x^-1 \in M by rewrite (normsP _ _ Mx') ?gFnorm in sYxMs.
  rewrite -(setCK M) inE; apply: contra ntYKs => M'x'.
  rewrite setIC -(setIidPr sYxMs) -/Ms -[Ms](setIidPr (pcore_sub _ _)).
  by rewrite conjIg !setIA; have [-> // _] := have_d; rewrite !setI1g.
rewrite inE PmaxM andbT -(trivg_kappa_compl maxM complUK) => ntU.
have [regMsU nilMs]: 'C_Ms(U) = 1 /\ nilpotent Ms.
  pose p := pdiv #|U|; have piUp: p \in \pi(U) by rewrite pi_pdiv cardG_gt1.
  have sk'p := pnatPpi sk'U piUp.
  have [S sylS] := Sylow_exists p U; have [sSU _] := andP sylS.
  have sylS_M := subHall_Sylow hallU sk'p sylS.
  rewrite -(setIidPr (centS (subset_trans (Ohm_sub 1 S) sSU))) setIA.
  have [|_ _ -> ->] := sigma'_kappa'_facts maxM sylS_M; last by rewrite setI1g.
  by rewrite -negb_or (piSg sUM).
have [[_ F _ defF] _ _ _] := sdprodP defM; rewrite defF in defM.
have hallMs: \sigma(M).-Hall(M) Ms by apply: Msigma_Hall.
have hallF: \sigma(M)^'.-Hall(M) F by apply/(sdprod_Hall_pcoreP hallMs).
have frF: [Frobenius F = U ><| K] by apply/Frobenius_semiregularP.
have ntMs: Ms != 1 by apply: Msigma_neq1.
have prK: prime #|K|.
  have [solF [_ _ nMsF _]] := (sigma_compl_sol hallF, sdprodP defM).
  have solMs: solvable Ms := solvableS (pcore_sub _ _) (mmax_sol maxM).
  have coMsF: coprime #|Ms| #|F|.
    by rewrite (coprime_sdprod_Hall_r defM) (pHall_Hall hallF).
  by have [] := Frobenius_primact frF solF nMsF solMs ntMs coMsF prMsK.
have eq_sb: \sigma(M) =i \beta(M).
  suffices bMs: \beta(M).-group Ms.
    move=> p; apply/idP/idP=> [sp|]; last exact: beta_sub_sigma.
    rewrite (pnatPpi bMs) //= (card_Hall (Msigma_Hall maxM)) pi_of_part //.
    by rewrite inE /= sigma_sub_pi.
  have [H hallH cHF'] := der_compl_cent_beta' maxM hallF.
  rewrite -pgroupNK -partG_eq1 -(card_Hall hallH) -trivg_card1 -subG1.
  rewrite -regMsU subsetI (pHall_sub hallH) centsC (subset_trans _ cHF') //.
  have [solU [_ mulUK nUK _]] := (abelian_sol cUU, sdprodP defF).
  have coUK: coprime #|U| #|K|.
    rewrite (p'nat_coprime (sub_pgroup _ (pHall_pgroup hallU)) kK) // => p.
    by case/norP.
  rewrite -(coprime_cent_prod nUK) // (cent_semiregular regUK) // mulg1.
  by rewrite -mulUK commgSS ?mulG_subl ?mulG_subr.
split=> //; apply/normedTI_P; rewrite setD_eq0 subG1 setTI normD1 gFnorm.
split=> // g _; rewrite -setI_eq0 conjD1g -setDIl setD_eq0 subG1 /= -/Ms.
have [_ _ b'MsMg] := sigma_compl_embedding maxM hallE.
apply: contraR => notMg; have{b'MsMg notMg} [_ b'MsMg _] := b'MsMg g notMg.
rewrite -{2}(setIidPr (pHall_sub hallMs)) conjIg setIA coprime_TIg // cardJg.
by apply: p'nat_coprime b'MsMg _; rewrite -(eq_pnat _ eq_sb).
Qed.

(* This is essentially the skolemized form of 14.2(a). *)
Lemma kappa_compl_context M U K :
    M \in 'M -> kappa_complement M U K ->
  [/\ \sigma(M)^'.-Hall(M) (U <*> K),
      M`_\sigma ><| (U ><| K) = M,
      semiprime M`_\sigma K,
      semiregular U K
    & K :!=: 1 -> abelian U].
Proof.
move=> maxM [hallU hallK gsetUK]; set E := U <*> K.
have mulUK: U * K = E by rewrite -(gen_set_id gsetUK) genM_join.
have [[sKM kK _] [sUM sk'U _]] := (and3P hallK, and3P hallU).
have tiUK: U :&: K = 1.
  by apply: coprime_TIg (p'nat_coprime (sub_pgroup _ sk'U) kK) => p; case/norP.
have hallE: \sigma(M)^'.-Hall(M) E.
  rewrite pHallE /= -/E -mulUK mul_subG //= TI_cardMg //.
  rewrite -(partnC \kappa(M) (part_gt0 _ _)) (partn_part _ (@kappa_sigma' M)).
  apply/eqP; rewrite -partnI -(card_Hall hallK) mulnC; congr (_ * _)%N.
  by rewrite (card_Hall hallU); apply: eq_partn => p; apply: negb_or. 
have [K1 | ntK] := altP (K :=P: 1).
  rewrite K1 sdprodg1 -{1}(mulg1 U) -{1}K1 mulUK sdprod_sigma //.
  by split=> //; first apply: semiregular_prime; apply: semiregular1r.
have PmaxM: M \in 'M_'P by rewrite inE maxM -(trivg_kappa maxM hallK) andbT.
have [[V [complV defM] [cVV prK regK]] _ _ _ _] := Ptype_structure PmaxM hallK.
have [[_ F _ defF] _ _ _] := sdprodP defM; rewrite defF in defM.
have hallF: \sigma(M)^'.-Hall(M) F.
  exact/(sdprod_Hall_pcoreP (Msigma_Hall maxM)).
have [a Ma /= defFa] := Hall_trans (mmax_sol maxM) hallE hallF.
have [hallV _ _] := complV; set sk' := \sigma_kappa(M)^' in hallU hallV sk'U.
have [nsVF sKF _ _ _] := sdprod_context defF.
have [[[sVF _] [sFM _]] [sEM _]] := (andP nsVF, andP hallF, andP hallE).
have hallV_F: sk'.-Hall(F) V := pHall_subl sVF sFM hallV.
have hallU_E: sk'.-Hall(E) U := pHall_subl (joing_subl _ _) sEM hallU.
have defV: 'O_sk'(F) = V := normal_Hall_pcore hallV_F nsVF.
have hallEsk': sk'.-Hall(E) 'O_sk'(E).
  by rewrite [E]defFa pcoreJ pHallJ2 /= defV.
have defU: 'O_sk'(E) = U by rewrite (eq_Hall_pcore hallEsk' hallU_E).
have nUE: E \subset 'N(U) by rewrite -defU gFnorm.
have hallK_E: \kappa(M).-Hall(E) K := pHall_subl (joing_subr _ _) sEM hallK.
have hallK_F: \kappa(M).-Hall(F) K := pHall_subl sKF sFM hallK.
have hallKa_E: \kappa(M).-Hall(E) (K :^ a) by rewrite [E]defFa pHallJ2.
have [b Eb /= defKab] := Hall_trans (sigma_compl_sol hallE) hallK_E hallKa_E.
have defVa: V :^ a = U by rewrite -defV -pcoreJ -defFa defU.
split=> // [| x Kx | _]; last by rewrite -defVa abelianJ.
  by rewrite [U ><| K]sdprodEY ?sdprod_sigma //; case/joing_subP: nUE.
rewrite -(conjgKV (a * b) x) -(normsP nUE b Eb) -defVa -conjsgM.
rewrite -cent_cycle cycleJ centJ -conjIg cent_cycle regK ?conjs1g //.
by rewrite -mem_conjg conjD1g conjsgM -defKab.
Qed.

(* This is B & G, Corollary 14.3. *)
Corollary pi_of_cent_sigma M x x' :
    M \in 'M -> x \in (M`_\sigma)^# ->
    x' \in ('C_M[x])^# -> \sigma(M)^'.-elt x' ->
     (*1*)  \kappa(M).-elt x' /\ 'C[x] \subset M
  \/ (*2*) [/\ \tau2(M).-elt x', \ell_\sigma(x') == 1%N & 'M('C[x']) = [set M]].
Proof.
move: x' => y maxM /setD1P[ntx Ms_x] /setD1P[nty cMxy] s'y.
have [My cxy] := setIP cMxy.
have [t2y | not_t2y] := boolP (\tau2(M).-elt y); [right | left].
  have uniqCy: 'M('C[y]) = [set M]; last split=> //.
    apply: cent1_nreg_sigma_uniq; rewrite // ?inE ?nty //.
    by apply/trivgPn; exists x; rewrite // inE Ms_x cent1C.
  pose p := pdiv #[y]; have piYp: p \in \pi(#[y]) by rewrite pi_pdiv order_gt1.
  have t2p := pnatPpi t2y piYp; have [E hallE] := ex_sigma_compl maxM.
  have [A Ep2A _] := ex_tau2Elem hallE t2p.
  have pA: p.-group A by case/pnElemP: Ep2A => _ /andP[].
  have ntA: A :!=: 1 by rewrite (nt_pnElem Ep2A).
  have [H maxNH] := mmax_exists (mFT_norm_proper ntA (mFT_pgroup_proper pA)).
  have [st2MsH _ _] := primes_norm_tau2Elem maxM hallE t2p Ep2A maxNH.
  have [maxH _] := setIdP maxNH.
  have sHy: \sigma(H).-elt y by apply: sub_p_elt t2y => q /st2MsH/andP[].
  rewrite /sigma_length (cardsD1 y.`_(\sigma(H))).
  rewrite mem_sigma_decomposition //; last by rewrite constt_p_elt.
  rewrite eqSS -sigma_decomposition_constt' //.
  by apply/ell_sigma0P; rewrite (constt1P _) ?p_eltNK.
have{not_t2y} [p piYp t2'p]: exists2 p, p \in \pi(#[y]) & p \notin \tau2(M).
  by apply/allPn; rewrite negb_and cardG_gt0 in not_t2y.
have sYM: <[y]> \subset M by rewrite cycle_subG.
have piMp: p \in \pi(M) := piSg sYM piYp.
have t13p: p \in [predU \tau1(M) & \tau3(M)].
  move: piMp; rewrite partition_pi_mmax // (negPf t2'p) /= orbA.
  by case/orP=> // sMy; case/negP: (pnatPpi s'y piYp).
have [X]: exists X, X \in 'E_p^1(<[y]>) by apply/p_rank_geP; rewrite p_rank_gt0.
rewrite -(setIidPr sYM) pnElemI -setIdE => /setIdP[EpX sXy].
have kp: p \in \kappa(M).
  rewrite unlock; apply/andP; split=> //; apply/exists_inP; exists X => //.
  apply/trivgPn; exists x; rewrite // inE Ms_x (subsetP (centS sXy)) //.
  by rewrite cent_cycle cent1C.
have [sXM abelX dimX] := pnElemP EpX; have [pX _] := andP abelX.
have [K hallK sXK] := Hall_superset (mmax_sol maxM) sXM (pi_pgroup pX kp).
have PmaxM: M \in 'M_'P.
  by rewrite 2!inE maxM andbT; apply: contraL kp => k'M; exact: (pnatPpi k'M).
have [_ [defNK defNX] [_ uniqCKs] _ _] := Ptype_structure PmaxM hallK.
have{defNX} sCMy_nMK: 'C_M[y] \subset 'N_M(K).
  have [|<- _] := defNX X.
    by apply/nElemP; exists p; rewrite !inE sXK abelX dimX.
  by rewrite setIS // cents_norm // -cent_cycle centS.
have [[sMK kK _] [_ mulKKs cKKs _]] := (and3P hallK, dprodP defNK).
have s'K: \sigma(M)^'.-group K := sub_pgroup (@kappa_sigma' M) kK.
have sMs: \sigma(M).-group M`_\sigma := pcore_pgroup _ M.
have sKs: \sigma(M).-group 'C_(M`_\sigma)(K) := pgroupS (subsetIl _ _) sMs.
have{s'K sKs} [hallK_N hallKs] := coprime_mulGp_Hall mulKKs s'K sKs.
split.
  rewrite (mem_p_elt kK) // (mem_normal_Hall hallK_N) ?normal_subnorm //.
  by rewrite (subsetP sCMy_nMK) // inE My cent1id.
have Mx: x \in M := subsetP (pcore_sub _ _) x Ms_x.
have sxKs: <[x]> \subset 'C_(M`_\sigma)(K).
  rewrite cycle_subG (mem_normal_Hall hallKs) ?(mem_p_elt sMs) //=.
    by rewrite -mulKKs /normal mulG_subr mulG_subG normG cents_norm // centsC.
  by rewrite (subsetP sCMy_nMK) // inE Mx cent1C.
have /rank_geP[Z]: 0 < 'r(<[x]>) by rewrite rank_gt0 cycle_eq1.
rewrite /= -(setIidPr sxKs) nElemI -setIdE => /setIdP[E1KsZ sZx].
have [_ sCZM] := mem_uniq_mmax (uniqCKs Z E1KsZ).
by rewrite (subset_trans _ sCZM) // -cent_cycle centS.
Qed.

(* This is B & G, Theorem 14.4. *)
(* We are omitting the first half of part (a), since we have taken it as our  *)
(* definition of 'R[x].                                                       *)
Theorem FT_signalizer_context x (N := 'N[x]) (R := 'R[x]) :
    \ell_\sigma(x) == 1%N ->
  [/\ [/\ [transitive R, on 'M_\sigma[x] | 'JG],
          #|R| = #|'M_\sigma[x]|,
          R <| 'C[x]
        & Hall 'C[x] R]
   & #|'M_\sigma[x]| > 1 ->
  [/\ 'M('C[x]) = [set N],
    (*a*) R :!=: 1,
    (*c1*) \tau2(N).-elt x,
     (*f*) N \in 'M_'F :|: 'M_'P2
    & {in 'M_\sigma[x], forall M,
  [/\ (*b*) R ><| 'C_(M :&: N)[x] = 'C[x],
     (*c2*) {subset \tau2(N) <= \sigma(M)},
      (*d*) {subset [predI \pi(M) & \sigma(N)] <= \beta(N)}
    & (*e*) \sigma(N)^'.-Hall(N) (M :&: N)]}]].
Proof.
rewrite {}/N {}/R => ell1x; have [ntx ntMSx] := ell_sigma1P x ell1x.
have [M MSxM] := set0Pn _ ntMSx; have [maxM Ms_x] := setIdP MSxM.
rewrite cycle_subG in Ms_x; have sMx := mem_p_elt (pcore_pgroup _ M) Ms_x.
have Mx: x \in M := subsetP (pcore_sub _ _) x Ms_x.
have [MSx_le1 | MSx_gt1] := leqP _ 1.
  rewrite /'R[x] /'N[x] ltnNge MSx_le1 (trivgP (pcore_sub _ _)) setI1g normal1.
  have <-: [set M] = 'M_\sigma[x].
    by apply/eqP; rewrite eqEcard sub1set MSxM cards1.
  by rewrite /Hall atrans_acts_card ?imset_set1 ?cards1 ?sub1G ?coprime1n.
have [q pi_x_q]: exists q, q \in \pi(#[x]).
  by exists (pdiv #[x]); rewrite pi_pdiv order_gt1.
have{sMx} sMq: q \in \sigma(M) := pnatPpi sMx pi_x_q.
have [X EqX]: exists X, X \in 'E_q^1(<[x]>).
  by apply/p_rank_geP; rewrite p_rank_gt0.
have [sXx abelX dimX] := pnElemP EqX; have [qX cXX _] := and3P abelX.
have ntX: X :!=: 1 := nt_pnElem EqX isT.
have sXM: X \subset M by rewrite (subset_trans sXx) ?cycle_subG.
have [N maxNX_N] := mmax_exists (mFT_norm_proper ntX (mFT_pgroup_proper qX)).
have [maxN sNX_N] := setIdP maxNX_N; pose R := 'C_(N`_\sigma)[x]%G.
have sCX_N: 'C(X) \subset N := subset_trans (cent_sub X) sNX_N.
have sCx_N: 'C[x] \subset N by rewrite -cent_cycle (subset_trans (centS sXx)).
have sMSx_MSX: 'M_\sigma[x] \subset 'M_\sigma(X).
  apply/subsetP=> M1 /setIdP[maxM1 sxM1].
  by rewrite inE maxM1 (subset_trans sXx).
have nsRCx: R <| 'C[x] by rewrite /= setIC (normalGI sCx_N) ?pcore_normal.
have hallR: \sigma(N).-Hall('C[x]) R.
  exact: setI_normal_Hall (pcore_normal _ _) (Msigma_Hall maxN) sCx_N.
have transCX: [transitive 'C(X), on 'M_\sigma(X) | 'JG].
  have [_ trCX _ ] := sigma_group_trans maxM sMq qX.
  case/imsetP: trCX => _ /setIdP[/imsetP[y _ ->] sXMy] trCX.
  have maxMy: (M :^ y)%G \in 'M by rewrite mmaxJ.
  have sXMys: X \subset (M :^ y)`_\sigma.
    by rewrite (sub_Hall_pcore (Msigma_Hall _)) // (pi_pgroup qX) ?sigmaJ.
  apply/imsetP; exists (M :^ y)%G; first exact/setIdP.
  apply/setP=> Mz; apply/setIdP/imsetP=> [[maxMz sXMzs] | [z cXz -> /=]].
    suffices: gval Mz \in orbit 'Js 'C(X) (M :^ y).
      by case/imsetP=> z CXz /group_inj->; exists z.
    rewrite -trCX inE andbC (subset_trans sXMzs) ?pcore_sub //=.
    apply/idPn => /(sigma_partition maxM maxMz)/=/(_ q)/idP[].
    rewrite inE /= sMq (pnatPpi (pgroupS sXMzs (pcore_pgroup _ _))) //.
    by rewrite -p_rank_gt0 p_rank_abelem ?dimX.
  by rewrite mmaxJ -(normP (subsetP (cent_sub X) z cXz)) MsigmaJ conjSg.
have MSX_M: M \in 'M_\sigma(X) := subsetP sMSx_MSX M MSxM.
have not_sCX_M: ~~ ('C(X) \subset M).
  apply: contraL MSx_gt1 => sCX_M.
  rewrite -leqNgt (leq_trans (subset_leq_card sMSx_MSX)) //.
  rewrite -(atransP transCX _ MSX_M) card_orbit astab1JG.
  by rewrite (setIidPl (normsG sCX_M)) indexgg.
have neqNM: N :!=: M by apply: contraNneq not_sCX_M => <-.
have maxNX'_N: N \in 'M('N(X)) :\ M by rewrite 2!inE neqNM.
have [notMGN _] := sigma_subgroup_embedding maxM sMq sXM qX ntX maxNX'_N.
have sN'q: q \notin \sigma(N).
  by apply: contraFN (sigma_partition maxM maxN notMGN q) => sNq; exact/andP.
rewrite (negPf sN'q) => [[t2Nq s_piM_bN hallMN]].
have defN: N`_\sigma ><| (M :&: N) = N.
  exact/(sdprod_Hall_pcoreP (Msigma_Hall maxN)).
have Nx: x \in N by rewrite (subsetP sCx_N) ?cent1id.
have MNx: x \in M :&: N by rewrite inE Mx.
have sN'x: \sigma(N)^'.-elt x by rewrite (mem_p_elt (pHall_pgroup hallMN)).
have /andP[sNsN nNsN]: N`_\sigma <| N := pcore_normal _ _.
have nNs_x: x \in 'N(N`_\sigma) := subsetP nNsN x Nx.
have defCx: R ><| 'C_(M :&: N)[x] = 'C[x].
  rewrite -{2}(setIidPr sCx_N) /= -cent_cycle (subcent_sdprod defN) //.
  by rewrite subsetI andbC normsG ?cycle_subG.
have transR: [transitive R, on 'M_\sigma[x] | 'JG].
  apply/imsetP; exists M => //; apply/setP=> L.
  apply/idP/imsetP=> [MSxL | [u Ru ->{L}]]; last first.
    have [_ cxu] := setIP Ru; rewrite /= -cent_cycle in cxu.
    by rewrite -(normsP (cent_sub _) u cxu) sigma_mmaxJ.
  have [u cXu defL] := atransP2 transCX MSX_M (subsetP sMSx_MSX _ MSxL).
  have [_ mulMN nNsMN tiNsMN] := sdprodP defN.
  have:= subsetP sCX_N u cXu; rewrite -mulMN -normC //.
  case/imset2P=> v w /setIP[Mv _] Ns_w def_u; exists w => /=; last first.
    by apply: group_inj; rewrite defL /= def_u conjsgM (conjGid Mv).
  rewrite inE Ns_w -groupV (sameP cent1P commgP) -in_set1 -set1gE -tiNsMN.
  rewrite setICA setIC (setIidPl sNsN) inE groupMl ?groupV //.
  rewrite memJ_norm // groupV Ns_w /= -(norm_mmax maxM) inE sub_conjg.
  rewrite invg_comm -(conjSg _ _ w) -{2}(conjGid Mx) -!conjsgM -conjg_Rmul.
  rewrite -conjgC conjsgM -(conjGid Mv) -(conjsgM M) -def_u.
  rewrite -[M :^ u](congr_group defL) conjGid // -cycle_subG.
  by have [_ Ls_x] := setIdP MSxL; rewrite (subset_trans Ls_x) ?pcore_sub.
have oR: #|R| = #|'M_\sigma[x]|.
  rewrite -(atransP transR _ MSxM) card_orbit astab1JG (norm_mmax maxM).
  rewrite -setIAC  /= -{3}(setIidPl sNsN) -(setIA _ N) -(setIC M).
  by have [_ _ _ ->] :=  sdprodP defN; rewrite setI1g indexg1.
have ntR: R :!=: 1 by rewrite -cardG_gt1 oR.
have [y Ns_y CNy_x]: exists2 y, y \in (N`_\sigma)^# & x \in ('C_N[y])^#.
  have [y Ry nty] := trivgPn _ ntR; have [Ns_y cxy] := setIP Ry.
  by exists y; rewrite 2!inE ?nty // inE Nx cent1C ntx.
have kN'q: q \notin \kappa(N).
  rewrite (contra (@kappa_tau13 N q)) // negb_or (contraL (@tau2'1 _ _ _)) //.
  exact: tau3'2.
have [[kNx _] | [t2Nx _ uniqN]] := pi_of_cent_sigma maxN Ns_y CNy_x sN'x.
  by case/idPn: (pnatPpi kNx pi_x_q).
have defNx: 'N[x] = N.
  apply/set1P; rewrite -uniqN /'N[x] MSx_gt1.
  by case: pickP => // /(_ N); rewrite uniqN /= set11.
rewrite /'R[x] {}defNx -(erefl (gval R)) (pHall_Hall hallR).
split=> // _; split=> // [|L MSxL].
  rewrite !(maxN, inE) /=; case: (pgroup _ _) => //=; rewrite andbT.
  apply: contra kN'q => skN_N; have:= pnatPpi (mem_p_elt skN_N Nx) pi_x_q.
  by case/orP=> //=; rewrite (negPf sN'q).
have [u Ru ->{L MSxL}] := atransP2 transR MSxM MSxL; rewrite /= cardJg.
have [Ns_u cxu] := setIP Ru; have Nu := subsetP sNsN u Ns_u.
rewrite -{1}(conjGid Ru) -(conjGid cxu) -{1 6 7}(conjGid Nu) -!conjIg pHallJ2.
split=> // [|p t2Np].
  rewrite /= -(setTI 'C[x]) -!(setICA setT) -!morphim_conj.
  exact: injm_sdprod (subsetT _) (injm_conj _ _) defCx.
have [A Ep2A _] := ex_tau2Elem hallMN t2Np.
have [[nsAMN _] _ _ _] := tau2_compl_context maxN hallMN t2Np Ep2A.
have{Ep2A} Ep2A: A \in 'E_p^2(M) by move: Ep2A; rewrite pnElemI; case/setIP.
have rpM: 'r_p(M) > 1 by apply/p_rank_geP; exists A.
have: p \in \pi(M) by rewrite -p_rank_gt0 ltnW.
rewrite sigmaJ partition_pi_mmax // !orbA; case/orP=> //.
rewrite orbAC -2!andb_orr -(subnKC rpM) andbF /= => t2Mp.
case/negP: ntX; rewrite -subG1 (subset_trans sXx) //.
have [_ _ <- _ _] := tau2_context maxM t2Mp Ep2A.
have [[sAM abelA _] [_ nAMN]] := (pnElemP Ep2A, andP nsAMN).
rewrite -coprime_norm_cent ?(subset_trans sAM) ?gFnorm //.
  by rewrite cycle_subG inE Ms_x (subsetP nAMN).
have [[sM'p _] [pA _]] := (andP t2Mp, andP abelA).
exact: pnat_coprime (pcore_pgroup _ _) (pi_pgroup pA sM'p).
Qed.

(* A useful supplement to Theorem 14.4. *)
Lemma cent1_sub_uniq_sigma_mmax x M :
  #|'M_\sigma[x]| == 1%N -> M \in 'M_\sigma[x] -> 'C[x] \subset M.
Proof.
move: M => M0 /cards1P[M defMSx] MS_M0; move: MS_M0 (MS_M0).
rewrite {1}defMSx => /set1P->{M0} MSxM; have [maxM _] := setIdP MSxM.
rewrite -(norm_mmax maxM); apply/normsP=> y cxy; apply: congr_group.
by apply/set1P; rewrite -defMSx -(mulKg y x) (cent1P cxy) cycleJ sigma_mmaxJ.
Qed.

Remark cent_FT_signalizer x : x \in 'C('R[x]).
Proof. by rewrite -sub_cent1 subsetIr. Qed.

(* Because the definition of 'N[x] uses choice, we can only prove it commutes *)
(* with conjugation now that we have established that the choice is unique.   *)
Lemma FT_signalizer_baseJ x z : 'N[x ^ z] :=: 'N[x] :^ z.
Proof.
case MSx_gt1: (#|'M_\sigma[x]| > 1); last first.
  by rewrite /'N[x] /'N[_] cycleJ card_sigma_mmaxJ MSx_gt1 conjs1g.
have [x1 | ntx] := eqVneq x 1.
  rewrite x1 conj1g /'N[1] /= norm1.
  case: pickP => [M maxTM | _]; last by rewrite if_same conjs1g.
  by have [maxM] := setIdP maxTM; case/idPn; rewrite proper_subn ?mmax_proper.
apply: congr_group; apply/eqP; rewrite eq_sym -in_set1.
have ell1xz: \ell_\sigma(x ^ z) == 1%N.
  by rewrite ell_sigmaJ; apply/ell_sigma1P; rewrite -cards_eq0 -lt0n ltnW.
have [_ [|<- _ _ _ _]] := FT_signalizer_context ell1xz.
  by rewrite cycleJ card_sigma_mmaxJ.
rewrite -conjg_set1 normJ mmax_ofJ; rewrite ell_sigmaJ in ell1xz.
by have [_ [//|-> _ _ _ _]] := FT_signalizer_context ell1xz; apply: set11.
Qed.

Lemma FT_signalizerJ x z : 'R[x ^ z] :=: 'R[x] :^ z.
Proof.
by rewrite /'R[x] /'R[_] FT_signalizer_baseJ MsigmaJ -conjg_set1 normJ conjIg.
Qed.

Lemma sigma_coverJ x z : x ^ z *: 'R[x ^ z] = (x *: 'R[x]) :^ z.
Proof. by rewrite FT_signalizerJ conjsMg conjg_set1. Qed.

Lemma sigma_supportJ M z : (M :^ z)^~~ = M^~~ :^ z.
Proof.
rewrite -bigcupJ /_^~~ MsigmaJ -conjD1g (big_imset _ (in2W (act_inj 'J z))) /=.
by apply: eq_bigr => x _; rewrite sigma_coverJ.
Qed.

(* This is the remark imediately above B & G, Lemma 14.5; note the adjustment *)
(* allowing for the case x' = 1. *)
Remark sigma_cover_decomposition x x' :
    \ell_\sigma(x) == 1%N -> x' \in 'R[x] ->
  sigma_decomposition (x * x') = x |: [set x']^#.
Proof.
move=> ell1x Rx'; have [-> | ntx'] := eqVneq x' 1.
  by rewrite mulg1 setDv setU0 ell1_decomposition.
rewrite setDE (setIidPl _) ?sub1set ?inE // setUC.
have ntR: #|'R[x]| > 1 by rewrite cardG_gt1; apply/trivgPn; exists x'.
have [Ns_x' cxx'] := setIP Rx'; move/cent1P in cxx'.
have [[_ <- _ _] [//| maxN _ t2Nx _ _]] := FT_signalizer_context ell1x.
have{maxN} [maxN _] := mem_uniq_mmax maxN.
have sNx' := mem_p_elt (pcore_pgroup _ _) Ns_x'.
have sN'x: \sigma('N[x])^'.-elt x by apply: sub_p_elt t2Nx => p /andP[].
have defx': (x * x').`_\sigma('N[x]) = x'.
  by rewrite consttM // (constt1P sN'x) mul1g constt_p_elt.
have sd_xx'_x': x' \in sigma_decomposition (x * x').
  by rewrite 2!inE ntx' -{1}defx'; apply: mem_imset.
rewrite -(setD1K sd_xx'_x') -{3}defx' -sigma_decomposition_constt' ?consttM //.
by rewrite constt_p_elt // (constt1P _) ?p_eltNK ?mulg1 // ell1_decomposition.
Qed.

(* This is the simplified form of remark imediately above B & G, Lemma 14.5. *)
Remark nt_sigma_cover_decomposition x x' :
    \ell_\sigma(x) == 1%N -> x' \in 'R[x]^# ->
  sigma_decomposition (x * x') = [set x; x'].
Proof.
move=> ell1x /setD1P[ntx' Rx']; rewrite sigma_cover_decomposition //.
by rewrite setDE (setIidPl _) ?sub1set ?inE // setUC.
Qed.

Remark mem_sigma_cover_decomposition x g :
  \ell_\sigma(x) == 1%N -> g \in x *: 'R[x] -> x \in sigma_decomposition g.
Proof.
by move=> ell1x /lcosetP[x' Rx' ->]; rewrite sigma_cover_decomposition ?setU11.
Qed.

Remark ell_sigma_cover x g :
  \ell_\sigma(x) == 1%N -> g \in x *: 'R[x] -> \ell_\sigma(g) <= 2.
Proof.
move=> ell1x /lcosetP[x' Rx' ->].
rewrite /(\ell_\sigma(_)) sigma_cover_decomposition // cardsU1.
by rewrite (leq_add (leq_b1 _)) // -(cards1 x') subset_leq_card ?subsetDl.
Qed.

Remark ell_sigma_support M g : M \in 'M -> g \in M^~~ -> \ell_\sigma(g) <= 2.
Proof.
by move=> maxM /bigcupP[x Msx]; apply: ell_sigma_cover; apply: Msigma_ell1 Msx.
Qed.

(* This is B & G, Lemma 14.5(a). *)
Lemma sigma_cover_disjoint x y :
    \ell_\sigma(x) == 1%N -> \ell_\sigma(y) == 1%N -> x != y ->
  [disjoint x *: 'R[x] & y *: 'R[y]].
Proof.
move=> ell1x ell1y neq_xy; apply/pred0P=> g /=.
have [[ntx _] [nty _]] := (ell_sigma1P x ell1x, ell_sigma1P y ell1y).
apply: contraNF (ntx) => /andP[/lcosetP[x' Rxx' ->{g}] /= yRy_xx'].
have def_y: y = x'.
  apply: contraTeq (mem_sigma_cover_decomposition ell1y yRy_xx') => neq_yx'.
  by rewrite sigma_cover_decomposition // !inE negb_or nty eq_sym neq_xy.
have [[_ <- _ _] [|uniqCx _ _ _ _]] := FT_signalizer_context ell1x.
  by rewrite cardG_gt1; apply/trivgPn; exists x'; rewrite // -def_y.
have{uniqCx} [maxNx sCxNx] := mem_uniq_mmax uniqCx.
have Rx_y: y \in 'R[x] by [rewrite def_y]; have [Nxs_y cxy] := setIP Rx_y.
have Ry_x: x \in 'R[y].
  by rewrite -def_y -(cent1P cxy) mem_lcoset mulKg in yRy_xx'.
have MSyNx: 'N[x] \in 'M_\sigma[y] by rewrite inE maxNx cycle_subG.
have [[_ <- _ _] [|uniqCy _ _ _]] := FT_signalizer_context ell1y.
  by rewrite cardG_gt1; apply/trivgPn; exists x.
have{uniqCy} [_ sCyNy] := mem_uniq_mmax uniqCy.
case/(_ 'N[x] MSyNx)=> /sdprodP[_ _ _ tiRyNx] _ _ _.
rewrite -in_set1 -set1gE -tiRyNx -setIA (setIidPr sCyNy) inE Ry_x /=.
by rewrite inE cent1C cxy (subsetP sCxNx) ?cent1id.
Qed.

(* This is B & G, Lemma 14.5(b). *)
Lemma sigma_support_disjoint M1 M2 :
  M1 \in 'M -> M2 \in 'M -> gval M2 \notin M1 :^: G -> [disjoint M1^~~ & M2^~~].
Proof.
move=> maxM1 maxM2 notM1GM2; rewrite -setI_eq0 -subset0 big_distrl.
apply/bigcupsP=> x M1s_x; rewrite big_distrr; apply/bigcupsP=> y M2s_y /=.
have [ell1x ell1y] := (Msigma_ell1 maxM1 M1s_x, Msigma_ell1 maxM2 M2s_y).
rewrite subset0 setI_eq0 sigma_cover_disjoint //.
have{M1s_x M2s_y}[[ntx M1s_x] [_ M2s_y]] := (setD1P M1s_x, setD1P M2s_y).
pose p := pdiv #[x]; have pixp: p \in \pi(#[x]) by rewrite pi_pdiv order_gt1.
apply: contraFN (sigma_partition maxM1 maxM2 notM1GM2 p) => eq_xy.
rewrite inE /= (pnatPpi (mem_p_elt (pcore_pgroup _ _) M1s_x)) //=.
by rewrite (pnatPpi (mem_p_elt (pcore_pgroup _ _) M2s_y)) -?(eqP eq_xy).
Qed.

(* This is B & G, Lemma 14.5(c). *)
Lemma card_class_support_sigma M :
  M \in 'M -> #|class_support M^~~ G| = (#|M`_\sigma|.-1 * #|G : M|)%N.
Proof.
move=> maxM; rewrite [#|M`_\sigma|](cardsD1 1) group1 /=.
set MsG := class_support (M`_\sigma)^# G; pose P := [set x *: 'R[x] | x in MsG].
have ellMsG x: x \in MsG -> \ell_\sigma(x) == 1%N.
  by case/imset2P=> y z My _ ->; rewrite ell_sigmaJ (Msigma_ell1 maxM).
have tiP: trivIset P.
  apply/trivIsetP=> _ _ /imsetP[x MsGx ->] /imsetP[y MsGy ->] neq_xRyR.
  by rewrite sigma_cover_disjoint ?ellMsG //; apply: contraNneq neq_xRyR => ->.
have->: class_support M^~~ G = cover P.
  apply/setP=> az; apply/imset2P/bigcupP=> [[a z] | [xRz]].
    case/bigcupP=> x Ms_x xRa Gz ->; exists (x ^ z *: 'R[x ^ z]).
      by apply: mem_imset; exact: mem_imset2.
    by rewrite sigma_coverJ memJ_conjg.
  case/imsetP=> _ /imset2P[x z Ms_x Gz ->] ->; rewrite sigma_coverJ.
  by case/imsetP=> a xRa ->; exists a z => //; apply/bigcupP; exists x.
rewrite -(eqnP tiP) big_imset /= => [|x y MsGx MsGy eq_xyR]; last first.
  have: x *: 'R[x] != set0 by rewrite -cards_eq0 -lt0n card_lcoset cardG_gt0.
  rewrite -[x *: _]setIid {2}eq_xyR setI_eq0.
  by apply: contraNeq => neq_xy; rewrite sigma_cover_disjoint ?ellMsG.
rewrite -{2}(norm_mmax maxM) -astab1JG -indexgI -card_orbit.
set MG := orbit _ G M; rewrite mulnC -sum_nat_const.
transitivity (\sum_(Mz in MG) \sum_(x in (Mz`_\sigma)^#) 1); last first.
  apply: eq_bigr => _ /imsetP[z _ ->]; rewrite sum1_card MsigmaJ.
  by rewrite -conjD1g cardJg.
rewrite (exchange_big_dep (mem MsG)) /= => [|Mz xz]; last first.
  case/imsetP=> z Gz ->; rewrite MsigmaJ -conjD1g => /imsetP[x Ms_x ->{xz}].
  exact: mem_imset2.
apply: eq_bigr => x MsGx; rewrite card_lcoset sum1dep_card.
have ell1x := ellMsG x MsGx; have [ntx _] := ell_sigma1P x ell1x.
have [[transRx -> _ _] _] := FT_signalizer_context ell1x.
apply: eq_card => Mz; rewrite 2!inE cycle_subG in_setD1 ntx /=.
apply: andb_id2r => Mzs_x.
apply/idP/imsetP=> [maxMz | [z _ ->]]; last by rewrite mmaxJ.
have [y t Ms_y _ def_x] := imset2P MsGx; have{Ms_y} [_ Ms_y] := setD1P Ms_y.
have [MSxMz MSxMt]: Mz \in 'M_\sigma[x] /\ (M :^ t)%G \in 'M_\sigma[x].
  by rewrite {2}def_x cycleJ sigma_mmaxJ inE maxMz inE maxM !cycle_subG.
have [z _ ->] := atransP2 transRx MSxMt MSxMz.
by exists (t * z); rewrite ?inE ?actM.
Qed.

(* This is B & G, Lemma 14.6. *)
Lemma sigma_decomposition_dichotomy (g : gT) :
   g != 1 ->
     [exists (x | \ell_\sigma(x) == 1%N), x^-1 * g \in 'R[x]]
 (+) [exists (y | \ell_\sigma(y) == 1%N),
      let y' := y^-1 * g in
      [exists M in 'M_\sigma[y], (y' \in ('C_M[y])^#) && \kappa(M).-elt y']].
Proof.
move=> ntg; have [[x ell1x Rx'] | ] := altP exists_inP.
  rewrite /= negb_exists_in; apply/forall_inP=> y ell1y.
  set y' := y^-1 * g; set x' := x^-1 * g in Rx'.
  apply/existsP=> -[M /and3P[MSyM CMy_y' kMy']].
  have [maxM Ms_y] := setIdP MSyM; rewrite cycle_subG in Ms_y.
  have [nty'] := setD1P CMy_y'; case/setIP=> My'; move/cent1P=> cyy'.
  have [[nty _] sMy]:= (ell_sigma1P y ell1y, mem_p_elt (pcore_pgroup _ _) Ms_y).
  have sM'y': \sigma(M)^'.-elt y' := sub_p_elt (@kappa_sigma' M) kMy'.
  have t2M'y': \tau2(M)^'.-elt y'.
    apply: sub_p_elt kMy' => p; move/kappa_tau13.
    by case/orP; [apply: tau2'1 | apply: contraL; apply: tau3'2].
  have xx'_y: y \in pred2 x x'.
    suffices: y \in x |: [set x']^# by rewrite !inE nty.
    rewrite -sigma_cover_decomposition // mulKVg 2!inE nty /=.
    apply/imsetP; exists M => //; rewrite -(mulKVg y g) -/y' consttM //.
    by rewrite (constt_p_elt sMy) (constt1P sM'y') mulg1.
  have nt_x': x' != 1 by case/pred2P: xx'_y; rewrite /x' => <-.
  have maxCY_M: M \in 'M('C[y]).
    have Ms1_y: y \in (M`_\sigma)^# by apply/setD1P.
    rewrite inE maxM; case/pi_of_cent_sigma: CMy_y' => // [[//] | [t2y']].
    by rewrite -order_eq1 (pnat_1 t2y' t2M'y') in nty'.
  have [[_ <- _ _] [|uniqNx _ t2Nx _ _]] := FT_signalizer_context ell1x.
    by rewrite cardG_gt1; apply/trivgPn; exists x'.
  rewrite -order_gt1 (pnat_1 sMy _) // -/(_.-elt _) in nty.
  have{xx'_y} [eq_yx | eq_yx']: y = x \/ y = x' := pred2P xx'_y.
    rewrite eq_yx uniqNx in maxCY_M *; rewrite (set1P maxCY_M).
    by apply: sub_p_elt t2Nx => p; case/andP.
  have eq_xy': x = y' by apply: (mulIg y); rewrite cyy' {1}eq_yx' !mulKVg.
  have [[z _ defM] | notMGNx] := altP (@orbitP _ _ _ 'Js G 'N[x] M).
    rewrite -order_eq1 (pnat_1 _ t2M'y') // in nty'.
    by rewrite -defM (eq_pnat _ (tau2J _ _)) -eq_xy'.
  have Ns_y: y \in 'N[x]`_\sigma by rewrite eq_yx'; case/setIP: Rx'.
  apply: sub_p_elt (mem_p_elt (pcore_pgroup _ _) Ns_y) => p sNp.
  have [maxN _] := mem_uniq_mmax uniqNx.
  by apply: contraFN (sigma_partition _ _ notMGNx p) => // sMp; apply/andP.
rewrite negb_exists_in => /forall_inP not_sign_g.
apply: wlog_neg; rewrite negb_exists_in => /forall_inP not_kappa_g.
have s'g M: M \in 'M -> g \in M -> g.`_\sigma(M) = 1.
  move=> maxM; set x := g.`_\sigma(M); pose x' := g.`_(\sigma(M))^'.
  have def_x': x^-1 * g = x' by rewrite -(consttC \sigma(M) g) mulKg.
  apply: contraTeq => ntx.
  have ell1x: \ell_\sigma(x) == 1%N.
    rewrite /sigma_length (cardsD1 x.`_\sigma(M)).
    rewrite -sigma_decomposition_constt' // mem_sigma_decomposition //.
      by apply/ell_sigma0P; apply/constt1P; rewrite p_eltNK p_elt_constt.
    by rewrite sub_in_constt // => ?.
  apply: contra (not_sign_g _ ell1x) => Mg; rewrite def_x'.
  have [-> | ntx'] := eqVneq x' 1; first exact: group1.
  have cxx': x \in 'C[x'] by apply/cent1P; apply: commuteX2.
  have cMx_x': x' \in ('C_M[x])^# by rewrite 3!inE ntx' cent1C cxx' groupX.
  have Ms_x: x \in M`_\sigma.
    by rewrite (mem_Hall_pcore (Msigma_Hall maxM)) ?p_elt_constt ?groupX.
  have Ms1x: x \in (M`_\sigma)^# by apply/setD1P.
  have sM'x': (\sigma(M))^'.-elt x' := p_elt_constt _ _.
  have [[kMx' _] | [_ ell1x' uniqM]] := pi_of_cent_sigma maxM Ms1x cMx_x' sM'x'.
    case/existsP: (not_kappa_g _ ell1x); exists M; rewrite def_x' cMx_x' /=.
    by rewrite inE maxM cycle_subG Ms_x.
  have MSx'_gt1: #|'M_\sigma[x']| > 1.
    have [_ ntMSx'] := ell_sigma1P _ ell1x'.
    rewrite ltn_neqAle lt0n cards_eq0 ntMSx' andbT eq_sym.
    apply: contra ntx' => MSx'_eq1; rewrite -order_eq1 (pnat_1 _ sM'x') //.
    have [N MSx'N] := set0Pn _ ntMSx'; have [maxN Ns_x'] := setIdP MSx'N.
    rewrite -(eq_uniq_mmax uniqM maxN) ?cent1_sub_uniq_sigma_mmax //.
    exact: pgroupS Ns_x' (pcore_pgroup _ _).
  have defNx': 'N[x'] = M.
    by apply: set1_inj; case/FT_signalizer_context: ell1x' => _ [|<-].
  case/negP: (not_sign_g _ ell1x').
  by rewrite -(consttC \sigma(M)^' g) mulKg consttNK inE defNx' Ms_x.
have [x sg_x]: exists x, x \in sigma_decomposition g.
  by apply/set0Pn; rewrite -cards_eq0 (sameP (ell_sigma0P g) eqP).
have{sg_x} [ntx /imsetP[M maxM def_x]] := setD1P sg_x.
wlog MSxM: M maxM def_x / M \in 'M_\sigma[x].
  have sMx: \sigma(M).-elt x by rewrite def_x p_elt_constt.
  have [|[z Ms_xz] _] := sigma_Jsub maxM sMx; first by rewrite cycle_eq1.
  move/(_ (M :^ z^-1)%G)->; rewrite ?mmaxJ ?(eq_constt _ (sigmaJ M _)) //.
  by rewrite inE mmaxJ maxM MsigmaJ -sub_conjg.
have ell1x: \ell_\sigma(x) == 1%N.
  by apply/ell_sigma1P; split=> //; apply/set0Pn; exists M.
have notMg: g \notin M by apply: contra ntx; rewrite def_x; move/s'g->.
have cxg: g \in 'C[x] by rewrite cent1C def_x groupX ?cent1id.
have MSx_gt1: #|'M_\sigma[x]| > 1.
  rewrite ltnNge; apply: contra notMg => MSx_le1; apply: subsetP cxg.
  have [_ ntMSx] := ell_sigma1P _ ell1x.
  by rewrite cent1_sub_uniq_sigma_mmax // eqn_leq MSx_le1 lt0n cards_eq0.
have [_ [//|defNx _ _ _]] := FT_signalizer_context ell1x.
case/(_ M)=> // _ _ _ hallMN; have [maxN sCxN] := mem_uniq_mmax defNx.
have Ng: <[g]> \subset 'N[x] by rewrite cycle_subG (subsetP sCxN).
have sN'g: \sigma('N[x])^'.-elt g by apply/constt1P; rewrite s'g // -cycle_subG.
have [z _ MNgz] := Hall_subJ (mmax_sol maxN) hallMN Ng sN'g.
case/eqP: ntx; rewrite def_x -(eq_constt _ (sigmaJ M z)) s'g ?mmaxJ //.
by move: MNgz; rewrite conjIg cycle_subG => /setIP[].
Qed.

Section PTypeEmbedding.
Implicit Types Mi Mj : {group gT}.
Implicit Type Ks : {set gT}.

(* This is B & G, Theorem 14.7. *)
(* This theorem provides the basis for the maximal subgroup classification,   *)
(* the main output of the local analysis. Note that we handle differently the *)
(* two separate instances of non-structural proof (by analogy) that occur in  *)
(* the textbook, p. 112, l. 7 and p. 113, l. 22. For the latter we simply use *)
(* global induction on the size of the class support of the TI-set \hat{Z}    *)
(* (for this reason we have kept the assertion that this is greater than half *)
(* of the size of G, even though this is not used later in the proof; we did  *)
(* drop the more precise lower bound). For the former we prove a preliminary  *)
(* lemma that summarizes the four results of the beginning of the proof that  *)
(* used after p. 112, l. 7 -- note that this also gets rid of a third non     *)
(* structural argument (on p. 112, l. 5).                                     *)
(*   Also, note that the direct product decomposition of Z and the K_i, and   *)
(* its direct relation with the sigma-decomposition of elements of Z (p. 112, *)
(* l. 13-19) is NOT materially used in the rest of the argument, though it    *)
(* does obviously help a human reader forge a mental picture of the situation *)
(* at hand. Only the first remark, l. 13, is used to prove the alternative    *)
(* definition of T implicit in the remarks l. 22-23. Accordingly, we have     *)
(* suppressed most of these intermediate results: we have only kept the proof *)
(* that Z is the direct product of the K_i^*, though we discard this result   *)
(* immediately (its 24-line proof just nudges the whole proof size slightyly  *)
(* over the 600-line bar).                                                    *)
Theorem Ptype_embedding M K :
    M \in 'M_'P -> \kappa(M).-Hall(M) K ->
  exists2 Mstar, Mstar \in 'M_'P /\ gval Mstar \notin M :^: G
  & let Kstar := 'C_(M`_\sigma)(K) in
    let Z := K <*> Kstar in let Zhat := Z :\: (K :|: Kstar) in
  [/\ (*a*) {in 'E^1(K), forall X, 'M('C(X)) = [set Mstar]},
      (*b*) \kappa(Mstar).-Hall(Mstar) Kstar /\ \sigma(M).-Hall(Mstar) Kstar,
      (*c*) 'C_(Mstar`_\sigma)(Kstar) = K /\ \kappa(M) =i \tau1(M),
      (*d*) [/\ cyclic Z, M :&: Mstar = Z,
                {in K^#, forall x, 'C_M[x] = Z},
                {in Kstar^#, forall y, 'C_Mstar[y] = Z}
              & {in K^# & Kstar^#, forall x y, 'C[x * y] = Z}]
& [/\ (*e*) [/\ normedTI Zhat G Z, {in ~: M, forall g, [disjoint Zhat & M :^ g]}
              & (#|G|%:R / 2%:R < #|class_support Zhat G|%:R :> rat)%R ],
      (*f*) M \in 'M_'P2 /\ prime #|K| \/ Mstar \in 'M_'P2 /\ prime #|Kstar|,
      (*g*) {in 'M_'P, forall H, gval H \in M :^: G :|: Mstar :^: G}
    & (*h*) M^`(1) ><| K = M]].
Proof.
pose isKi Ks M K := [&& M \in 'M_'P, \kappa(M).-Hall(M) K & Ks \subset K].
move: M K; have Pmax_sym M K X (Ks := 'C_(M`_\sigma)(K)) (Z := K <*> Ks) Mi :
    M \in 'M_'P -> \kappa(M).-Hall(M) K -> X \in 'E^1(K) -> Mi \in 'M('N(X)) ->
 [/\ Z \subset Mi, gval Mi \notin M :^: G, exists Ki, isKi Ks Mi Ki
   & {in 'E^1(Ks), forall Xs, Z \subset 'N_Mi(gval Xs)}].
- move=> PmaxM hallK E1X maxNMi.
  have [[_ maxM] [maxMi sNXMi]] := (setIdP PmaxM, setIdP maxNMi).
  have [_ [defNK defNX] [ntKs uniqCKs] _ _] := Ptype_structure PmaxM hallK.
  rewrite -/Ks in defNK ntKs uniqCKs; have [_ mulKKs cKKs _] := dprodP defNK.
  have{mulKKs} defZ: 'N_M(K) = Z by rewrite -mulKKs -cent_joinEr.
  have sZMi: Z \subset Mi.
    by rewrite -defZ; have [<- _] := defNX X E1X; rewrite setIC subIset ?sNXMi.
  have [sKMi sKsMi] := joing_subP sZMi.
  have sXMis: X \subset Mi`_\sigma by have [_ ->] := defNX X E1X.
  have sMiX: \sigma(Mi).-group X := pgroupS sXMis (pcore_pgroup _ _).
  have [q EqX] := nElemP E1X; have [sXK abelX dimX] := pnElemP EqX.
  have piXq: q \in \pi(X) by rewrite -p_rank_gt0 p_rank_abelem ?dimX.
  have notMGMi: gval Mi \notin M :^: G.
    apply: contraL (pnatPpi sMiX piXq); case/imsetP=> a _ ->; rewrite sigmaJ.
    exact: kappa_sigma' (pnatPpi (pHall_pgroup hallK) (piSg sXK piXq)).
  have kMiKs: \kappa(Mi).-group Ks.
    apply/pgroupP=> p p_pr /Cauchy[] // xs Ks_xs oxs.
    pose Xs := <[xs]>%G; have sXsKs: Xs \subset Ks by rewrite cycle_subG.
    have EpXs: Xs \in 'E_p^1(Ks) by rewrite p1ElemE // !inE sXsKs -oxs /=.
    have sMi'Xs: \sigma(Mi)^'.-group Xs.
      rewrite /pgroup /= -orderE oxs pnatE //=.
      apply: contraFN (sigma_partition maxM maxMi notMGMi p) => /= sMi_p.
      rewrite inE /= sMi_p -pnatE // -oxs andbT.
      exact: pgroupS sXsKs (pgroupS (subsetIl _ _) (pcore_pgroup _ _)).
    have uniqM: 'M('C(Xs)) = [set M] by apply: uniqCKs; apply/nElemP; exists p.
    have [x Xx ntx] := trivgPn _ (nt_pnElem EqX isT).
    have Mis_x: x \in (Mi`_\sigma)^# by rewrite !inE ntx (subsetP sXMis).
    have CMix_xs: xs \in ('C_Mi[x])^#.
      rewrite 2!inE -order_gt1 oxs prime_gt1 // inE -!cycle_subG.
      rewrite (subset_trans sXsKs) //= sub_cent1 (subsetP _ x Xx) //.
      by rewrite centsC (centSS sXsKs sXK).
    have{sMi'Xs} [|[_ _]] := pi_of_cent_sigma maxMi Mis_x CMix_xs sMi'Xs.
      by case; rewrite /p_elt oxs pnatE.
    case/mem_uniq_mmax=> _ sCxsMi; case/negP: notMGMi.
    by rewrite -(eq_uniq_mmax uniqM maxMi) ?orbit_refl //= cent_cycle.
  have{kMiKs} [Ki hallKi sKsKi] := Hall_superset (mmax_sol maxMi) sKsMi kMiKs.
  have{ntKs} PmaxMi: Mi \in 'M_'P.
    rewrite !(maxMi, inE) andbT /= -partG_eq1 -(card_Hall hallKi) -trivg_card1.
    exact: subG1_contra sKsKi ntKs.
  have [_ [defNKi defNXs] _ _ _] := Ptype_structure PmaxMi hallKi.
  split=> //= [|Xs]; first by exists Ki; apply/and3P.
  rewrite -{1}[Ks](setIidPr sKsKi) nElemI -setIdE => /setIdP[E1Xs sXsKs].
  have{defNXs} [defNXs _] := defNXs _ E1Xs; rewrite join_subG /= {2}defNXs.
  by rewrite !subsetI sKMi sKsMi cents_norm ?normsG ?(centsS sXsKs) // centsC.
move=> M K PmaxM hallK /=; set Ks := 'C_(M`_\sigma)(K); set Z := K <*> Ks.
move: {2}_.+1 (ltnSn #|class_support (Z :\: (K :|: Ks)) G|) => nTG.
elim: nTG => // nTG IHn in M K PmaxM hallK Ks Z *; rewrite ltnS => leTGn.
have [maxM notFmaxM]: M \in 'M /\ M \notin 'M_'F := setDP PmaxM.
have{notFmaxM} ntK: K :!=: 1 by rewrite (trivg_kappa maxM).
have [_ [defNK defNX] [ntKs uniqCKs] _ _] := Ptype_structure PmaxM hallK.
rewrite -/Ks in defNK ntKs uniqCKs; have [_ mulKKs cKKs _] := dprodP defNK.
have{mulKKs} defZ: 'N_M(K) = Z by rewrite -mulKKs -cent_joinEr.
pose MNX := \bigcup_(X in 'E^1(K)) 'M('N(X)); pose MX := M |: MNX.
have notMG_MNX: {in MNX, forall Mi, gval Mi \notin M :^: G}.
  by move=> Mi /bigcupP[X E1X /(Pmax_sym M K)[]].
have MX0: M \in MX := setU11 M MNX.
have notMNX0: M \notin MNX by apply/negP=> /notMG_MNX; rewrite orbit_refl.
pose K_ Mi := odflt K [pick Ki | isKi Ks Mi Ki].
pose Ks_ Mi := 'C_(Mi`_\sigma)(K_ Mi).
have K0: K_ M = K.
  rewrite /K_; case: pickP => // K1 /and3P[_ /and3P[_ kK1 _] sKsK1].
  have sM_Ks: \sigma(M).-group Ks := pgroupS (subsetIl _ _) (pcore_pgroup _ _).
  rewrite -(setIid Ks) coprime_TIg ?eqxx ?(pnat_coprime sM_Ks) // in ntKs.
  exact: sub_pgroup (@kappa_sigma' M) (pgroupS sKsK1 kK1).
have Ks0: Ks_ M = Ks by rewrite /Ks_ K0.
have K_spec: {in MNX, forall Mi, isKi Ks Mi (K_ Mi)}.
  move=> Mi /bigcupP[X _ /(Pmax_sym M K)[] // _ _ [Ki Ki_ok] _].
  by rewrite /K_; case: pickP => // /(_ Ki)/idP.
have PmaxMX: {in MX, forall Mi, Mi \in 'M_'P /\ \kappa(Mi).-Hall(Mi)(K_ Mi)}.
  by move=> Mi /setU1P[-> | /K_spec/and3P[]//]; rewrite K0.
have ntKsX: {in MX, forall Mi, Ks_ Mi != 1}.
  by move=> Mi /PmaxMX[MX_Mi /Ptype_structure[] // _ _ []].
pose co_sHallK Mi Zi := 
  let sMi := \sigma(Mi) in sMi^'.-Hall(Zi) (K_ Mi) /\ sMi.-Hall(Zi) (Ks_ Mi).
have hallK_Zi: {in MX, forall Mi, co_sHallK Mi (K_ Mi \x Ks_ Mi)}.
  move=> Mi MXi; have [PmaxMi hallKi] := PmaxMX _ MXi.
  have [_ [defNKs _] _ _ _] := Ptype_structure PmaxMi hallKi.
  have [_ mulKKs _ _] := dprodP defNKs; rewrite defNKs.
  have sMi_Kis: _.-group (Ks_ Mi) := pgroupS (subsetIl _ _) (pcore_pgroup _ _).
  have sMi'Ki := sub_pgroup (@kappa_sigma' _) (pHall_pgroup hallKi).
  exact: coprime_mulGp_Hall mulKKs sMi'Ki sMi_Kis.
have{K_spec} defZX: {in MX, forall Mi, K_ Mi \x Ks_ Mi = Z}.
  move=> Mi MXi; have [-> | MNXi] := setU1P MXi; first by rewrite K0 Ks0 defNK.
  have /and3P[PmaxMi hallKi sKsKi] := K_spec _ MNXi.
  have [X E1X maxNMi] := bigcupP MNXi.
  have{defNX} [defNX /(_ Mi maxNMi) sXMis] := defNX X E1X.
  have /rank_geP[Xs E1Xs]: 0 < 'r(Ks) by rewrite rank_gt0.
  have [_ [defNi defNXi] _ _ _] := Ptype_structure PmaxMi hallKi.
  have [defNXs _] := defNXi _ (subsetP (nElemS 1 sKsKi) _ E1Xs).
  have [_ hallKis] := hallK_Zi _ MXi; rewrite defNi in hallKis.
  have sZNXs: Z \subset 'N_Mi(Xs) by case/(Pmax_sym M K): maxNMi => // _ _ _ ->.
  apply/eqP; rewrite eqEsubset andbC {1}defNi -defNXs sZNXs.
  have [_ _ cKiKis tiKiKis] := dprodP defNi; rewrite dprodEY // -defZ -defNX.
  have E1KiXs: Xs \in 'E^1(K_ Mi) := subsetP (nElemS 1 sKsKi) Xs E1Xs.
  have [|_ _ _ -> //] := Pmax_sym Mi _ Xs M PmaxMi hallKi E1KiXs.
    have [p EpXs] := nElemP E1Xs; have [_] := pnElemP EpXs; case/andP=> pXs _ _.
    rewrite inE maxM (sub_uniq_mmax (uniqCKs _ E1Xs)) ?cent_sub //=.
    exact: mFT_norm_proper (nt_pnElem EpXs isT) (mFT_pgroup_proper pXs).
  have [q /pnElemP[sXK abelX dimX]] := nElemP E1X.
  apply/nElemP; exists q; apply/pnElemP; split=> //.
  have nKisZi: Ks_ Mi <| 'N_Mi(K_ Mi) by case/dprod_normal2: defNi.
  rewrite (sub_normal_Hall hallKis) ?(pgroupS sXMis (pcore_pgroup _ _)) //=.
  by rewrite -defNXs (subset_trans sXK) // (subset_trans (joing_subl _ Ks)).
have{hallK_Zi} hallK_Z: {in MX, forall Mi, co_sHallK Mi Z}.
  by move=> Mi MXi; rewrite -(defZX _ MXi); apply: hallK_Zi.
have nsK_Z: {in MX, forall Mi, K_ Mi <| Z /\ Ks_ Mi <| Z}. 
  by move=> Mi /defZX; apply: dprod_normal2.
have tiKs: {in MX &, forall Mi Mj, gval Mi != gval Mj -> Ks_ Mi :&: Ks_ Mj = 1}.
  move=> Mi Mj MXi MXj; apply: contraNeq; rewrite -rank_gt0.
  case/rank_geP=> X E1X; move: E1X (E1X); rewrite /= {1}setIC {1}nElemI.
  case/setIP=> E1jX _; rewrite nElemI => /setIP[E1iX _].
  have [[maxKi hallKi] [maxKj hallKj]] := (PmaxMX _ MXi, PmaxMX _ MXj).
  have [_ _ [_ uniqMi] _ _] := Ptype_structure maxKi hallKi.
  have [_ _ [_ uniqMj] _ _] := Ptype_structure maxKj hallKj.
  by rewrite val_eqE -in_set1 -(uniqMj _ E1jX) (uniqMi _ E1iX) set11.
have sKsKX: {in MX &, forall Mi Mj, Mj != Mi -> Ks_ Mj \subset K_ Mi}.
  move=> Mi Mj MXi MXj /= neqMji; have [hallKi hallKsi] := hallK_Z _ MXi.
  have [[_ nsKsjZ] [nsKiZ _]] := (nsK_Z _ MXj, nsK_Z _ MXi).
  rewrite (sub_normal_Hall hallKi) ?(normal_sub nsKsjZ) // -partG_eq1.
  by rewrite -(card_Hall (Hall_setI_normal _ hallKsi)) //= setIC tiKs ?cards1.
have exMNX X: X \in 'E^1(K) -> exists2 Mi, Mi \in MNX & X \subset Mi`_\sigma.
  move=> E1X; have [p EpX] := nElemP E1X; have [_ abelX _] := pnElemP EpX.
  have ltXG: X \proper G := mFT_pgroup_proper (abelem_pgroup abelX).
  have [Mi maxNMi] := mmax_exists (mFT_norm_proper (nt_pnElem EpX isT) ltXG).
  have MNXi: Mi \in MNX by apply/bigcupP; exists X.
  by exists Mi => //; have [_ ->] := defNX X E1X.
have dprodKs_eqZ: \big[dprod/1]_(Mi in MX) Ks_ Mi = Z; last clear dprodKs_eqZ.
  have sYKs_KX Mi:
      Mi \in MX -> <<\bigcup_(Mj in MX | Mj != Mi) Ks_ Mj>> \subset K_ Mi.
  - move=> MXi; rewrite gen_subG.
    by apply/bigcupsP=> Mj /= /andP[]; apply: sKsKX.
  transitivity <<\bigcup_(Mi in MX) Ks_ Mi>>; apply/eqP.
    rewrite -bigprodGE; apply/bigdprodYP => Mi MXi; rewrite bigprodGE.
    apply: subset_trans (sYKs_KX _ MXi) _; apply/dprodYP.
    have [_ defZi cKiKs tiKiKs] := dprodP (defZX _ MXi).
    by rewrite dprodC joingC dprodEY.
  rewrite eqEsubset {1}(bigD1 M) //= Ks0 setUC -joingE -joing_idl.
  rewrite genS ?setSU ?big_setU1 //=; last by rewrite -K0 sYKs_KX.
  rewrite setUC -joingE -joing_idl Ks0 genS ?setSU // -(Sylow_gen K) gen_subG.
  apply/bigcupsP=> P; case/SylowP=> p p_pr /=; case/and3P=> sPK pP _.
  have [-> | ] := eqsVneq P 1; first exact: sub1G.
  rewrite -rank_gt0 (rank_pgroup pP); case/p_rank_geP=> X EpX.
  have EpKX: X \in 'E_p^1(K) := subsetP (pnElemS p 1 sPK) X EpX.
  have{EpKX} E1X: X \in 'E^1(K) by apply/nElemP; exists p.
  have [Mi MNXi sXMis] := exMNX X E1X; have MXi: Mi \in MX by rewrite setU1r.
  have [[_ nsKsi] [_ hallKsi]] := (nsK_Z _ MXi, hallK_Z _ MXi).
  have sPZ: P \subset Z := subset_trans sPK (joing_subl _ _).
  rewrite sub_gen ?(bigcup_max Mi) // (sub_normal_Hall hallKsi) //.
  rewrite (pi_pgroup pP) // (pnatPpi (pcore_pgroup _ _) (piSg sXMis _)) //.
  by have [_ ? dimX] := pnElemP EpX; rewrite -p_rank_gt0 p_rank_abelem ?dimX.
pose PZ := [set (Ks_ Mi)^# | Mi in MX]; pose T := Z^# :\: cover PZ.
have defT: \bigcup_(Mi in MX) (Ks_ Mi)^# * (K_ Mi)^# = T.
  apply/setP=> x; apply/bigcupP/setDP=> [[Mi MXi] | [Zx notZXx]].
    case/mulsgP=> y y' /setD1P[nty Ks_y] /setD1P[nty' Ky'] defx.
    have [_ defZi cKsKi tiKsKi] := dprodP (defZX _ MXi).
    rewrite 2!inE -[Z]defZi -(centC cKsKi) andbC {1}defx mem_mulg //=.
    have notKx: x \notin K_ Mi.
      by rewrite -in_set1 -set1gE -tiKsKi inE Ks_y andbT defx groupMr in nty *.
    split; first exact: group1_contra notKx.
    rewrite cover_imset; apply/bigcupP=> [[Mj MXj /setD1P[_ Ksj_x]]].
    rewrite (subsetP (sKsKX Mi Mj _ _ _)) // in notKx.
    apply: contraNneq nty' => eqMji; rewrite -in_set1 -set1gE -tiKsKi inE Ky'.
    by rewrite -(groupMl _ Ks_y) -defx -eqMji.
  have{Zx} [ntx Zx] := setD1P Zx.
  have [Mi MXi notKi_x]: exists2 Mi, Mi \in MX & x \notin K_ Mi.
    have [Kx | notKx] := boolP (x \in K); last by exists M; rewrite ?K0.
    pose p := pdiv #[x]; have xp: p \in \pi(#[x]) by rewrite pi_pdiv order_gt1.
    have /p_rank_geP[X EpX]: 0 < 'r_p(<[x]>) by rewrite p_rank_gt0.
    have [sXx abelX dimX] := pnElemP EpX.
    have piXp: p \in \pi(X) by rewrite -p_rank_gt0 p_rank_abelem ?dimX.
    have sXK: X \subset K by rewrite (subset_trans sXx) ?cycle_subG.
    have E1X: X \in 'E^1(K) by apply/nElemP; exists p; apply/pnElemP. 
    have [Mi MNXi sXMis] := exMNX X E1X; have MXi: Mi \in MX := setU1r M MNXi.
    have sXZ: X \subset Z := subset_trans sXK (joing_subl _ _).
    have sMip: p \in \sigma(Mi) := pnatPpi (pcore_pgroup _ _) (piSg sXMis piXp).
    have [hallKi _] := hallK_Z _ MXi.
    exists Mi => //; apply: contraL sMip => Ki_x.
    exact: pnatPpi (mem_p_elt (pHall_pgroup hallKi) Ki_x) xp.
  have [_ defZi cKisKi _] := dprodP (defZX _ MXi).
  rewrite -[Z]defZi -(centC cKisKi) in Zx.
  have [y y' Kis_y Ki_y' defx] := mulsgP Zx.
  have Kis1y: y \in (Ks_ Mi)^#.
    rewrite 2!inE Kis_y andbT; apply: contraNneq notKi_x => y1.
    by rewrite defx y1 mul1g.
  exists Mi; rewrite // defx mem_mulg // 2!inE Ki_y' andbT.
  apply: contraNneq notZXx => y'1; rewrite cover_imset.
  by apply/bigcupP; exists Mi; rewrite // defx y'1 mulg1.
have oT: #|T| = #|Z| + #|MNX| - (\sum_(Mi in MX) #|Ks_ Mi|).
  have tiTPZ Kis: Kis \in PZ -> [disjoint T & Kis].
    move=> Z_Kis; rewrite -setI_eq0 setIDAC setD_eq0.
    by rewrite (bigcup_max Kis) ?subsetIr.
  have notPZset0: set0 \notin PZ.
    apply/imsetP=> [[Mi MXi]]; apply/eqP; rewrite /= eq_sym setD_eq0 subG1.
    exact: ntKsX.
  have [| tiPZ injKs] := trivIimset _ notPZset0.
    move=> Mi Mj MXi MXj /= neqMji.
    by rewrite -setI_eq0 -setDIl setD_eq0 setIC tiKs.
  have{tiPZ} [tiPZ notPZ_T] := trivIsetU1 tiTPZ tiPZ notPZset0.
  rewrite (eq_bigr (fun Mi : {group gT} => 1 + #|(Ks_ Mi)^#|)%N); last first.
    by move=> Mi _; rewrite (cardsD1 1) group1.
  rewrite big_split sum1_card cardsU1 notMNX0 (cardsD1 1 Z) group1 /=.
  have ->: Z^# = cover (T |: PZ).
    rewrite -(setID Z^# (cover PZ)) setUC (setIidPr _) /cover ?big_setU1 //=.
    apply/bigcupsP=> _ /imsetP[Mi MXi ->]; apply: setSD.
    by case/nsK_Z: MXi => _ /andP[].
  by rewrite addnAC subnDl -(eqnP tiPZ) big_setU1 // big_imset //= addnK.
have tiTscov: {in 'M, forall H, [disjoint T & H^~~]}.
  move=> H maxH; apply/pred0P=> t; apply/andP=> [[/= Tt scovHt]].
  have ntt: t != 1 by have [/setD1P[]] := setDP Tt.
  have [x Hs_x xR_y] := bigcupP scovHt; have ell1x := Msigma_ell1 maxH Hs_x.
  have:= sigma_decomposition_dichotomy ntt.
  rewrite (introT existsP) /=; last by exists x; rewrite ell1x -mem_lcoset.
  rewrite -defT in Tt; have [Mi MXi Zi_t] := bigcupP Tt.
  case/mulsgP: Zi_t => y y' /setD1P[nty Ks_y] /setD1P[nty' Ky'] ->.
  case/existsP; exists y; rewrite mulKg.
  have [[Mis_y cKy] [PmaxMi hallKi]] := (setIP Ks_y, PmaxMX _ MXi).
  have [[maxMi _] [sKiMi kMiKi _]] := (setDP PmaxMi, and3P hallKi).
  rewrite (Msigma_ell1 maxMi) ?inE ?nty //=; apply/existsP; exists Mi.
  rewrite inE maxMi cycle_subG Mis_y 3!inE nty' (subsetP sKiMi) //=.
  by rewrite (subsetP _ _ Ky') ?sub_cent1 // (mem_p_elt kMiKi).
have nzT: T != set0.
  have [[y Ksy nty] [y' Ky' nty']] := (trivgPn _ ntKs, trivgPn _ ntK).
  apply/set0Pn; exists (y * y'); rewrite -defT; apply/bigcupP.
  by exists M; rewrite ?MX0 // K0 Ks0 mem_mulg 2?inE ?nty ?nty'.
have ntiT: normedTI T G Z.
  have sTZ: {subset T <= Z} by apply/subsetP; rewrite 2!subDset setUA subsetUr.
  have nTZ: Z \subset 'N(T).
    rewrite normsD ?norms_bigcup ?normD1 ?normG //.
    apply/bigcapsP=> _ /imsetP[Mi MXi ->]; rewrite normD1.
    by case/nsK_Z: MXi => _ /andP[].
  apply/normedTI_P; rewrite setTI /= -/Z.
  split=> // a _ /pred0Pn[t /andP[/= Tt]]; rewrite mem_conjg => Tta.
  have{Tta} [Zt Zta] := (sTZ t Tt, sTZ _ Tta).
  move: Tt; rewrite -defT => /bigcupP[Mi MXi].
  case/mulsgP=> y y' /setD1P[nty Kisy] /setD1P[nty' Kiy'] def_yy'.
  have [[hallKi hallKis] [nsKiZ _]] := (hallK_Z _ MXi, nsK_Z _ MXi).
  have [[PmaxMi hallKiMi] defZi] := (PmaxMX _ MXi, defZX _ MXi).
  have [_ [defNKi _] _ [[]]] := Ptype_structure PmaxMi hallKiMi.
  rewrite -defNKi defZi -/(Ks_ _) => tiKsi tiKi _ _ _.
  have [defy defy']: y = t.`_\sigma(Mi) /\ y' = t.`_\sigma(Mi)^'.
    have [_ cKiy] := setIP Kisy; have cy'y := centP cKiy _ Kiy'.
    have sMi_y := mem_p_elt (pHall_pgroup hallKis) Kisy.
    have sMi'y' := mem_p_elt (pHall_pgroup hallKi) Kiy'.
    rewrite def_yy' !consttM // constt_p_elt // 2?(constt1P _) ?p_eltNK //.
    by rewrite mulg1 mul1g constt_p_elt.
  have: a \in Mi.
    apply: contraR nty; rewrite -in_setC -in_set1 -set1gE; move/tiKsi <-.
    rewrite inE Kisy mem_conjg defy -consttJ groupX ?(subsetP _ _ Zta) //.
    by rewrite -defZi defNKi subsetIl.
  apply/implyP; apply: contraR nty'; rewrite negb_imply andbC -in_setD.
  rewrite -in_set1 -set1gE => /tiKi <-; rewrite inE Kiy' defy' mem_conjg.
  by rewrite -consttJ (mem_normal_Hall hallKi nsKiZ) ?p_elt_constt ?groupX.
have [_ tiT /eqP defNT] := and3P ntiT; rewrite setTI in defNT.
pose n : rat := #|MNX|%:R; pose g : rat := #|G|%:R.
pose z : rat := #|Z|%:R; have nz_z: z != 0%R := natrG_neq0 _ _.
pose k_ Mi : rat := #|K_ Mi|%:R.
have nz_ks: #|Ks_ _|%:R != 0%R :> rat := natrG_neq0 _ _.
pose TG := class_support T G.
have oTG: (#|TG|%:R = (1 + n / z - \sum_(Mi in MX) (k_ Mi)^-1) * g)%R.
  rewrite /TG class_supportEr -cover_imset -(eqnP tiT).
  rewrite (eq_bigr (fun _ => #|T|)) => [|_ /imsetP[x _ ->]]; last first.
    by rewrite cardJg.
  rewrite sum_nat_const card_conjugates setTI defNT.
  rewrite natrM natf_indexg ?subsetT //= -/z -mulrA mulrC; congr (_ * _)%R.
  rewrite oT natrB; last by rewrite ltnW // -subn_gt0 lt0n -oT cards_eq0.
  rewrite mulrC natrD -/n -/z natr_sum /=.
  rewrite mulrBl mulrDl big_distrl divff //=; congr (_ - _)%R. 
  apply: eq_bigr => Mi MXi; have defZi := defZX _ MXi.
  by rewrite /z -(dprod_card defZi) natrM invfM mulrC divfK.  
have neMNX: MNX != set0.
  move: ntK; rewrite -rank_gt0 => /rank_geP[X /exMNX[Mi MNXi _]].
  by apply/set0Pn; exists Mi.
have [Mi MXi P2maxMi]: exists2 Mi, Mi \in MX & Mi \in 'M_'P2.
  apply/exists_inP; apply: negbNE; rewrite negb_exists_in.
  apply/forall_inP=> allP1; pose ssup Mi := class_support (gval Mi)^~~ G.
  have{allP1} min_ssupMX Mi:
    Mi \in MX -> (#|ssup Mi|%:R >= ((k_ Mi)^-1 - (z *+ 2)^-1) * g)%R.
  - move=> MXi; have [PmaxMi hallKi] := PmaxMX _ MXi.
    have [[U [complU defMi] _]] := Ptype_structure PmaxMi hallKi.
    case=> defZi _ _ _ _; have [maxMi _] := setDP PmaxMi.
    have{complU} U1: U :==: 1; last rewrite {U U1}(eqP U1) sdprod1g in defMi.
      rewrite (trivg_kappa_compl maxMi complU).
      by apply: contraR (allP1 _ MXi) => ?; apply/setDP.
    rewrite card_class_support_sigma // natrM natf_indexg ?subsetT // -/g.
    rewrite mulrCA mulrC ler_wpmul2r ?ler0n // -subn1 natrB ?cardG_gt0 //.
    rewrite mulr1n mulrBl -{1}(sdprod_card defMi) natrM invfM.
    rewrite mulVKf ?natrG_neq0 // ler_add2l ler_opp2 -(mulr_natr _ 2) invfM.
    rewrite ler_pdivr_mulr ?natrG_gt0 // mulrC mulrA.
    have sZM: Z \subset M by rewrite -defZ subsetIl.
    have sZMi: Z \subset Mi by rewrite -(defZX _ MXi) defZi subsetIl.
    rewrite -natf_indexg //= -/Z ler_pdivl_mulr ?(ltr0Sn _ 1) // mul1r ler_nat.
    rewrite indexg_gt1 /= -/Z subEproper /proper sZMi andbF orbF.
    apply: contraNneq notMNX0 => defMiZ; have [Mj MNXj] := set0Pn _ neMNX.
    have maxZ: [group of Z] \in 'M by rewrite !inE defMiZ in maxMi *.
    have eqZ := group_inj (eq_mmax maxZ _ _); rewrite -(eqZ M) //.
    have [Xj E1Xj maxNMj] := bigcupP MNXj; have [maxMj _] := setIdP maxNMj.
    by rewrite (eqZ Mj) //; case/(Pmax_sym M K): maxNMj.
  pose MXsup := [set ssup Mi | Mi in MX].
  have notMXsup0: set0 \notin MXsup.
    apply/imsetP=> [[Mi /PmaxMX[/setDP[maxMi _] _] /esym/eqP/set0Pn[]]].
    have [x Mis_x ntx] := trivgPn _ (Msigma_neq1 maxMi).
    exists (x ^ 1); apply: mem_imset2; rewrite ?inE //.
    by apply/bigcupP; exists x; rewrite ?inE ?ntx // lcoset_refl.
  have [Mi Mj MXi MXj /= neqMij | tiMXsup inj_ssup] := trivIimset _ notMXsup0.
    apply/pred0Pn=> [[_ /andP[/imset2P[x y1 signMi_x _ ->]]]] /=.
    rewrite /ssup class_supportEr /= => /bigcupP[y2 _].
    rewrite -mem_conjgV -conjsgM -sigma_supportJ; set H := Mj :^ _ => Hx.
    suffices: [disjoint Mi^~~ & H^~~].
      by case/pred0Pn; exists x; rewrite /= {1}signMi_x Hx.
    have [[PmaxMi _] [PmaxMj _]] := (PmaxMX _ MXi, PmaxMX _ MXj).
    have [[maxMi _] [maxMj _]] := (setDP PmaxMi, setDP PmaxMj).
    apply: sigma_support_disjoint; rewrite ?mmaxJ //.
    rewrite (orbit_transr _ (mem_orbit _ _ _)) ?inE //=.
    apply: contra (ntKsX _ MXi); case/imsetP=> y _ /= defMj; rewrite -/(Ks_ _).
    have sKisKj: Ks_ Mi \subset K_ Mj by rewrite sKsKX // eq_sym.
    rewrite -(setIidPl sKisKj) coprime_TIg //.
    have [[_ hallKis] [hallKj _]] := (hallK_Z _ MXi, hallK_Z _ MXj).
    apply: pnat_coprime (pHall_pgroup hallKj).
    by rewrite defMj -pgroupE (eq_pgroup _ (sigmaJ _ _)) (pHall_pgroup hallKis).
  have [|tiPG notMXsupTG]: _ /\ TG \notin _ := trivIsetU1 _ tiMXsup notMXsup0.
    move=> _ /imsetP[Mi /PmaxMX[/setDP[maxMi _] _] ->].
    apply/pred0Pn=> [[_ /andP[/imset2P[x y1 Tx _ ->]]]] /=.
    rewrite /ssup class_supportEr => /bigcupP[y2 _].
    rewrite -mem_conjgV -conjsgM -sigma_supportJ; set H := Mi :^ _ => Hx.
    have maxH: [group of H] \in 'M by rewrite mmaxJ.
    by case/andP: (pred0P (tiTscov _ maxH) x).
  suffices: (g <= #|cover (TG |: MXsup)|%:R)%R.
    rewrite ler_nat (cardsD1 1 G) group1 ltnNge subset_leq_card //.
    apply/bigcupsP=> _ /setU1P[|/imsetP[Mi /PmaxMX[/setDP[maxMi _] _]]] ->.
      rewrite /TG class_supportEr; apply/bigcupsP=> x _.
      rewrite sub_conjg (normP _) ?normD1 ?(subsetP (normG _)) ?inE //.
      by rewrite subDset setUC subsetU // setSD ?subsetT.
    rewrite /ssup class_supportEr; apply/bigcupsP=> x _.
    rewrite subsetD1 subsetT mem_conjg conj1g {x}/=.
    move/ell_sigma0P: (@erefl gT 1); rewrite cards_eq0.
    apply: contraL => /bigcupP[x Mis_x xR1]; apply/set0Pn; exists x.
    exact: mem_sigma_cover_decomposition (Msigma_ell1 maxMi Mis_x) xR1.
  rewrite -(eqnP tiPG) big_setU1 ?big_imset //= natrD natr_sum.
  suffices: (g <= #|TG|%:R + \sum_(i in MX) ((k_ i)^-1 - (z *+ 2)^-1) * g)%R.
    by move/ler_trans->; rewrite // ler_add2l ler_sum.
  rewrite -big_distrl /= oTG -/g -mulrDl big_split /= sumr_const.
  rewrite addrA subrK -(mulr_natl _ 2) -[_ *+ _]mulr_natl invfM mulrN.
  rewrite mulrA -addrA -mulrBl -{1}(mul1r g) ler_wpmul2r ?ler0n //.
  rewrite ler_addl -(mul0r z^-1)%R ler_wpmul2r ?invr_ge0 ?ler0n //.
  rewrite subr_ge0 ler_pdivr_mulr ?(ltr0Sn _ 1) // -natrM ler_nat.
  by rewrite muln2 -addnn cardsU1 leq_add2r notMNX0 lt0n cards_eq0.
have [prKi nilMis]: prime #|K_ Mi| /\ nilpotent Mi`_\sigma.
  by have [PmaxMi /Ptype_structure[] // _ _ _ _ []] := PmaxMX _ MXi.
have [Mj MXj neqMji]: exists2 Mj, Mj \in MX & Mj :!=: Mi.
  have [Mj |] := pickP (mem ((MX) :\ Mi)); first by case/setD1P; exists Mj.
  move/eq_card0/eqP; rewrite -(eqn_add2l true) -{1}MXi -cardsD1 cardsU1.
  by rewrite notMNX0 eqSS cards_eq0 (negPf neMNX).
have defKjs: Ks_ Mj = K_ Mi.
  have sKjsKi: Ks_ Mj \subset K_ Mi by rewrite sKsKX.
  apply/eqP; rewrite eqEcard sKjsKi (prime_nt_dvdP _ _ (cardSg sKjsKi)) //=.
  by rewrite -trivg_card1 ntKsX.
have defMXij: MX = [set Mi; Mj].
  symmetry; rewrite -(setD1K MXi); congr (_ |: _); apply/eqP.
  rewrite eqEcard sub1set cards1 (cardsD1 Mj) 2!inE neqMji MXj /= ltnS leqn0.
  apply/pred0Pn=> [[Mk /setD1P[neMkj /setD1P[neMki MXk]]]].
  have sKskKsj: Ks_ Mk \subset Ks_ Mj by rewrite defKjs sKsKX.
  by case/negP: (ntKsX _ MXk); rewrite -(setIidPl sKskKsj) tiKs.
have defKsi: Ks_ Mi = K_ Mj.
  apply/eqP; rewrite eqEcard sKsKX 1?eq_sym //=.
  rewrite -(@leq_pmul2r #|Ks_ Mj|) ?cardG_gt0 // (dprod_card (defZX _ MXj)).
  by rewrite defKjs mulnC (dprod_card (defZX _ MXi)).
have{nilMis} cycZ: cyclic Z.
  have cycKi := prime_cyclic prKi.
  apply: nil_Zgroup_cyclic.
    apply/forall_inP=> S /SylowP[p _ /and3P[sSZ pS _]].
    have [[hallKi hallKis] [nsKi nsKis]] := (hallK_Z _ MXi, nsK_Z _ MXi).
    have [sMi_p | sMi'p] := boolP (p \in \sigma(Mi)); last first.
      by rewrite (cyclicS _ cycKi) // (sub_normal_Hall hallKi) ?(pi_pgroup pS).
    have sSKj: S \subset K_ Mj.
      by rewrite -defKsi (sub_normal_Hall hallKis) ?(pi_pgroup pS).
    rewrite (odd_pgroup_rank1_cyclic pS) ?mFT_odd //.
    apply: wlog_neg; rewrite -ltnNge ltn_neqAle p_rank_gt0 => /andP[_ piSp].
    have [_ /and3P[sKjMj kKj _]] := PmaxMX _ MXj.
    rewrite -(rank_kappa (pnatPpi kKj (piSg sSKj piSp))) p_rankS //.
    exact: subset_trans sSKj sKjMj.  
  rewrite (dprod_nil (defZX _ MXi)) abelian_nil ?cyclic_abelian //=.
  exact: (nilpotentS (subsetIl _ _)) nilMis.
have cycK: cyclic K := cyclicS (joing_subl _ _) cycZ.
have defM: M^`(1) ><| K = M.
  have [U complU] := ex_kappa_compl maxM hallK; have [hallU _ _] := complU.
  have [_ defM _ regUK _] := kappa_compl_context maxM complU.
  have{hallU} [[sUM _] [sKM kK _]] := (andP hallU, and3P hallK).
  case/sdprodP: defM => [[_ E _ defE]]; rewrite defE.
  case/sdprodP: defE => _ <-{E} nUK _ defM /mulGsubP[nMsU nMsK] tiMsUK.
  pose MsU := M`_\sigma <*> U; have nMsUK: K \subset 'N(MsU) by rewrite normsY.
  have defMl: MsU * K = M by rewrite [MsU]norm_joinEr // -mulgA.
  have coUK := regular_norm_coprime nUK regUK.
  have ->: M^`(1) = MsU.
    apply/eqP; rewrite eqEsubset; apply/andP; split; last first.
      have solU := solvableS sUM (mmax_sol maxM).
      rewrite join_subG Msigma_der1 //= -(coprime_cent_prod nUK coUK solU).
      by rewrite (cent_semiregular regUK) // mulg1 commgSS.
    apply: der1_min; first by rewrite -{1}defMl mulG_subG normG.
    by rewrite -{2}defMl quotientMidl quotient_abelian ?cyclic_abelian.
  rewrite sdprodE ?coprime_TIg //= norm_joinEr //.
  rewrite (coprime_dvdl (dvdn_cardMg _ _)) // coprime_mull coUK.
  rewrite (pnat_coprime (pcore_pgroup _ _) (sub_pgroup _ kK)) //.
  exact: kappa_sigma'.
have{neMNX} [Mstar MNX'star] := set0Pn _ neMNX.
have defMNX: MNX = [set Mstar].
  apply/eqP; rewrite eq_sym eqEcard sub1set MNX'star /= -(leq_add2l true).
  by rewrite -{1}notMNX0 -cardsU1 -/MX defMXij setUC cards2 neqMji !cards1.
have MXstar: Mstar \in MX by rewrite setU1r.
have [[PmaxMstar hallKstar] defZstar] := (PmaxMX _ MXstar, defZX _ MXstar).
have [maxMstar _] := setDP PmaxMstar.
have notMGMstar := notMG_MNX _ MNX'star; exists Mstar => //.
have [defKs defKs_star]: Ks = K_ Mstar /\ Ks_ Mstar = K.
  rewrite /Ks /Ks_ -K0; rewrite /MX defMNX 3!inE val_eqE in neqMji MXj MXi.
  by case/set2P: MXi (negPf neqMji) MXj => <- ->; rewrite ?orbF /= => /eqP <-.
have hallKs: \sigma(M).-Hall(Mstar) Ks.
  have sKsMstar: Ks \subset Mstar by rewrite defKs (pHall_sub hallKstar).
  have sM_Ks: \sigma(M).-group Ks := pgroupS (subsetIl _ _) (pcore_pgroup _ _).
  have [Y hallY sKsY] := Hall_superset (mmax_sol maxMstar) sKsMstar sM_Ks.
  have [sYMstar sM_Y _] := and3P hallY; apply: etrans hallY; congr pHall.
  have sYMs: Y \subset M`_\sigma.
    case/Ptype_structure: hallK => // _ _ _ [_ _ -> //].
    by rewrite (setIidPr sKsY).
  apply/eqP; rewrite eqEsubset sKsY subsetI sYMs (sameP commG1P trivgP) /=.
  have <-: M`_\sigma :&: Mstar`_\sigma = 1.
    rewrite coprime_TIg // (pnat_coprime (pcore_pgroup _ _)) //.
    apply: sub_pgroup (pcore_pgroup _ _) => q sM1q.
    apply: contraFN (sigma_partition maxM maxMstar notMGMstar q) => sMq.
    exact/andP.
  rewrite commg_subI //.
    by rewrite subsetI sYMs (subset_trans sYMstar) ?gFnorm.
  rewrite subsetI -{1}defKs_star subsetIl.
  by rewrite (subset_trans (pHall_sub hallK)) ?gFnorm.
have oTGgt_g2: (g / 2%:R < #|TG|%:R)%R.
  rewrite oTG big_setU1 //= /n defMNX big_set1 cards1 mulrC mul1r.
  rewrite ltr_pmul2r ?(ltr_nat _ 0) ?cardG_gt0 //  /k_ K0 -defKs.
  rewrite /z -defZ -(dprod_card defNK) natrM invfM opprD.
  pose hm u : rat := (1 - u%:R^-1)%R; set lhs := (_^-1)%R.
  suffices: (lhs < hm #|K| * hm #|Ks|)%R.
    by rewrite mulrBl !mulrBr !mul1r mulr1 opprB addrAC !addrA.
  have hm_inc u v: 0 < u <= v -> (hm u <= hm v)%R.
    case/andP=> u_gt0 le_uv; rewrite ler_add2l ler_opp2.
    have v_gt0 := leq_trans u_gt0 le_uv.
    rewrite -(mul1r _^-1)%R ler_pdivr_mulr ?ltr0n //.
    by rewrite ler_pdivl_mull ?ltr0n // mulr1 ler_nat.
  have le_pdiv H: 0 < pdiv #|H| <= #|H| by rewrite pdiv_gt0 dvdn_leq ?pdiv_dvd.
  have{le_pdiv} hm_pdiv := hm_inc _ _ (le_pdiv _).
  have hm_ge0 u: (0 <= hm u)%R.
    by case: u => // u; rewrite subr_ge0 invf_le1 ?ltr0Sn ?(ler_nat _ 1).
  do 2![rewrite mulrC (ltr_le_trans _ (ler_wpmul2r (hm_ge0 _) (hm_pdiv _))) //].
  set p := pdiv #|K|; set q := pdiv #|Ks|.
  have [odd_p odd_q]: odd p /\ odd q.
    by split; apply: dvdn_odd (pdiv_dvd _) (mFT_odd _).
  without loss [lt1p ltpq]: p q odd_p odd_q / 1 < p /\ p < q.
    have [p_pr q_pr]: prime p /\ prime q by rewrite !pdiv_prime ?cardG_gt1.
    have [ltpq | ltqp | eqpq] := ltngtP p q.
    - by apply; rewrite ?prime_gt1. 
    - by rewrite mulrC; apply; rewrite ?prime_gt1.
    have [] := hallK_Z _ MX0.
    rewrite K0 Ks0 => /and3P[_ sM'K _] /and3P[_ sMKs _].
    case/negP: (pgroupP sM'K _ p_pr (pdiv_dvd _)); rewrite eqpq.
    exact: pgroupP sMKs _ q_pr (pdiv_dvd _).
  have p_gt2: 2 < p by rewrite odd_geq.
  apply: ltr_le_trans (isT : lhs < hm 3 * hm 5)%R _.
  by rewrite ler_pmul ?hm_inc ?hm_ge0 //= odd_geq ?(leq_trans _ ltpq).
have defZhat: Z :\: (K :|: Ks) = T.
  rewrite /T cover_imset big_setU1 //= defMNX big_set1 defKs_star Ks0.
  by rewrite -setDUl setDDl setUC setD1K // inE group1.
rewrite defZhat {1}defKs; split; first 2 [by split].
- by rewrite -defKs_star; case/Ptype_structure: hallKstar => // _ _ [].
- split=> [|p]; first by rewrite -defKs_star defKs.
  apply/idP/idP=> [kMp | t1p].
    have /orP[// | /and3P[_ _ p_dv_M']] := kappa_tau13 kMp.
    have hallM': \kappa(M)^'.-Hall(M) M^`(1).
      exact/(sdprod_normal_pHallP (der_normal 1 M) hallK).
    have piMp: p \in \pi(M) by rewrite kappa_pi.
    case/idPn: kMp; apply: (pnatPpi (pHall_pgroup hallM')).
    by move: piMp; rewrite !mem_primes !cardG_gt0 /= => /andP[->].
  apply: (pnatPpi (pHall_pgroup hallK)); have [_ _ not_p_dv_M'] := and3P t1p.
  have: p \in \pi(M) by rewrite (partition_pi_mmax maxM) t1p ?orbT.
  rewrite !mem_primes !cardG_gt0 /= => /andP[p_pr].
  by rewrite p_pr -(sdprod_card defM) Euclid_dvdM // (negPf not_p_dv_M').
- split=> // [| x | y | x y K1_x Ks1_y].
  + have defMsMstar: M`_\sigma :&: Mstar = Ks.
      apply: sub_pHall hallKs _ _ (subsetIr _ _).
        exact: pgroupS (subsetIl _ _) (pcore_pgroup _ _).
      by rewrite subsetI subsetIl /= -/Ks defKs (pHall_sub hallKstar).
    have nKsMMstar: M :&: Mstar \subset 'N(Ks).
      by rewrite -defMsMstar normsIG ?gFnorm.
    have [_ [defNKs _] _ _ _] := Ptype_structure PmaxMstar hallKstar.
    rewrite -(setIidPl nKsMMstar) -setIA defKs -defNKs defZstar.
    by rewrite -defZ setIA setIid.
  + case/setD1P; rewrite -cycle_eq1 -cycle_subG -cent_cycle => ntx sxK.
    apply/eqP; rewrite eqEsubset andbC subsetI -{1}defZ subsetIl.
    rewrite sub_abelian_cent ?cyclic_abelian //=; last first.
      by rewrite (subset_trans sxK) ?joing_subl.
    move: ntx; rewrite -rank_gt0 /= -{1}(setIidPr sxK) => /rank_geP[X].
    rewrite nElemI -setIdE -defZ => /setIdP[E1X sXx]. 
    by have [<- _] := defNX _ E1X; rewrite setIS ?cents_norm ?centS.
  + case/setD1P; rewrite -cycle_eq1 -cycle_subG -cent_cycle => nty syKs.
    have [_ [defNKs defNY] _ _ _] := Ptype_structure PmaxMstar hallKstar.
    rewrite defZstar -defKs in defNKs defNY.
    apply/eqP; rewrite eqEsubset andbC subsetI {1}defNKs subsetIl.
    rewrite sub_abelian_cent ?cyclic_abelian //=; last first.
      by rewrite (subset_trans syKs) ?joing_subr.
    move: nty; rewrite -rank_gt0 /= -{1}(setIidPr syKs) => /rank_geP[Y].
    rewrite nElemI -setIdE defNKs => /setIdP[E1Y sYy].
    by have [<- _] := defNY _ E1Y; rewrite setIS ?cents_norm ?centS.
  have [[_ K_x] [_ Ks_y]] := (setD1P K1_x, setD1P Ks1_y).
  apply/eqP; rewrite eqEsubset sub_cent1 -(centsP cKKs) //.
  have Tyx: y * x \in T by rewrite -defT big_setU1 //= inE Ks0 K0 mem_mulg.
  rewrite (subset_trans _ (cent1_normedTI ntiT Tyx)) ?setTI //.
  rewrite (subsetP _ _ Tyx) // -defZhat setDE subIset //.
  by rewrite -abelianE cyclic_abelian.
split=> // [||H PmaxH].
- split=> // a notMa.
  have{tiKs} [_ _ _ [[tiKs _] _ _] _] := Ptype_structure PmaxM hallK.
  rewrite -defT big_setU1 //= defMNX big_set1 -defKs defKs_star Ks0 K0.
  rewrite centC ?(centSS _ _ cKKs) ?subsetDl // setUid.
  apply/pred0Pn=> [[_ /andP[/mulsgP[x y K1_x Ks1_y ->] /= Ma_xy]]].
  have [[_ K_x] [nty Ks_y]] := (setD1P K1_x, setD1P Ks1_y); case/negP: nty.
  rewrite -in_set1 -set1gE -(tiKs a notMa) inE Ks_y.
  suffices ->: y = (x * y).`_\sigma(M) by rewrite groupX.
  rewrite consttM; last by red; rewrite -(centsP cKKs).
  have sM'K := sub_pgroup (@kappa_sigma' M) (pHall_pgroup hallK).
  rewrite (constt1P (mem_p_elt sM'K K_x)) mul1g constt_p_elt //.
  exact: mem_p_elt (pHall_pgroup hallKs) Ks_y.
- have:= set21 Mi Mj; rewrite -defMXij /MX defMNX defKs -K0.
  by case/set2P=> <-; [left | right].
have [maxH _] := setDP PmaxH.
have{maxH}[L hallL] := Hall_exists \kappa(H) (mmax_sol maxH).
pose Ls := 'C_(H`_\sigma)(L); pose S := (L <*> Ls) :\: (L :|: Ls).
have{IHn} oSGgt_g2: (g / 2%:R < #|class_support S G|%:R)%R.
  have [|nTG_leS] := ltnP #|class_support S G| nTG.
    by case/IHn=> // Sstar _ [_ _ _ _ [[_ _ -> //]]].
  apply: ltr_le_trans oTGgt_g2 _; rewrite ler_nat /TG -defZhat.
  exact: leq_trans leTGn nTG_leS.
have{oSGgt_g2 oTGgt_g2} meetST: ~~ [disjoint TG & class_support S G].
  rewrite -leq_card_setU; apply: contraTneq (leqnn #|G|) => tiTGS.
  rewrite -ltnNge -(ltr_nat [realFieldType of rat]) -/g.
  rewrite -{1}[g](@divfK _ 2%:R) // mulr_natr.
  apply: ltr_le_trans (ltr_add oTGgt_g2 oSGgt_g2) _.
  by rewrite -natrD -tiTGS ler_nat cardsT max_card.
have{meetST} [x Tx [a Sx]]: exists2 x, x \in T & exists a, x \in S :^ a.
  have [_ /andP[/imset2P[x a1 Tx _ ->]]] := pred0Pn meetST.
  rewrite class_supportEr => /bigcupP[a2 _ Sa2_xa1].
  by exists x => //; exists (a2 * a1^-1); rewrite conjsgM mem_conjgV.
rewrite {}/S {}/Ls in Sx; without loss a1: a H L PmaxH hallL Sx / a = 1.
  move/(_ 1 (H :^ a)%G (L :^ a)%G); rewrite conjsg1 PtypeJ PmaxH pHallJ2.
  rewrite (eq_pHall _ _ (kappaJ H a)) hallL MsigmaJ centJ.
  rewrite -conjIg -conjYg -conjUg -conjDg Sx !inE.
  by rewrite !(orbit_transr _ (mem_orbit _ _ _)) ?inE //; exact.
have [_ [defNL _] [_ uniqH] _ _] := Ptype_structure PmaxH hallL.
do [rewrite {a}a1 conjsg1; set Ls := 'C_(_)(L)] in Sx defNL.
have{x Sx Tx} [Mk MXk ntLsMks]: exists2 Mk, Mk \in MX & Ls :&: Ks_ Mk != 1.
  have [_ _ cLLs tiLLs] := dprodP defNL.
  pose W := L <*> Ls; pose y := x.`_\sigma(H); pose ys := y.`_\sigma(Mi).
  have Zy: y \in Z by apply: groupX; case/setDP: Tx; case/setD1P=> _ ->.
  have{hallL} [hallL hallLs]: \sigma(H)^'.-Hall(W) L /\ \sigma(H).-Hall(W) Ls.
    apply: coprime_mulGp_Hall; first by rewrite /= cent_joinEr.
      exact: sub_pgroup (@kappa_sigma' H) (pHall_pgroup hallL).
    exact: pgroupS (subsetIl _ _) (pcore_pgroup _ _).
  have [nsLW nsLsW]: L <| W /\ Ls <| W := cprod_normal2 (cprodEY cLLs).
  have{Sx} [Ls_y nty]: y \in Ls /\ y != 1.
    move: Sx; rewrite 2!inE negb_or -andbA -/W; case/and3P=> notLx _ Wx.
    split; first by rewrite (mem_normal_Hall hallLs) ?p_elt_constt ?groupX.
    by rewrite (sameP eqP constt1P) -(mem_normal_Hall hallL).
  have [[hallKi hallKis] [nsKi nsKis]] := (hallK_Z _ MXi, nsK_Z _ MXi).
  have [/constt1P sM'y | ntys] := altP (ys =P 1).
    exists Mj; rewrite // defKjs.
    by apply/trivgPn; exists y; rewrite // inE Ls_y (mem_normal_Hall hallKi).
  exists Mi => //; apply/trivgPn; exists ys; rewrite // inE groupX //=.
  by rewrite (mem_normal_Hall hallKis) ?p_elt_constt // groupX.
suffices ->: H = Mk.
  by move: MXk; rewrite /MX defMNX => /set2P[]->; rewrite inE orbit_refl ?orbT.
move: ntLsMks; rewrite -rank_gt0 => /rank_geP[Y E1Y].
have:= E1Y; rewrite nElemI => /setIP[E1LsY _].
apply: set1_inj; rewrite -(uniqH _ E1LsY).
have [PmaxMk hallKk] := PmaxMX _ MXk.
have [_ _ [_ -> //]] := Ptype_structure PmaxMk hallKk.
by rewrite /= setIC nElemI in E1Y; case/setIP: E1Y.
Qed.

End PTypeEmbedding.

(* This is the first part of B & G, Corollary 14.8. *)
Corollary P1type_trans : {in 'M_'P1 &, forall M H, gval H \in M :^: G}.
Proof.
move=> M H P1maxM P1maxH; have [PmaxM _] := setIdP P1maxM.
have [[maxM _] [PmaxH _]] := (setDP PmaxM, setIdP P1maxH).
have [K hallK] := Hall_exists \kappa(M) (mmax_sol maxM).
have [Mstar _ [_ _ _ _ [_ [|]]]] := Ptype_embedding PmaxM hallK.
  by case; rewrite inE P1maxM.
case=> /setDP[_ /negP notP1maxMstar] _.
case/(_ H PmaxH)/setUP=> // /imsetP[a _ /group_inj defH].
by rewrite defH P1typeJ in P1maxH.
Qed.

(* This is the second part of B & G, Corollary 14.8. *)
Corollary Ptype_trans : {in 'M_'P, forall M,
  exists2 Mstar, Mstar \in 'M_'P /\ gval Mstar \notin M :^: G
  & {in 'M_'P, forall H, gval H \in M :^: G :|: Mstar :^: G}}.
Proof.
move=> M PmaxM; have [maxM _] := setDP PmaxM.
have [K hallK] := Hall_exists \kappa(M) (mmax_sol maxM).
have [Mstar PmaxMstar [_ _ _ _ [_ _ inMMs _]]] := Ptype_embedding PmaxM hallK.
by exists Mstar.
Qed.

(* This is B & G, Corollary 14.9. *)
Corollary mFT_partition :
  let Pcover := [set class_support M^~~ G | M : {group gT} in 'M] in
  [/\ (*1*) 'M_'P == set0 :> {set {group gT}} -> partition Pcover G^#
    & (*2*) forall M K, M \in 'M_'P -> \kappa(M).-Hall(M) K ->
            let Ks := 'C_(M `_\sigma)(K) in let Z := K <*> Ks in
            let Zhat := Z :\: (K :|: Ks) in
            let ClZhat := class_support Zhat G in
            partition (ClZhat |: Pcover) G^# /\ ClZhat \notin Pcover].
Proof.
move=> Pcover; have notPcover0: set0 \notin Pcover.
  apply/imsetP=> [[M maxM]]; apply/eqP; rewrite eq_sym; apply/set0Pn.
  have [x Ms_x ntx] := trivgPn _ (Msigma_neq1 maxM); exists x.
  rewrite class_supportEl; apply/bigcupP; exists x; last exact: class_refl.
  by apply/bigcupP; exists x; [apply/setD1P | apply: lcoset_refl].
have tiPcover: trivIset Pcover.
  apply/trivIsetP=> _ _ /imsetP[M maxM ->] /imsetP[H maxH ->] notMGH.
  rewrite -setI_eq0 !{1}class_supportEr big_distrr big1 //= => a Ga.
  rewrite big_distrl big1 //= => b Gb; apply/eqP.
  rewrite -!{1}sigma_supportJ setI_eq0 sigma_support_disjoint ?mmaxJ //.
  apply: contra notMGH; rewrite {a Ga}(orbit_transr _ (mem_orbit _ _ Ga)).
  rewrite {b Gb}(orbit_transl (mem_orbit _ _ Gb))=> /imsetP[c Gc ->] /=.
  by rewrite sigma_supportJ class_supportGidl.
have ntPcover: cover Pcover \subset G^#.
  apply/bigcupsP=> _ /imsetP[M maxM ->]; rewrite class_supportEr.
  apply/bigcupsP=> a _; rewrite subsetD1 subsetT mem_conjg conj1g {a}//=.
  move/ell_sigma0P: (@erefl gT 1); rewrite cards_eq0; apply: contraL.
  case/bigcupP=> x Ms_x xR1; apply/set0Pn; exists x.
  exact: mem_sigma_cover_decomposition (Msigma_ell1 maxM Ms_x) xR1.
split=> [MP0 | M K PmaxM hallK Ks Z Zhat ClZhat].
  rewrite /partition eqEsubset ntPcover tiPcover notPcover0 !andbT /=.
  apply/subsetP=> x; rewrite !inE andbT => ntx.
  have:= sigma_decomposition_dichotomy ntx.
  have [[y ell1y yRx] _ | _] := exists_inP.
    have [nty /set0Pn[M /setIdP[maxM Ms_y]]] := ell_sigma1P _ ell1y.
    apply/bigcupP; exists (class_support M^~~ G); first exact: mem_imset.
    rewrite -(conjg1 x) mem_imset2 ?inE //.
    apply/bigcupP; exists y; last by rewrite mem_lcoset.
    by rewrite !inE nty -cycle_subG.
  case/exists_inP=> y _; move: (_ * x) => y' /existsP[M].
  case/and3P => /setIdP[maxM _] /setD1P[nty' /setIP[My' _]] kMy' {y}.
  case/set0Pn: MP0; exists M; rewrite 2!inE maxM andbT.
  apply: contra nty' => kM'M; rewrite -order_eq1 (pnat_1 kMy') //.
  exact: mem_p_elt kM'M My'.
have [_ [defNK _] [ntKs _] _ _] := Ptype_structure PmaxM hallK.
have [Mst [PmaxMst _] [_ [hallKst _] [defK _]]] := Ptype_embedding PmaxM hallK.
rewrite -/Ks -/Z -/Zhat in ntKs hallKst * => _  [_ _ conjMMst _].
have [_ _ [ntK _] _ _] := Ptype_structure PmaxMst hallKst.
have [maxM _] := setDP PmaxM; rewrite defK in ntK.
have [|//|tiZPcover notPcovZ]: _ /\ ClZhat \notin _ := trivIsetU1 _ tiPcover _.
  move=> HcovG; case/imsetP=> H maxH ->{HcovG}.
  rewrite -setI_eq0 /ClZhat !class_supportEr big_distrr big1 //= => a _.
  rewrite big_distrl big1 //= => b _; apply/eqP; rewrite -cards_eq0.
  rewrite -(cardJg _ b^-1) conjIg conjsgK -conjsgM -sigma_supportJ cards_eq0.
  wlog ->: a b H maxH / H :^ (a * b^-1) = H.
    by move/(_ a a (H :^ (a * b^-1))%G); rewrite mmaxJ mulgV act1 => ->.
  rewrite setIC big_distrl big1 //= => y Hs_y; apply/setP=> x; rewrite in_set0.
  rewrite 3!inE mem_lcoset negb_or -andbA; apply/and4P=> [[yRx notKx notKs_x]].
  rewrite /Z cent_joinEr ?subsetIr //; case/mulsgP=> z z' Kz Ks_z' defx.
  have:= sigma_decomposition_dichotomy (group1_contra notKx).
  rewrite (introT exists_inP) /=; last first.
    by exists y; rewrite // (Msigma_ell1 maxH).
  have [Ms_z' cKz'] := setIP Ks_z'; case/exists_inP; exists z'.
    rewrite (Msigma_ell1 maxM) ?inE // Ms_z' andbT.
    by apply: contraNneq notKx => z'1; rewrite defx z'1 mulg1.
  apply/existsP; exists M; rewrite inE maxM cycle_subG Ms_z'.
  rewrite defx -(centP cKz') // mulKg (mem_p_elt (pHall_pgroup hallK)) //=.
  rewrite 3!inE (subsetP (pHall_sub hallK)) //= cent1C !andbT.
  rewrite andbC cent1C (subsetP _ _ Kz) ?sub_cent1 //=.
  by apply: contraNneq notKs_x => z1; rewrite defx z1 mul1g.
split=> //; rewrite /partition eqEsubset 2!inE {}tiZPcover negb_or notPcover0.
rewrite /cover big_setU1 {notPcovZ}//= subUset ntPcover subsetD1 subsetT.
rewrite {}/ClZhat {}/Zhat !andbT /= andbC; apply/and3P; split.
- have [[y Ks_y nty] [y' Ky' nty']] := (trivgPn _ ntKs, trivgPn _ ntK).
  rewrite eq_sym; apply/set0Pn; exists ((y' * y) ^ 1).
  apply: mem_imset2; rewrite 2?inE // groupMl // groupMr // -/Ks negb_or.
  have [_ _ _ tiKKs] := dprodP defNK.
  rewrite -[Z]genM_join ?mem_gen ?mem_mulg //= andbT; apply/andP; split.
    by apply: contra nty => Ky; rewrite -in_set1 -set1gE -tiKKs inE Ky.
  by apply: contra nty' => Ks_y'; rewrite -in_set1 -set1gE -tiKKs inE Ky'.
- rewrite class_supportEr; apply/bigcupP=> [[a _]].
  by rewrite mem_conjg conj1g 2!inE !group1.
apply/subsetP=> x; case/setD1P=> ntx _; apply/setUP.
case: exists_inP (sigma_decomposition_dichotomy ntx) => [[y ell1y yRx] _ | _].
  have [nty] := ell_sigma1P _ ell1y; case/set0Pn=> H; case/setIdP=> maxH Hs_y.
  right; apply/bigcupP; exists (class_support H^~~ G); first exact: mem_imset.
  rewrite -[x]conjg1 mem_imset2 ?inE //; apply/bigcupP.
  by exists y; rewrite ?mem_lcoset // !inE nty -cycle_subG.
case/exists_inP=> y ell1y /existsP[H]; set y' := y^-1 * x.
case/and3P=> /setIdP[maxH Hs_y] /setD1P[nty' /setIP[Hy' cyy']] kHy'.
rewrite {ntK ntKs maxM defNK}/Z /Ks; left.
wlog{Ks Mst PmaxMst hallKst conjMMst defK maxH} defH: M K PmaxM hallK / H :=: M.
  move=> IH; have PmaxH: H \in 'M_'P.
    apply/PtypeP; split=> //; exists (pdiv #[y']).
    by rewrite (pnatPpi kHy') // pi_pdiv order_gt1.
  have [|] := setUP (conjMMst H PmaxH); case/imsetP=> a Ga defH.
    have:= IH _ (K :^ a)%G _ _ defH.
    rewrite (eq_pHall _ _ (kappaJ _ _)) pHallJ2 PtypeJ MsigmaJ centJ.
    by rewrite -conjIg -conjUg -conjYg -conjDg class_supportGidl //; apply.
  have:= IH _ [group of Ks :^ a] _ _ defH.
  rewrite (eq_pHall _ _ (kappaJ _ _)) pHallJ2 PtypeJ MsigmaJ centJ.
  rewrite -conjIg -conjUg -conjYg -conjDg setUC joingC defK.
  by rewrite class_supportGidl //; apply.
have /andP[sMsM nMsM]: M`_\sigma <| M := pcore_normal _ M.
have{Hs_y} Ms_y: y \in M`_\sigma by rewrite -defH -cycle_subG.
wlog{H defH Hy' kHy'} Ky': K hallK / y' \in K.
  have [maxM _] := setDP PmaxM; rewrite -cycle_subG defH in Hy' kHy'.
  have [a Ma Ka_y'] := Hall_subJ (mmax_sol maxM) hallK Hy' kHy'.
  move/(_ (K :^ a)%G); rewrite pHallJ // -cycle_subG.
  rewrite -{1 2}(normsP nMsM a Ma) centJ -conjIg -conjYg -conjUg -conjDg.
  by rewrite class_supportGidl ?inE //; apply.
rewrite -[x]conjg1 mem_imset2 ?group1 //.
have [Mst _ [_ _ _ [cycZ _ defZ _ _] _]] := Ptype_embedding PmaxM hallK.
rewrite -(mulKVg y x) -/y' 2!inE negb_or andbC.
do [set Ks := 'C_(_)(K); set Z := K <*> _] in cycZ defZ *.
have Ks_y: y \in Ks.
  have cKZ := sub_abelian_cent (cyclic_abelian cycZ) (joing_subl K Ks). 
  rewrite inE Ms_y (subsetP cKZ) // -(defZ y'); last by rewrite !inE nty'.
  by rewrite inE cent1C (subsetP sMsM).
have [_ [defNK _] _ _ _] := Ptype_structure PmaxM hallK.
have{defNK} [_ _ cKKs tiKKs] := dprodP defNK.
rewrite [Z]joingC cent_joinEl // mem_mulg // groupMr // groupMl //= -/Ks.
apply/andP; split.
  have [nty _] := ell_sigma1P _ ell1y.
  by apply: contra nty => Ky; rewrite -in_set1 -set1gE -tiKKs inE Ky.
by apply: contra nty' => Ks_y'; rewrite -in_set1 -set1gE -tiKKs inE Ky'.
Qed.

(* This is B & G, Corollary 14.10. *)
Corollary ell_sigma_leq_2 x : \ell_\sigma(x) <= 2.
Proof.
have [/ell_sigma0P/eqP-> // | ntx] := eqVneq x 1.
case sigma_x: (x \in cover [set class_support M^~~ G | M : {group gT} in 'M]).
  case/bigcupP: sigma_x => _ /imsetP[M maxM ->].
  case/imset2P=> x0 a /bigcupP[y Ms_y yRx0] _ ->; rewrite ell_sigmaJ.
  exact: ell_sigma_cover (Msigma_ell1 maxM Ms_y) yRx0.
have G1x: x \in G^# by rewrite !inE andbT.
have [FpartG1 PpartG1] := mFT_partition.
have [/eqP/FpartG1 partG1 | [M PmaxM]] := set_0Vmem ('M_'P : {set {group gT}}).
  by rewrite -(cover_partition partG1) sigma_x in G1x.
have [maxM _] := setDP PmaxM.
have [K hallK] := Hall_exists \kappa(M) (mmax_sol maxM).
have{PpartG1} [/cover_partition defG1 notZsigma] := PpartG1 M K PmaxM hallK.
rewrite -{}defG1 /cover big_setU1 {notZsigma}// inE {}sigma_x orbF in G1x.
case/imset2P: G1x => x0 a /setDP[].
have [Mst [PmaxMst _] [_ _ [defK _] _ _]] := Ptype_embedding PmaxM hallK.
rewrite cent_joinEr ?subsetIr // => /mulsgP[y' y Ky' /= Ks_y ->].
rewrite inE; have [-> | nty] := eqVneq y 1; first by rewrite mulg1 Ky'.
have [-> | nty' _ _ ->] := eqVneq y' 1; first by rewrite mul1g Ks_y orbT.
have [Ms_y cKy] := setIP Ks_y; set Ks := 'C_(_)(_) in Ks_y defK.
have Msts_y': y' \in Mst`_\sigma by move: Ky'; rewrite -defK => /setIP[].
have kMy': \kappa(M).-elt y' := mem_p_elt (pHall_pgroup hallK) Ky'.
have{kMy'} sM'y': \sigma(M)^'.-elt y' := sub_pgroup (@kappa_sigma' _) kMy'.
rewrite ell_sigmaJ /sigma_length (cardsD1 (y' * y).`_\sigma(M)).
rewrite (leq_add (leq_b1 _)) // -sigma_decomposition_constt' //.
rewrite consttM /commute ?(centP cKy) // constt_p_elt //.
rewrite (constt1P _) ?p_eltNK ?(mem_p_elt (pcore_pgroup _ _) Ms_y) // mulg1.
have [maxMst _] := setDP PmaxMst; rewrite leq_eqVlt (Msigma_ell1 maxMst) //.
by rewrite !inE nty' Msts_y'.
Qed.

(* This is B & G, Lemma 14.11. *)
Lemma primes_non_Fitting_Ftype M E q Q :
    M \in 'M_'F -> \sigma(M)^'.-Hall(M) E ->
    Q \in 'E_q^1(E) -> ~~ (Q \subset 'F(E)) ->
  exists2 Mstar, Mstar \in 'M &
  [\/ (*1*) q \in \tau2(Mstar) /\ 'M('C(Q)) = [set Mstar]
    | (*2*) q \in \kappa(Mstar) /\ Mstar \in 'M_'P1 ].
Proof.
move=> FmaxM hallE EqQ notsFE_Q; have [maxM k'M] := FtypeP _ FmaxM.
have [sQE abelQ dimQ] := pnElemP EqQ; have [qQ _] := andP abelQ.
have [q_pr oQ] := (pnElem_prime EqQ, card_pnElem EqQ : #|Q| = q).
have t1Mq: q \in \tau1(M).
  have: q \in \pi(E) by rewrite -p_rank_gt0; apply/p_rank_geP; exists Q.
  rewrite (partition_pi_sigma_compl maxM hallE) => /or3P[// | t2q | t3q].
    have [A EqA _] := ex_tau2Elem hallE t2q.
    have [[nsAE defA1] _ _ _] := tau2_compl_context maxM hallE t2q EqA.
    have sQA: Q \subset A by move: EqQ; rewrite defA1 => /pnElemP[].
    rewrite (subset_trans sQA) ?Fitting_max // ?abelian_nil // in notsFE_Q.
    by have [_ abelA _] := pnElemP EqA; apply: abelem_abelian abelA.
  have [[E1 hallE1] [E3 hallE3]] := ex_tau13_compl hallE.
  have [E2 _ complEi] := ex_tau2_compl hallE hallE1 hallE3.
  have [[_ nsE3E] _ [_ cycE3] _ _] := sigma_compl_context maxM complEi.
  have sQE3: Q \subset E3 by rewrite (sub_normal_Hall hallE3) ?(pi_pgroup qQ).
  rewrite (subset_trans sQE3) ?Fitting_max ?abelian_nil // in notsFE_Q.
  exact: cyclic_abelian cycE3.
have q'FE: q^'.-group 'F(E).
  have [R sylR sQR] := Sylow_superset sQE qQ; have [sRE qR _] := and3P sylR.
  have cycR: cyclic R.
    rewrite (odd_pgroup_rank1_cyclic qR) ?mFT_odd // (p_rank_Sylow sylR) //.
    by move: t1Mq; rewrite (tau1E maxM hallE) eqn_leq; case/and4P.
  rewrite -partG_eq1 -(card_Hall (Hall_setI_normal (Fitting_normal E) sylR)).
  have sRFER: R :&: 'F(E) \subset R := subsetIl _ _.
  apply: contraR notsFE_Q; rewrite -trivg_card1 => ntRFE.
  rewrite (subset_trans _ (subsetIr R _)) // -(cardSg_cyclic cycR) // oQ.
  by have [] := pgroup_pdiv (pgroupS sRFER qR) ntRFE.
have cE'E': abelian E^`(1) := der_mmax_compl_abelian maxM hallE.
pose K := [~: E, Q]; have cKK: abelian K by rewrite (abelianS (commgS E sQE)).
have nsKE: K <| E by rewrite /normal commg_norml comm_subG.
have q'K: q^'.-group K by rewrite (pgroupS _ q'FE) // Fitting_max ?abelian_nil.
have [sKE nKE] := andP nsKE; have nKQ := subset_trans sQE nKE.
have defKQ: [~: K, Q] = K.
  have nsKQ_E: K <*> Q <| E.
    rewrite -(quotientGK nsKE) -(quotientYK nKQ) cosetpre_normal /= -/K.
    by rewrite /normal quotientS // cents_norm // quotient_cents2r.
  have [_ sylQ] := coprime_mulGp_Hall (esym (norm_joinEr nKQ)) q'K qQ.
  have defE: K * 'N_E(Q) = E.
    rewrite -{2}(Frattini_arg nsKQ_E sylQ) /= norm_joinEr //= -/K -mulgA.
    by congr (K * _); rewrite mulSGid // subsetI sQE normG.
  have cQ_NEQ: [~: 'N_E(Q), Q] = 1.
    apply/trivgP; rewrite -(coprime_TIg (pnat_coprime qQ q'K)) subsetI.
    by rewrite commg_subr subsetIr commSg ?subsetIl.
  by rewrite {2}/K -defE commMG ?cQ_NEQ ?mulg1 1?normsR ?subsetIr ?subIset ?nKE.
have [sEM s'E _] := and3P hallE; have sQM := subset_trans sQE sEM.
have [sKM s'K] := (subset_trans sKE sEM, pgroupS sKE s'E).
have regQ: 'C_(M`_\sigma)(Q) = 1.
  apply/eqP; apply: contraFT (k'M q) => nregQ.
  have EqQ_M: Q \in 'E_q^1(M) by apply/pnElemP.
  by rewrite unlock 3!inE /= t1Mq; apply/exists_inP; exists Q. 
have nsKM: K <| M.
  have [s'q _] := andP t1Mq.
  have EqQ_NK: Q \in 'E_q^1('N_M(K)) by apply/pnElemP; rewrite subsetI sQM.
  have:= commG_sigma'_1Elem_cyclic maxM sKM s'K s'q EqQ_NK regQ q'K cKK.
  by rewrite defKQ; case.
have ntK: K != 1.
  apply: contraNneq notsFE_Q => /commG1P cQE.
  by rewrite Fitting_max ?(pgroup_nil qQ) // /normal sQE cents_norm.
pose p := pdiv #|K|; have p_pr: prime p by rewrite pdiv_prime ?cardG_gt1.
have piKp: p \in \pi(K) by rewrite pi_pdiv cardG_gt1.
have t2Mp: p \in \tau2(M).
  have s'p := pnatPpi s'K piKp.
  have sylKp: p.-Sylow(K) 'O_p(K) := nilpotent_pcore_Hall p (abelian_nil cKK).
  rewrite inE /= s'p ?(sigma'_norm_mmax_rank2 maxM s'p (pHall_pgroup sylKp)) //.
  rewrite (mmax_normal maxM) ?(char_normal_trans (pcore_char _ _)) //.
  by rewrite -rank_gt0 (rank_Sylow sylKp) p_rank_gt0.
have [A EpA _] := ex_tau2Elem hallE t2Mp.
have [sAE] := pnElemP EpA; case/andP=> pA _ dimA.
have [[nsAE _] _ _ _] := tau2_compl_context maxM hallE t2Mp EpA.
have nAQ := subset_trans sQE (normal_norm nsAE).
have [S sylS sAS]:= Sylow_superset (subsetT A) pA.
have not_cSS: ~~ abelian S.
  apply: contra notsFE_Q => cSS; rewrite Fitting_max ?(pgroup_nil qQ) //.
  have solE := sigma_compl_sol hallE.
  have [E1 hallE1 sQE1] := Hall_superset solE sQE (pi_pgroup qQ t1Mq).
  have [_ [E3 hallE3]] := ex_tau13_compl hallE.
  have [E2 _ complEi] := ex_tau2_compl hallE hallE1 hallE3.
  have [_ _ _ sQZ] := abelian_tau2 maxM complEi t2Mp EpA sylS sAS cSS.
  by rewrite sub_center_normal ?{}sQZ //; apply/nElemP; exists q; apply/pnElemP.
have [] := nonabelian_tau2 maxM hallE t2Mp EpA (pHall_pgroup sylS) not_cSS.
set A0 := 'C_A(M`_\sigma)%G => _ [oA0 defFM] _ _.
have defA0: A0 :=: K.
  have sA0E: A0 \subset E by rewrite subIset ?sAE.
  have sKA0: K \subset A0.
    have [_ _ _ tiMsE] := sdprodP (sdprod_sigma maxM hallE).
    rewrite -(mul1g A0) -tiMsE setIC group_modr // subsetI sKE.
    by have [_ -> _ _] := dprodP defFM; rewrite Fitting_max ?abelian_nil.
  by apply/eqP; rewrite eqEsubset prime_meetG ?(setIidPr sKA0) ?oA0.
have ntA: A :!=: 1 := nt_pnElem EpA isT.
have [H maxNH] := mmax_exists (mFT_norm_proper ntA (mFT_pgroup_proper pA)).
have [maxH sNH] := setIdP maxNH; have sQH := subset_trans nAQ sNH.
exists H => //.
have: p \in [predD \sigma(H) & \beta(H)] /\ q \in [predU \tau1(H) & \tau2(H)].
  have [-> // piAb _] := primes_norm_tau2Elem maxM hallE t2Mp EpA maxNH.
  rewrite (pnatPpi piAb) // (piSg (quotientS _ sQE)) //=.
  have piQq: q \in \pi(Q) by rewrite -p_rank_gt0 p_rank_abelem ?dimQ.
  rewrite /= card_quotient ?normsI ?norms_cent // ?normsG //.
  rewrite -indexgI setIA (setIidPl sQE) prime_TIg ?indexg1 // ?oQ //.
  rewrite (sameP commG1P eqP) (subG1_contra _ ntK) //= -/K -defKQ commGC.
  by rewrite -defA0 commgS ?subsetIl.
case=> /andP[/= b'Hp sHP] t12Hq.
have nregQHs: 'C_(H`_\sigma)(Q) != 1.
  apply: subG1_contra (setSI _ _) (_ : 'C_A(Q) != 1).
    rewrite (sub_Hall_pcore (Msigma_Hall maxH)) ?(pi_pgroup pA) //.
    exact: subset_trans (normG A) sNH.
  apply: contraTneq (leqnn 1) => regQA; rewrite -ltnNge -dimA.
  rewrite -(leq_exp2l _ _ (prime_gt1 p_pr)) -card_pgroup // -oA0 defA0.
  have coAQ := pnat_coprime (pi_pnat pA t2Mp) (pi_pnat qQ (tau2'1 t1Mq)).
  rewrite subset_leq_card // -(coprime_cent_prod nAQ) ?(pgroup_sol pA) //.
  by rewrite regQA mulg1 commSg.
have{t12Hq} [/= t1Hq | /= t2Hq] := orP t12Hq.
  have EqQ_H: Q \in 'E_q^1(H) by apply/pnElemP.
  have kHq: q \in \kappa(H).
    by rewrite unlock 3!inE /= t1Hq; apply/exists_inP; exists Q.
  right; split=> //; apply: contraR b'Hp => notP1maxH.
  have PmaxH: H \in 'M_'P by apply/PtypeP; split=> //; exists q.
  have [L hallL] := Hall_exists \kappa(H) (mmax_sol maxH).
  by have [_ _ _ _ [|<- //]] := Ptype_structure PmaxH hallL; apply/setDP.
left; split=> //.
have [x defQ]: exists x, Q :=: <[x]> by apply/cyclicP; rewrite prime_cyclic ?oQ.
rewrite defQ cent_cycle in nregQHs *; rewrite (cent1_nreg_sigma_uniq maxH) //. 
  by rewrite 2!inE -cycle_eq1 -cycle_subG -defQ (nt_pnElem EqQ).
by rewrite /p_elt /order -defQ oQ pnatE.
Qed.

(* This is B & G, Lemma 14.12. *)
(* Note that the assumption M \in 'M_'P2 could be weakened to M \in 'M_'P,   *)
(* since the assumption H \in 'M('N(R)) implies H != 1, and hence U != 1.    *)
Lemma P2type_signalizer M Mstar U K r R H :
    M \in 'M_'P2 -> kappa_complement M U K -> Mstar \in 'M('C(K)) ->
    r.-Sylow(U) R -> H \in 'M('N(R)) ->
  [/\ H \in 'M_'F, U \subset H`_\sigma, U <*> K = M :&: H
   & [/\ ~~ ('N_H(U) \subset M), K \subset 'F(H :&: Mstar)
       & \sigma(H)^'.-Hall(H) (H :&: Mstar)]].
Proof.
move=> P2maxM complU maxCMstar sylR maxNH; have [hallU hallK _] := complU.
have [PmaxM notP1maxM] := setDP P2maxM; have [maxM notFmaxM] := setDP PmaxM.
have [[sUM sk'M_U _] [sKM kK _]] := (and3P hallU, and3P hallK).
have{notFmaxM} ntK: K :!=: 1 by rewrite (trivg_kappa maxM).
have [hallE defM _ regK /(_ ntK)cUU] := kappa_compl_context maxM complU.
case/sdprodP: defM => [[_ E _ defE] _ _ _].
have [nsUE sKE mulUK nUK tiUK] := sdprod_context defE.
rewrite (norm_joinEr nUK) mulUK in hallE *.
have [Mst [PmaxMst notMGMst] [uniqMst []]] := Ptype_embedding PmaxM hallK.
set Ks := 'C_(_)(K) => hallKs; case/and3P=> sKsMst sM_Ks _ [defK _].
case=> cycZ ziMMst _ _ _ [_ _ defPmax _].
have [_ [defNK _] [ntKs _] _ [//|_ q_pr _ _]] := Ptype_structure PmaxM hallK.
set q := #|K| in q_pr.
have{uniqMst} uniqMst: 'M('C(K)) = [set Mst].
  by apply: uniqMst; apply/nElemP; exists q; rewrite p1ElemE // !inE subxx /=.
have{maxCMstar} ->: Mstar = Mst by [apply/set1P; rewrite -uniqMst] => {Mstar}.
have [maxH sNRH] := setIdP maxNH.
have ntR: R :!=: 1.
  by apply: contraTneq sNRH => ->; rewrite norm1 proper_subn ?mmax_proper.
have piUr: r \in \pi(U) by rewrite -p_rank_gt0 -(rank_Sylow sylR) rank_gt0.
have r_pr: prime r by move: piUr; rewrite mem_primes; case/andP.
have sylR_M := subHall_Sylow hallU (pnatPpi sk'M_U piUr) sylR.
have [/= s'Mr k'Mr] := norP (pnatPpi sk'M_U piUr).
have [sRH [sRM rR _]] := (subset_trans (normG R) sNRH, and3P sylR_M).
have notMGH: gval H \notin M :^: G.
  apply: contra s'Mr; case/imsetP=> a _ defH.
  rewrite -(sigmaJ _ a) -defH; apply/exists_inP; exists R => //.
  by rewrite pHallE sRH /= (card_Hall sylR_M) defH cardJg.
have sK_uniqMst a: K \subset Mst :^ a -> a \in Mst.
  move=> sKMa; apply: contraR ntK; rewrite -in_setC => Mst'a.
  have [_ _ _ [[tiK_MstG _] _ _] _] := Ptype_structure PmaxMst hallKs.
  by rewrite -(tiK_MstG a) // defK (setIidPl sKMa).
have [_ _] := dprodP defNK; rewrite -/Ks => cKKs tiKKs.
have snK_sMst L: K <|<| L -> L \subset Mst.
  elim: {L}_.+1 {-2}L (ltnSn #|L|) => // n IHn A leAn.
  case/subnormalEr=> [<- | [L [snKL nsLA ltLA]]].
    by rewrite -defK subIset // pcore_sub.
  have [sKL sLMst]: K \subset L /\ L \subset Mst.
    by rewrite subnormal_sub // IHn // (leq_trans (proper_card ltLA)).
  apply/subsetP=> a Aa; rewrite -groupV sK_uniqMst // (subset_trans sKL) //.
  by rewrite -sub_conjg (normsP (normal_norm nsLA)).
have sEH: E \subset H.
  apply: subset_trans (char_norm_trans _ (normal_norm nsUE)) sNRH.
  by rewrite (nilpotent_Hall_pcore (abelian_nil cUU) sylR) pcore_char.
have [sUH sKH]: U \subset H /\ K \subset H by apply/mulGsubP; rewrite mulUK.
have notMstGH: gval H \notin Mst :^: G.
  apply: contra ntR => /imsetP[a _ defH].
  have{a defH} defH: H :=: Mst by rewrite -(conjGid (sK_uniqMst a _)) -?defH.
  rewrite -(setIidPl sRH) -(setIidPl sRM) -setIA defH ziMMst coprime_TIg //=.
  rewrite cent_joinEr // TI_cardMg //= coprime_mulr -/Ks.
  rewrite (p'nat_coprime (pi_pnat rR _) kK) //=.
  exact: p'nat_coprime (pi_pnat rR _) sM_Ks.
have FmaxH: H \in 'M_'F.
  suffices: H \notin 'M_'P by rewrite inE maxH andbT negbK.
  by apply: (contra (defPmax H)); rewrite inE; apply/norP.
have sKMsts: K \subset Mst`_\sigma by rewrite -defK subsetIl.
have s'H_K: \sigma(H)^'.-group K.
  apply/pgroupP=> p p_pr p_dv_K; have [maxMst _] := setDP PmaxMst.
  apply: contraFN (sigma_partition maxMst maxH notMstGH p) => /= sHp.
  by rewrite inE /= (pgroupP (pgroupS sKMsts _)) ?pcore_pgroup.
have [D hallD sKD] := Hall_superset (mmax_sol maxH) sKH s'H_K.
have piKq: q \in \pi(K) by rewrite pi_of_prime ?inE.
have sK_FD: K \subset 'F(D).
  have EqK: K \in 'E_q^1(D) by rewrite p1ElemE // !inE sKD /=.
  have sMst_q: q \in \sigma(Mst).
    by rewrite (pnatPpi (pcore_pgroup _ _) (piSg sKMsts _)).
  apply: contraR notP1maxM => not_sKFD.
  have [L _ ] := primes_non_Fitting_Ftype FmaxH hallD EqK not_sKFD.
  case=> [[t2Lq ]|[kLq P1maxL]].
    rewrite uniqMst => /set1_inj defL.
    by rewrite -defL 3!inE sMst_q in t2Lq.
  have [PmaxL _] := setIdP P1maxL.
  case/setUP: (defPmax L PmaxL) => /imsetP[a _ defL].
    by rewrite (group_inj defL) P1typeJ in P1maxL.
  move: kLq; rewrite defL kappaJ unlock 3!inE /=.
  by rewrite -andb_orr inE /= sMst_q.
have sDMst: D \subset Mst.
  apply: snK_sMst (subnormal_trans _ (normal_subnormal (Fitting_normal D))).
  exact: nilpotent_subnormal (Fitting_nil D) sK_FD.
have defUK: [~: U, K] = U.
  rewrite -{2}(coprime_cent_prod nUK) ?abelian_sol //; last first.
    by apply: p'nat_coprime (sub_pgroup _ sk'M_U) kK => ? /norP[].
  by rewrite (cent_semiregular regK) ?mulg1.
have qK: q.-group K := pnat_id q_pr.
have sUHs: U \subset H`_\sigma.
  have [nsHsH _ mulHsD nHsD _] := sdprod_context (sdprod_sigma maxH hallD).
  have nHsDq := subset_trans (pcore_sub q D) nHsD.
  pose HsDq := H`_\sigma <*> 'O_q(D).
  have defHsDq: H`_\sigma * 'O_q(D) = HsDq by rewrite -norm_joinEr.
  have hallHs_HsDq: q^'.-Hall(HsDq) H`_\sigma.
    have [|//] := coprime_mulGp_Hall defHsDq _ (pcore_pgroup _ _).
    rewrite p'groupEpi; apply: (contra (pnatPpi (pcore_pgroup _ _))).
    exact: pnatPpi s'H_K piKq.
  have sK_HsDq: K \subset HsDq.
    rewrite sub_gen ?subsetU // orbC -p_core_Fitting.
    by rewrite (sub_Hall_pcore (nilpotent_pcore_Hall _ (Fitting_nil _))) ?qK.
  have [|sHsDq_H nHsDq_H] := andP (_ : HsDq <| H).   
    rewrite -(quotientGK nsHsH) -[HsDq]quotientYK //= cosetpre_normal //.
    by rewrite -{3}mulHsD quotientMidl quotient_normal // pcore_normal.
  have sU_HsDq: U \subset HsDq.
    by rewrite -defUK (subset_trans (commgSS sUH sK_HsDq)) // commg_subr.
  rewrite (sub_normal_Hall hallHs_HsDq) //.
    rewrite p'groupEpi; apply: (contraL (pnatPpi sk'M_U)) => /=.
    by rewrite inE /= orbC (pnatPpi kK).
  exact: normalS (joing_subl _ _) _ (pcore_normal _ _).
have defNMU: 'N_M(U) = E.
  have [_ mulHsE nHsE _] := sdprodP (sdprod_sigma maxM hallE).
  have [sUE nUE] := andP nsUE; rewrite -mulHsE -normC // -group_modl //=.
  rewrite coprime_norm_cent ?(subset_trans sUE) //; last first.
    exact: coprimegS sUE (coprime_sigma_compl hallE).
  have sR1U: 'Ohm_1(R) \subset U := subset_trans (Ohm_sub 1 R) (pHall_sub sylR).
  rewrite (trivgP (subset_trans (setIS _ (centS sR1U)) _)) ?mulg1 //.
  have [|_ _ -> //] := sigma'_kappa'_facts maxM sylR_M.
  by rewrite s'Mr (piSg sUM).
have sHsFH: H`_\sigma \subset 'F(H).
  rewrite Fitting_max ?pcore_normal //.
  have [S] := Sylow_exists q H; case/sigma'_kappa'_facts=> {S}//.
  have [_ k'H] := setIdP FmaxH.
  rewrite [~~ _](pnatPpi (pHall_pgroup hallD) (piSg sKD _)) //=.
  by rewrite [~~ _](pnatPpi k'H) (piSg sKH).
suffices ->: H :&: Mst = D.
  set sk' := _^' in sk'M_U hallU; pose Fu := 'O_sk'('F(H)).
  have [sUFH nilFH] := (subset_trans sUHs sHsFH, Fitting_nil H).
  have hallFu: sk'.-Hall('F(H)) Fu := nilpotent_pcore_Hall sk' nilFH.
  have sUFu: U \subset Fu by rewrite (sub_Hall_pcore hallFu).
  have nsFuH: Fu <| H := char_normal_trans (pcore_char _ _) (Fitting_normal _).
  have [[sFuFH sk'Fu _] [sFuH nFuH]] := (and3P hallFu, andP nsFuH).
  have defU: M :&: Fu = U.
    have sk'MFu: sk'.-group(M :&: Fu) := pgroupS (subsetIr M _) sk'Fu.
    by rewrite (sub_pHall hallU sk'MFu) ?subsetIl // subsetI sUM.
  do 2?split=> //.
    apply/eqP; rewrite eqEsubset subsetI (pHall_sub hallE) sEH /=.
    by rewrite -defNMU subsetI subsetIl -defU normsGI.
  apply: contra (contra_orbit _ _ notMGH) => sNHU_M.
  rewrite (eq_mmax maxH maxM (subset_trans _ sNHU_M)) // subsetIidl.
  rewrite -(nilpotent_sub_norm (nilpotentS sFuFH nilFH) sUFu) //= -/Fu.
  by rewrite -{2}defU subsetI subsetIl (subset_trans (setSI _ sFuH)).
have [maxMst _] := setDP PmaxMst.
have [_ <- _ _] := sdprodP (sdprod_sigma maxH hallD).
rewrite -{2}(mul1g D) setIC -group_modr // setIC; congr (_ * _).
apply/eqP; apply: wlog_neg => ntHsMst.
have nregHsK: 'C_(H`_\sigma)(K) != 1.
  rewrite (subG1_contra _ ntHsMst) // subsetI subsetIl (sameP commG1P trivgP).
  have <-: H`_\sigma :&: Mst`_\sigma = 1.
    apply: card_le1_trivg; rewrite leqNgt -pi_pdiv; set p := pdiv _.
    apply: contraFN (sigma_partition maxMst maxH notMstGH p) => piIp.
    rewrite inE /= (pnatPpi (pcore_pgroup _ _) (piSg (subsetIl _ _) piIp)).
    by rewrite (pnatPpi (pcore_pgroup _ _) (piSg (subsetIr _ _) piIp)).
  rewrite commg_subI ?setIS ?gFnorm // subsetI sKMsts.
  by rewrite (subset_trans sKH) ?gFnorm.
have t2Hq: q \in \tau2(H).
  have: q \in \pi(D) := piSg sKD piKq.
  rewrite (partition_pi_sigma_compl maxH hallD) orbCA; case/orP=> // t13Hq.
  case/FtypeP: FmaxH => _ /(_ q)/idP[]; rewrite unlock 3!inE /= t13Hq.
  by apply/exists_inP; exists K => //; rewrite p1ElemE // !inE sKH /=.
have [A EqA_D EqA] := ex_tau2Elem hallD t2Hq.
have [_ _ _ -> //] := tau2_context maxH t2Hq EqA.
rewrite 3!inE -val_eqE /= eq_sym (contra_orbit _ _ notMstGH) maxMst.
by have [sAD _ _] := pnElemP EqA_D; apply: subset_trans sAD sDMst.
Qed.

(* This is B & G, Lemma 14.13(a). *)
(* Part (b) is not needed for the Peterfalvi revision of the character theory *)
(* part of the proof.                                                         *)
Lemma non_disjoint_signalizer_Frobenius x M :
    \ell_\sigma(x) == 1%N -> #|'M_\sigma[x]| > 1 ->
    M \in 'M_\sigma[x] -> ~~ (\sigma('N[x])^'.-group M) ->
  M \in 'M_'F /\ \tau2(M)^'.-group M.
Proof.
move=> ell1x ntR SMxM; have [maxM Ms_x] := setIdP SMxM.
rewrite negb_and cardG_gt0 all_predC negbK => /hasP[q /= piMq sNq].
have [Q EqQ]: exists Q, Q \in 'E_q^1(M) by apply/p_rank_geP; rewrite p_rank_gt0.
have [ntQ [sQM abelQ dimQ]] := (nt_pnElem EqQ isT, pnElemP EqQ).
have [[qQ _] q_pr] := (andP abelQ, pnElem_prime EqQ).
have [_ [//| uniqN _ t2Nx _]] := FT_signalizer_context ell1x.
case/(_ M SMxM)=> _ st2NsM spM_sbN _; have [maxN sCxN] := mem_uniq_mmax uniqN.
have bNq: q \in \beta('N[x]) by rewrite spM_sbN //= 4!inE /= piMq.
have bGq: q \in \beta(G) by move: bNq; rewrite -predI_sigma_beta // inE /= sNq.
set p := pdiv #[x]; have pi_p: p \in \pi(#[x]).
  by rewrite pi_pdiv order_gt1 (sameP eqP (ell_sigma0P _)) (eqP ell1x).
have sMp: p \in \sigma(M) := pnatPpi (pcore_pgroup _ _) (piSg Ms_x pi_p).
have t2Np: p \in \tau2('N[x]) := pnatPpi t2Nx pi_p.
have notMGN: gval 'N[x] \notin M :^: G.
  apply: contraL t2Np => /imsetP[a _ ->].
  by rewrite negb_and negbK /= sigmaJ sMp.
have sM'q: q \in \sigma(M)^'.
  by apply: contraFN (sigma_partition maxM maxN notMGN q) => sMq; apply/andP.
have [g sQNg]: exists g, Q \subset 'N[x] :^ g.
  have [Q1 sylQ1] := Sylow_exists q 'N[x].
  have [g _ sQQ1g] := Sylow_subJ (sigma_Sylow_G maxN sNq sylQ1) (subsetT Q) qQ.
  by exists g; rewrite (subset_trans sQQ1g) // conjSg (pHall_sub sylQ1).
have EqNQ: Q \in 'E_q^1('N[x] :^ g) by apply/pnElemP.
have uniqNg: 'M('C(Q)) = [set 'N[x] :^ g]%G.
  by case/cent_der_sigma_uniq: EqNQ; rewrite ?mmaxJ 1?betaJ ?bNq.
have b'Mp: p \notin \beta(M).
  by rewrite -predI_sigma_beta // inE /= sMp /=; case/tau2_not_beta: t2Np.
have{p pi_p sMp t2Np b'Mp} FmaxM: M \in 'M_'F.
  have [P1maxM | notP1maxM] := boolP (M \in 'M_'P1); last first.
    have [K hallK] := Hall_exists \kappa(M) (mmax_sol maxM).
    apply: contraR b'Mp => notFmaxM; have PmaxM: M \in 'M_'P by apply/setDP.
    by have [_ _ _ _ [|<- //]] := Ptype_structure PmaxM hallK; apply/setDP.
  have [PmaxM skM] := setIdP P1maxM.
  have kMq: q \in \kappa(M).
    by case/orP: (pnatPpi skM piMq) => //= sMq; case/negP: sM'q.
  have [K hallK sQK] := Hall_superset (mmax_sol maxM) sQM (pi_pnat qQ kMq).
  have EqKQ: Q \in 'E_q^1(K) by apply/pnElemP.  
  have [L _ [uniqL [kLhallKs sMhallKs] _ _ _]] := Ptype_embedding PmaxM hallK.
  set Ks := 'C_(_)(K) in kLhallKs sMhallKs.
  have{uniqL} defL: 'N[x] :^ g = L.
    apply: congr_group; apply: set1_inj; rewrite -uniqNg uniqL //.
    by apply/nElemP; exists q.
  have rpL: 'r_p(L) = 2.
    by apply/eqP; case/andP: t2Np => _; rewrite -defL p_rankJ.
  suffices piKs_p: p \in \pi(Ks).
    by rewrite rank_kappa // (pnatPpi (pHall_pgroup kLhallKs)) in rpL.
  have [P sylP] := Sylow_exists p [group of Ks].
  have sylP_L: p.-Sylow(L) P := subHall_Sylow sMhallKs sMp sylP.
  by rewrite -p_rank_gt0 -(rank_Sylow sylP) (rank_Sylow sylP_L) ?rpL.
split=> //; apply: sub_pgroup (pgroup_pi _) => p piMp; apply/negP=> /= t2Mp.
have rpN: 'r_p('N[x]) <= 1.
  have: p \notin \beta('N[x]).
    rewrite -(predI_sigma_beta maxN) negb_and /= orbC.
    by have [-> _] := tau2_not_beta maxM t2Mp.
  apply: contraR; rewrite -ltnNge => rpN; rewrite spM_sbN // inE /= piMp.
  have: p \in \pi('N[x]) by rewrite -p_rank_gt0 ltnW.
  rewrite (partition_pi_mmax maxN) orbCA => /orP[t2Np | ].
    by case/andP: t2Mp => /negP[]; apply: st2NsM.
  by rewrite orbA -!andb_orr eqn_leq leqNgt rpN andbF.
have [E hallE sQE] := Hall_superset (mmax_sol maxM) sQM (pi_pgroup qQ sM'q).
have [A Ep2A _] := ex_tau2Elem hallE t2Mp; have [_ abelA dimA] := pnElemP Ep2A.
pose A0 := [~: A, Q]%G; pose A1 := 'C_A(Q)%G.
have sCQNg: 'C(Q) \subset 'N[x] :^ g by have [] := mem_uniq_mmax uniqNg.
have ntA0: A0 :!=: 1.
  rewrite (sameP eqP commG1P); apply: contraL rpN => cQA.
  rewrite -ltnNge -(p_rankJ p _ g); apply/p_rank_geP.
  by exists A; apply/pnElemP; rewrite (subset_trans cQA).
have t1Mq: q \in \tau1(M).
  have [_ nsCEA_E t1Eb] := tau1_cent_tau2Elem_factor maxM hallE t2Mp Ep2A.
  rewrite (pnatPpi t1Eb) // (piSg (quotientS _ sQE)) // -p_rank_gt0.
  rewrite -rank_pgroup ?quotient_pgroup // rank_gt0 -subG1.
  rewrite quotient_sub1 ?(subset_trans _ (normal_norm nsCEA_E)) //.
  by rewrite subsetI sQE centsC (sameP commG1P eqP).
have EqEQ: Q \in 'E_q^1(E) by apply/pnElemP.
have regMsQ: 'C_(M`_\sigma)(Q) = 1.
  apply: contraTeq FmaxM => nregMsQ; apply/FtypeP=> [[_]]; move/(_ q).
  by rewrite unlock 3!inE /= t1Mq; case/exists_inP; exists Q.
have [[]] := tau1_act_tau2 maxM hallE t2Mp Ep2A t1Mq EqEQ regMsQ ntA0.
rewrite -/A0 -/A1 => EpA0 cMsA0 _ notA1GA0 [EpA1 _].
have [sA0A abelA0 oA0] := pnElemPcard EpA0; have [pA0 _] := andP abelA0.
have [sA1A abelA1 oA1] := pnElemPcard EpA1; have [pA1 _] := andP abelA1.
have sA0N: A0 \subset 'N[x].
  rewrite -cMsA0 (subset_trans _ sCxN) //= -cent_cycle (centsS Ms_x) //.
  exact: subsetIr.
have [P sylP sA0P] := Sylow_superset sA0N pA0; have [_ pP _] := and3P sylP.
have cycP: cyclic P.
  by rewrite (odd_pgroup_rank1_cyclic pP) ?mFT_odd ?(p_rank_Sylow sylP).
have sA1gN: A1 :^ g^-1 \subset 'N[x] by rewrite sub_conjgV subIset ?sCQNg ?orbT.
have [|z _ sA1gzP] := Sylow_Jsub sylP sA1gN; first by rewrite pgroupJ.
case/imsetP: notA1GA0; exists (g^-1 * z); rewrite ?inE // conjsgM.
by apply/eqP; rewrite (eq_subG_cyclic cycP) // !cardJg oA0 oA1.
Qed.

End Section14.


