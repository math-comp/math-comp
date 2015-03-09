(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice div fintype.
Require Import path bigop finset prime fingroup morphism perm automorphism.
Require Import quotient action gproduct gfunctor pgroup cyclic commutator.
Require Import center gseries nilpotent sylow abelian maximal hall frobenius.
Require Import BGsection1 BGsection2 BGsection3 BGsection4 BGsection5.
Require Import BGsection6 BGsection7 BGsection9 BGsection10 BGsection12.
Require Import BGsection13 BGsection14.

(******************************************************************************)
(*   This file covers B & G, section 15; it fills in the picture of maximal   *)
(* subgroups that was sketched out in section14, providing an intrinsic       *)
(* characterization of M`_\sigma and establishing the TI property for the     *)
(* "kernels" of maximal groups. We introduce only one new definition:         *)
(*    M`_\F == the (direct) product of all the normal Sylow subgroups of M;   *)
(*             equivalently, the largest normal nilpotent Hall subgroup of M  *)
(*             We will refer to M`_\F as the Fitting core or F-core of M.     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Section Definitions.

Variables (gT : finGroupType) (M : {set gT}).

Definition Fitting_core :=
  <<\bigcup_(P : {group gT} | Sylow M P && (P <| M)) P>>.
Canonical Structure Fitting_core_group := [group of Fitting_core].

End Definitions.

Notation "M `_ \F" := (Fitting_core M)
  (at level 3, format "M `_ \F") : group_scope.
Notation "M `_ \F" := (Fitting_core_group M) : Group_scope.

Section FittingCore.

Variable (gT : finGroupType) (M : {group gT}).
Implicit Types H P : {group gT}.
Implicit Type p : nat.

Lemma Fcore_normal : M`_\F <| M.
Proof.
rewrite -[M`_\F]bigprodGE.
elim/big_ind: _ => [|P Q nsP nsG|P /andP[] //]; first exact: normal1.
by rewrite /normal normsY ?normal_norm // join_subG ?normal_sub.
Qed.
Hint Resolve Fcore_normal.

Lemma Fcore_sub : M`_\F \subset M.
Proof. by case/andP: Fcore_normal. Qed.

Lemma Fcore_sub_Fitting : M`_\F \subset 'F(M).
Proof.
rewrite gen_subG; apply/bigcupsP=> P /andP[/SylowP[p _ /and3P[_ pP _]] nsP].
by rewrite Fitting_max // (pgroup_nil pP).
Qed.

Lemma Fcore_nil : nilpotent M`_\F.
Proof. exact: nilpotentS Fcore_sub_Fitting (Fitting_nil M). Qed.

Lemma Fcore_max pi H :
  pi.-Hall(M) H -> H <| M -> nilpotent H -> H \subset M`_\F.
Proof.
move=> hallH nsHM nilH; have [sHM pi_H _] := and3P hallH.
rewrite -(nilpotent_Fitting nilH) FittingEgen genS //.
apply/bigcupsP=> [[p /= _] piHp]; rewrite (bigcup_max 'O_p(H)%G) //.
have sylHp := nilpotent_pcore_Hall p nilH.
have sylHp_M := subHall_Sylow hallH (pnatPpi pi_H piHp) sylHp.
by rewrite (p_Sylow sylHp_M) (char_normal_trans (pcore_char _ _)).
Qed.

Lemma Fcore_dprod : \big[dprod/1]_(P | Sylow M (gval P) && (P <| M)) P = M`_\F.
Proof.
rewrite -[M`_\F]bigprodGE.
apply/eqP/bigdprodYP=> P /andP[/SylowP[p p_pr sylP] nsPM].
have defP := normal_Hall_pcore sylP nsPM.
have /dprodP[_ _ cFpFp' tiFpFp'] := nilpotent_pcoreC p (Fitting_nil M).
have /dprodYP := dprodEY cFpFp' tiFpFp'; rewrite /= p_core_Fitting defP.
apply: subset_trans; rewrite bigprodGE gen_subG.
apply/bigcupsP=> Q => /andP[/andP[/SylowP[q _ sylQ] nsQM] neqQP].
have defQ := normal_Hall_pcore sylQ nsQM; rewrite -defQ -p_core_Fitting.
apply: sub_pcore => q' /eqnP->; apply: contraNneq neqQP => eq_qp.
by rewrite -val_eqE /= -defP -defQ eq_qp.
Qed.

Lemma Fcore_pcore_Sylow p : p \in \pi(M`_\F) -> p.-Sylow(M) 'O_p(M).
Proof.
rewrite /= -(bigdprod_card Fcore_dprod) mem_primes => /and3P[p_pr _].
have not_p_dv_1: ~ p %| 1 by rewrite gtnNdvd ?prime_gt1.
elim/big_ind: _ => // [p1 p2 IH1 IH2|P /andP[/SylowP[q q_pr sylP] nsPM p_dv_P]].
  by rewrite Euclid_dvdM // => /orP[/IH1 | /IH2].
have qP := pHall_pgroup sylP.
by rewrite (eqnP (pgroupP qP p p_pr p_dv_P)) (normal_Hall_pcore sylP).
Qed.

Lemma p_core_Fcore p : p \in \pi(M`_\F) -> 'O_p(M`_\F) = 'O_p(M).
Proof.
move=> piMFp /=; rewrite -(pcore_setI_normal p Fcore_normal).
apply/setIidPl; rewrite sub_gen // (bigcup_max 'O_p(M)%G) //= pcore_normal.
by rewrite (p_Sylow (Fcore_pcore_Sylow piMFp)).
Qed.

Lemma Fcore_Hall : \pi(M`_\F).-Hall(M) M`_\F.
Proof.
rewrite Hall_pi // /Hall Fcore_sub coprime_pi' ?cardG_gt0 //=.
apply/pnatP=> // p p_pr; apply: contraL => /= piMFp; rewrite -p'natE //.
rewrite -partn_eq1 // -(eqn_pmul2l (part_gt0 p #|M`_\F|)) muln1.
rewrite -partnM ?cardG_gt0 // Lagrange ?Fcore_sub //.
rewrite -(card_Hall (nilpotent_pcore_Hall p Fcore_nil)) /=.
by rewrite p_core_Fcore // (card_Hall (Fcore_pcore_Sylow piMFp)).
Qed.

Lemma pcore_Fcore pi : {subset pi <= \pi(M`_\F)} -> 'O_pi(M`_\F) = 'O_pi(M).
Proof.
move=> s_pi_MF; rewrite -(pcore_setI_normal pi Fcore_normal).
apply/setIidPl; rewrite (sub_normal_Hall Fcore_Hall) ?pcore_sub //.
exact: sub_pgroup s_pi_MF (pcore_pgroup pi M).
Qed.

Lemma Fcore_pcore_Hall pi : {subset pi <= \pi(M`_\F)} -> pi.-Hall(M) 'O_pi(M).
Proof.
move=> s_pi_MF; apply: (subHall_Hall Fcore_Hall s_pi_MF).
by rewrite /= -pcore_Fcore // (nilpotent_pcore_Hall pi Fcore_nil).
Qed.

End FittingCore.

Lemma morphim_Fcore : GFunctor.pcontinuous Fitting_core.
Proof.
move=> gT rT G D f; have nsGF_G := Fcore_normal G.
suffices hall_fGF: \pi(G`_\F).-Hall(f @* (D :&: G)) (f @* (D :&: G`_\F)).
  rewrite !morphimIdom in hall_fGF.
  by rewrite (Fcore_max hall_fGF) ?morphim_normal // morphim_nil ?Fcore_nil.
rewrite morphim_pHall ?subsetIl //= -{2}(setIidPr (Fcore_sub G)) setIA.
by rewrite !(setIC (D :&: G)) (setI_normal_Hall nsGF_G) ?subsetIr ?Fcore_Hall.
Qed.

Canonical Structure Fcore_igFun := [igFun by Fcore_sub & morphim_Fcore].
Canonical Structure Fcore_gFun := [gFun by morphim_Fcore].
Canonical Structure Fcore_pgFun := [pgFun by morphim_Fcore].

Section MoreFittingCore.

Variables (gT rT : finGroupType) (D : {group gT}) (f : {morphism D >-> rT}).
Implicit Types (M H : {group gT}) (R : {group rT}).

Lemma Fcore_char M : M`_\F \char M. Proof. exact: gFchar. Qed.

Lemma FcoreJ M x : (M :^ x)`_\F = M`_\F :^ x.
Proof.
rewrite -{1}(setTI M) -morphim_conj.
by rewrite -injmF ?injm_conj ?subsetT // morphim_conj setTI.
Qed.

Lemma injm_Fcore M : 'injm f -> M \subset D -> f @* M`_\F = (f @* M)`_\F.
Proof. by move=> injf sMD; rewrite injmF. Qed.

Lemma isom_Fcore M R : isom M R f -> M \subset D -> isom M`_\F R`_\F f.
Proof. by move=> isoMR sMD; apply: gFisom. Qed.

Lemma isog_Fcore M R : M \isog R -> M`_\F \isog R`_\F.
Proof. by move=> isoMR; apply: gFisog. Qed.

End MoreFittingCore.

Section Section15.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).
Implicit Types p q q_star r : nat.
Implicit Types x y z : gT.
Implicit Types A E H K L M Mstar N P Q Qstar R S T U V W X Y Z : {group gT}.

Lemma Fcore_sub_Msigma M : M \in 'M -> M`_\F \subset M`_\sigma.
Proof.
move=> maxM; rewrite gen_subG.
apply/bigcupsP=> P /andP[/SylowP[p _ sylP] nsPM]; have [sPM pP _] := and3P sylP.
have [-> | ntP] := eqsVneq P 1; first exact: sub1G.
rewrite (sub_Hall_pcore (Msigma_Hall maxM)) // (pi_pgroup pP) //.
by apply/exists_inP; exists P; rewrite ?(mmax_normal maxM).
Qed.

Lemma Fcore_eq_Msigma M :
  M \in 'M -> reflect (M`_\F = M`_\sigma) (nilpotent M`_\sigma).
Proof.
move=> maxM; apply: (iffP idP) => [nilMs | <-]; last exact: Fcore_nil.
apply/eqP; rewrite eqEsubset Fcore_sub_Msigma //.
by rewrite (Fcore_max (Msigma_Hall maxM)) ?pcore_normal.
Qed.

(* This is B & G, Lemma 15.1. *)
(* We have made all semidirect products explicits, and omitted the assertion  *)
(* M`_\sigma \subset M^`(1), which is exactly covered by Msigma_der1.         *)
(*   Some refactoring is definitely needed here, to avoid the mindless cut    *)
(* and paste of a large fragment of the proof of Lemma 12.12.                 *)
Lemma kappa_structure M U K (Ms := M`_\sigma) :
     M \in 'M -> kappa_complement M U K ->
  [/\ (*a*) [/\ (Ms ><| U) ><| K = M, cyclic K & abelian (M^`(1) /  Ms)],
      (*b*) K :!=: 1 -> Ms ><| U = M^`(1) /\ abelian U,
      (*c*) forall X, X \subset U -> X :!=: 1 -> 'C_Ms(X) != 1 ->
            [/\ 'M('C(X)) = [set M], cyclic X & \tau2(M).-group X],
      (*d*) abelian <<\bigcup_(x in Ms^#) 'C_U[x]>>
    & (*e*) U :!=: 1 -> exists U0,
            [/\ gval U0 \subset U, exponent (gval U0) = exponent U
             & [Frobenius Ms <*> U0 = Ms ><| U0]]].
Proof.
move=> maxM complU; have [hallU hallK _] := complU.
have [hallE defM _ regUK cUU] := kappa_compl_context maxM complU.
have [[_ E _ defE]] := sdprodP defM.
have [nsUE sKE mulUK nUK tiUK] := sdprod_context defE.
rewrite defE -{1 2}mulUK mulgA => defMl /mulGsubP[nMsU nMsK] tiMsE.
have [/andP[sMsM nMsM] [sUE nUE]] := (pcore_normal _ M : Ms <| M, andP nsUE).
rewrite norm_joinEr // mulUK in hallE.
have [[sEM s'M_E _] [sUM sk'U _]] := (and3P hallE, and3P hallU).
have defMsU: Ms ><| U = Ms <*> U.
  by apply: sdprodEY nMsU (trivgP _); rewrite -tiMsE -mulUK setIS ?mulG_subl.
have{defM} defM: Ms <*> U ><| K = M.
  rewrite sdprodE ?normsY  ?coprime_TIg //=; first by rewrite norm_joinEr.
  rewrite -(sdprod_card defMsU) coprime_mull andbC regular_norm_coprime //=.
  by rewrite (coprimegS sKE) ?(pnat_coprime (pcore_pgroup _ _)).
rewrite defMsU quotient_der //= -/Ms -{2}defMl -mulgA mulUK.
rewrite quotientMidl -quotient_der ?(subset_trans sEM) //.
rewrite quotient_abelian ?(der_mmax_compl_abelian maxM hallE) //.
set part_c := forall U, _; have c_holds: part_c.
  move=> X sXU ntX nregMsX; have sXE := subset_trans sXU sUE.
  have [x /setIP[Ms_x cXx] ntx] := trivgPn _ nregMsX.
  have Ms1x: x \in Ms^# by apply/setD1P.
  have piCx_hyp: {in X^#, forall x', x' \in ('C_M[x])^# /\ \sigma(M)^'.-elt x'}.
    move=> x' /setD1P[ntx' Xx']; have Ex' := subsetP sXE x' Xx'.
    rewrite 3!inE ntx' (subsetP sEM) ?(mem_p_elt s'M_E) //=.
    by rewrite (subsetP _ _ Xx') ?sub_cent1.   
  have piCx x' X1x' := (* GG -- ssreflect evar generalization fails in trunk *)
    let: conj c e := piCx_hyp x' X1x' in pi_of_cent_sigma maxM Ms1x c e.
  have t2X: \tau2(M).-group X.
    apply/pgroupP=> p p_pr /Cauchy[] // x' Xx' ox'.
    have X1x': x' \in X^# by rewrite !inE Xx' -order_gt1 ox' prime_gt1.
    have [[]|[]] := piCx _ X1x'; last by rewrite /p_elt ox' pnatE.
    case/idPn; have:= mem_p_elt (pgroupS sXU sk'U) Xx'.
    by rewrite /p_elt ox' !pnatE // => /norP[]. 
  suffices cycX: cyclic X.
    split=> //; have [x' defX] := cyclicP cycX.
    have X1x': x' \in X^# by rewrite !inE -cycle_eq1 -cycle_subG -defX ntX /=.
    have [[kX _]|[_ _]] := piCx _ X1x'; last by rewrite defX cent_cycle.
    rewrite -(setIid X) coprime_TIg ?eqxx // {2}defX in ntX.
    rewrite (pnat_coprime t2X (sub_pgroup _ kX)) // => p kp.
    by rewrite inE /= negb_and rank_kappa ?orbT.
  have [E2 hallE2 sXE2] := Hall_superset (sigma_compl_sol hallE) sXE t2X.
  rewrite abelian_rank1_cyclic; last first.
    exact: abelianS sXE2 (tau2_compl_abelian maxM hallE hallE2).
  have [p _ ->] := rank_witness X; rewrite leqNgt; apply: contra nregMsX => rpX.
  have t2p: p \in \tau2(M) by  rewrite (pnatPpi t2X) // -p_rank_gt0 ltnW.
  rewrite -(setIidPr (subset_trans sXE sEM)) in rpX.
  case/p_rank_geP: rpX => A; rewrite pnElemI -setIdE; case/setIdP=> Ep2A sAX.
  rewrite -subG1; have [_ _ <- _ _] := tau2_context maxM t2p Ep2A.
  by rewrite setIS ?centS.
have hallU_E: Hall E U := pHall_Hall (pHall_subl sUE sEM hallU).
have UtypeF := FTtypeF_complement maxM hallE hallU_E nsUE.
set k'U13 := ({in _, _}) in UtypeF.
have/UtypeF{UtypeF k'U13}UtypeF: k'U13.
  move=> x /setD1P[]; rewrite -order_gt1 -pi_pdiv.
  set p := pdiv _ => pi_x_p Ux t13x.
  apply: contraNeq (pnatPpi (mem_p_elt sk'U Ux) pi_x_p) => nreg_x.
  apply/orP; right; rewrite unlock /= inE /= (pnatPpi t13x) //=.
  have sxM: <[x]> \subset M by rewrite cycle_subG (subsetP sUM).
  move: pi_x_p; rewrite -p_rank_gt0 /= -(setIidPr sxM) => /p_rank_geP[P].
  rewrite pnElemI -setIdE => /setIdP[EpP sPx]; apply/exists_inP; exists P => //.
  by rewrite (subG1_contra _ nreg_x) //= -cent_cycle setIS ?centS.
have [K1 | ntK] := altP (K :=P: 1).
  rewrite {2}K1 cyclic1; rewrite K1 mulg1 in mulUK; rewrite -mulUK in hallE.
  have ltM'M := sol_der1_proper (mmax_sol maxM) (subxx _) (mmax_neq1 maxM).
  suffices /UtypeF[[A0 [_ abA0 genA0]] frobM]: U :!=: 1.
    by split => //; apply: abelianS abA0; rewrite gen_subG; apply/bigcupsP.
  apply: contraNneq (proper_subn ltM'M); rewrite -{1}defMl => ->.
  by rewrite K1 !mulg1 Msigma_der1.
have PmaxM: M \in 'M_'P by rewrite inE maxM -(trivg_kappa maxM hallK) andbT.
have [_ _ [_ _ _ [cycZ _ _ _ _] [_ _ _ defM']]] := Ptype_embedding PmaxM hallK.
have{cycZ cUU} [cycK cUU] := (cyclicS (joing_subl _ _) cycZ, cUU ntK).
split=> // [_||/UtypeF[] //]; first split=> //.
  apply/eqP; rewrite eq_sym eqEcard -(leq_pmul2r (cardG_gt0 K)).
  have [nsMsU_M _ mulMsU _ _] := sdprod_context defM.
  rewrite  (sdprod_card defM) (sdprod_card defM') der1_min ?normal_norm //=.
  by rewrite -(isog_abelian (sdprod_isog defM)) cyclic_abelian.
by apply: abelianS cUU; rewrite gen_subG -big_distrr subsetIl.
Qed.

(* This is B & G, Theorem 15.2. *)
(* It is this theorem that implies that the non-functorial definition of      *)
(* M`_\sigma used in B & G is equivalent to the original definition in FT     *)
(* (also used in Peterfalvi).                                                 *)
(*   Proof notes: this proof contained two non-structural arguments: taking D *)
(* to be K-invariant, and reusing the nilpotent Frobenius kernel argument for *)
(* Q1 (bottom of p. 118). We handled the first with a "without loss", but for *)
(* the second we had to spell out explicitly the assumptions and conclusions  *)
(* of the nilpotent kernel argument that were spread throughout the last      *)
(* paragraph p. 118.                                                          *)
(*  We also had to make a few additions to the argument at the top of p. 119; *)
(* while the statement of the Theorem states that F(M) = C_M(Qbar), the text  *)
(* only shows that F(M) = C_Msigma(Qbar), and we need to show that K acts     *)
(* regularly on Qbar to complete the proof; this follows from the values of   *)
(* orders of K,  Kstar and Qbar. In addition we need to show much earlier     *)
(* that K acts faithfully on Q, to show that C_M(Q) is included in Ms, and    *)
(* this requires a use of 14.2(e) not mentioned in the text; in addition, the *)
(* reference to coprime action (Proposition 1.5) on p. 119 l. 1 is somewhat   *)
(* misleading, since we actually need to use the coprime stabilizer Lemma 1.9 *)
(* to show that C_D(Qbar) = C_D(Q) = 1 (unless we splice in the proof of that *)
(* lemma).                                                                    *)
Theorem Fcore_structure M (Ms := M`_\sigma) :
  M \in 'M ->
    [/\ M`_\F != 1, M`_\F \subset Ms, Ms \subset M^`(1) & M^`(1) \proper M]
 /\ (forall K D : {group gT},
     \kappa(M).-Hall(M) K -> M`_\F != M`_\sigma ->
     let p := #|K| in let Ks := 'C_Ms(K) in
     let q := #|Ks| in let Q := 'O_q(M) in
     let Q0 := 'C_Q(D) in let Qbar := Q / Q0 in
     q^'.-Hall(M`_\sigma) D ->
    [/\ (*a*) [/\ M \in 'M_'P1, Ms ><| K = M & Ms = M ^`(1)],
        (*b*) [/\ prime p, prime q, q \in \pi(M`_\F) & q \in \beta(M)],
      [/\ (*c*) q.-Sylow(M) Q,
          (*d*) nilpotent D
        & (*e*) Q0 <| M],
        (*f*) [/\ minnormal Qbar (M / Q0), q.-abelem Qbar & #|Qbar| = (q ^ p)%N]
      & (*g*) [/\ Ms^`(1) = M^`(2),
                  M^`(2) \subset 'F(M),
                  [/\ Q <*> 'C_M(Q) = 'F(M),
                      'C_M(Qbar | 'Q) = 'F(M)
                    & 'C_Ms (Ks / Q0 | 'Q) = 'F(M)]
                & 'F(M) \proper Ms]]).
Proof.
move=> maxM; set M' := M^`(1); set M'' := M^`(2).
have nsMsM: Ms <| M := pcore_normal _ M; have [sMsM nMsM] := andP nsMsM.
have solM := mmax_sol maxM; have solMs: solvable Ms := solvableS sMsM solM.
have sMF_Ms: M`_\F \subset Ms := Fcore_sub_Msigma maxM.
have ltM'M: M' \proper M by rewrite (sol_der1_proper solM) ?mmax_neq1.
have sMsM': Ms \subset M' := Msigma_der1 maxM.
have [-> | ltMF_Ms] := eqVproper sMF_Ms; first by rewrite eqxx Msigma_neq1.
set KDpart := (X in _ /\ X); suffices KD_holds: KDpart.
  do 2!split=> //;  have [K hallK] := Hall_exists \kappa(M) solM.
  pose q := #|'C_(M`_\sigma)(K)|; have [D hallD] := Hall_exists q^' solMs.
  have [_ [_ _ piMFq _] _ _ _] := KD_holds K D hallK (proper_neq ltMF_Ms) hallD.
  by rewrite -rank_gt0 (leq_trans _ (p_rank_le_rank q _)) ?p_rank_gt0.
move=> {KDpart} K D hallK neMF_Ms p Ks q Q /= hallD.
have not_nilMs: ~~ nilpotent Ms by rewrite (sameP (Fcore_eq_Msigma maxM) eqP).
have P1maxM: M \in 'M_'P1; last have [PmaxM _] := setIdP P1maxM.
  apply: contraR not_nilMs => notP1maxM; apply: notP1type_Msigma_nil.
  by rewrite orbC inE notP1maxM inE maxM andbT orNb.
have ntK: K :!=: 1 by rewrite inE maxM andbT -(trivg_kappa maxM hallK) in PmaxM.
have [defMs defM]: Ms = M' /\ Ms ><| K = M.
  have [U complU] := ex_kappa_compl maxM hallK.
  have U1: U :=: 1 by apply/eqP; rewrite (trivg_kappa_compl maxM complU).
  have [[defM _ _] [//| defM' _] _ _ _] := kappa_structure maxM complU.
  by rewrite U1 sdprodg1 in defM defM'.
have [_ mulMsK nMsK _] := sdprodP defM; rewrite /= -/Ms in mulMsK nMsK.
have [sKM kK _] := and3P hallK; have s'K := sub_pgroup (@kappa_sigma' _ _) kK.
have coMsK: coprime #|Ms| #|K| := pnat_coprime (pcore_pgroup _ _) s'K.
have q_pr: prime q.
  have [L _ [_ _ _ _ [_]]] := Ptype_embedding PmaxM hallK.
  by rewrite inE P1maxM => [[] []].
have hallMs: \sigma(M).-Hall(M) Ms := Msigma_Hall maxM.
have sMq: q \in \sigma(M).
  by rewrite -pnatE // -pgroupE (pgroupS (subsetIl _ _) (pcore_pgroup _ _)).
have{s'K kK} q'K: q^'.-group K := pi'_p'group s'K sMq.
have nsQM: Q <| M := pcore_normal q M; have [sQM nQM] := andP nsQM.
have qQ: q.-group Q := pcore_pgroup _ _.
have sQMs: Q \subset Ms by rewrite (sub_Hall_pcore hallMs) ?(pi_pgroup qQ).
have [K1 prK1 sK1K]: exists2 K1, prime #|gval K1| & K1 \subset K.
  have:= ntK; rewrite -rank_gt0; have [r r_pr ->] := rank_witness K.
  by case/p_rank_geP=> K1 /pnElemPcard[? _ oK1]; exists K1; rewrite ?oK1.
have coMsK1 := coprimegS sK1K coMsK; have coQK1 := coprimeSg sQMs coMsK1.
have prMsK: semiprime Ms K by have [[? _ []] ] := Ptype_structure PmaxM hallK.
have defCMsK1: 'C_Ms(K1) = Ks.
  by rewrite (cent_semiprime prMsK) // -cardG_gt1 prime_gt1.
have sK1M := subset_trans sK1K sKM; have nQK1 := subset_trans sK1M nQM.
have{sMsM'} sKsQ: Ks \subset Q.
  have defMsK: [~: Ms, K] = Ms by case/coprime_der1_sdprod: defM.
  have hallQ := nilpotent_pcore_Hall q (Fitting_nil M).
  rewrite -[Q]p_core_Fitting (sub_Hall_pcore hallQ) //; first exact: pnat_id.
  apply: prime_meetG => //; apply: contraNneq not_nilMs => tiKsFM.
  suffices <-: 'F(Ms) = Ms by apply: Fitting_nil.
  apply/eqP; rewrite eqEsubset Fitting_sub /= -{1}defMsK.
  rewrite (odd_sdprod_primact_commg_sub_Fitting defM) ?mFT_odd //.
  apply/trivgP; rewrite -tiKsFM setIAC setSI //= -/Ms subsetI Fitting_sub /=.
  by rewrite Fitting_max ?Fitting_nil // (char_normal_trans (Fitting_char _)).
have nilMs_Q: nilpotent (Ms / Q).
  have [nMsK1 tiQK1] := (subset_trans sK1K nMsK, coprime_TIg coQK1).
  have prK1b: prime #|K1 / Q| by rewrite -(card_isog (quotient_isog _ _)).
  have defMsK1: (Ms / Q) ><| (K1 / Q) = (Ms / Q) <*> (K1 / Q).
    by rewrite sdprodEY ?quotient_norms // coprime_TIg ?coprime_morph.
  apply: (prime_Frobenius_sol_kernel_nil defMsK1) => //.
    by rewrite (solvableS _ (quotient_sol _ solM)) ?join_subG ?quotientS.
  by rewrite -coprime_quotient_cent ?quotientS1 /= ?defCMsK1.
have defQ: 'O_q(Ms) = Q by rewrite -(setIidPl sQMs) pcore_setI_normal.
have sylQ: q.-Sylow(Ms) Q.
  have nsQMs: Q <| Ms by rewrite -defQ pcore_normal.
  rewrite -(pquotient_pHall qQ) // /= -/Q -{3}defQ.
  by rewrite -(pquotient_pcore _ qQ) ?nilpotent_pcore_Hall.
have{sMq hallMs} sylQ_M := subHall_Sylow hallMs sMq sylQ.
have sQ_MF: Q \subset M`_\F.
  by rewrite sub_gen ?(bigcup_max [group of Q]) ?(p_Sylow sylQ_M) ?pcore_normal.
have{sQ_MF} piMFq: q \in \pi(M`_\F).
  by rewrite (piSg sQ_MF) // (piSg sKsQ) // pi_of_prime ?inE /=.
without loss nDK: D hallD / K \subset 'N(D).
  have [E hallE nEK] := coprime_Hall_exists q^' nMsK coMsK solMs.
  have [x Ms_x ->] := Hall_trans solMs hallD hallE.
  set Q0 := 'C__(_)%G; rewrite -(isog_nil (conj_isog _ _)) -['C_Q(_)]/(gval Q0).
  move/(_ E hallE nEK)=> IH; suffices ->: Q0 = [group of 'C_Q(E)] by [].
  apply: group_inj => /=; have Mx: x \in M := subsetP (pcore_sub _ _) x Ms_x.
  rewrite /= -/Q -{1}(normsP nQM x Mx) centJ -conjIg (normsP _ x Mx) //.
  by case: IH => _ _ [_ _]; case/andP.
set Q0 := 'C_Q(D); set Qb := Q / Q0.
have defQD: Q ><| D = Ms by rewrite -defQ in sylQ *; apply/sdprod_Hall_pcoreP.
have [_ mulQD nQD tiQD] := sdprodP defQD; rewrite /= -/Q -/Ms in mulQD nQD tiQD.
have nilD: nilpotent D.
  by rewrite (isog_nil (quotient_isog nQD tiQD)) /= -quotientMidl mulQD.
have [sDMs q'D _] := and3P hallD; have sDM := subset_trans sDMs sMsM.
have sDKM: D <*> K \subset M by rewrite join_subG sDM.
have q'DK: q^'.-group (D <*> K) by rewrite norm_joinEr // pgroupM q'D.
have{K1 sK1M sK1K coMsK1 coQK1 prK1 defCMsK1 nQK1 solMs} Qi_rec Qi:
    Qi \in |/|_Q(D <*> K; q) -> Q0 \subset Qi -> Qi \proper Q ->
  exists L, [/\ L \in |/|_Q(D <*> K; q), Qi <| L, minnormal (L / Qi) (M / Qi)
               & ~~ ((Ks \subset L) ==> (Ks \subset Qi))].
- case/setIdP=> /andP[sQiQ qQi] nQiDK sQ0i ltQiQ.
  have ltQiN := nilpotent_proper_norm (pgroup_nil qQ) ltQiQ.
  have [Lb minLb sLbQ]: {Lb | minnormal (gval Lb) (M / Qi) & Lb \subset Q / Qi}.
    apply: mingroup_exists; rewrite quotient_norms //= andbT -quotientInorm.
    by rewrite -subG1 quotient_sub1 ?subsetIr // proper_subn.
  have [ntLb nLbM] := andP (mingroupp minLb).
  have nsQiN: Qi <| 'N_M(Qi) by rewrite normal_subnorm (subset_trans sQiQ).
  have: Lb <| 'N_M(Qi) / Qi.
    by rewrite quotientInorm /normal (subset_trans sLbQ) ?quotientS.
  case/(inv_quotientN nsQiN) => L defLb sQij /=; case/andP.
  case/subsetIP=> sLM nQij nLN; exists L.
  have{sLbQ} sLQ: L \subset Q by rewrite -(quotientSGK nQij sQiQ) -defLb.
  rewrite inE /psubgroup /normal sLQ sQij nQij (pgroupS sLQ qQ) -defLb.
  have nLDK: D <*> K \subset 'N(L) by apply: subset_trans nLN; exact/subsetIP.
  have sLD_Ms: L <*> D \subset Ms by rewrite join_subG (subset_trans sLQ).
  have coLD_K1: coprime #|L <*> D| #|K1| := coprimeSg sLD_Ms coMsK1.
  have [[nQiD nQiK] [nLD nLK]] := (joing_subP nQiDK, joing_subP nLDK).
  have [nQiK1 nLK1] := (subset_trans sK1K nQiK, subset_trans sK1K nLK).
  split=> //; apply: contra ntLb => regLK.
  have [sLLD sDLD] := joing_subP (subxx (L <*> D)).
  suffices nilLDbar: nilpotent (L <*> D / Qi).
    rewrite defLb -subG1 -(quotientS1 sQ0i) /= -/Q.
    rewrite coprime_quotient_cent ?(pgroup_sol qQ) ?(pnat_coprime qQ) //=.
    rewrite subsetI quotientS //= (sub_nilpotent_cent2 nilLDbar) ?quotientS //.
    by rewrite coprime_morph ?(p'nat_coprime q'D (pgroupS sLQ qQ)).
  have defLK1b: (L <*> D / Qi) ><| (K1 / Qi) = (L <*> D / Qi) <*> (K1 / Qi).
    rewrite sdprodEY ?coprime_TIg ?quotient_norms //=.
      by rewrite (subset_trans sK1K) // normsY.
    by rewrite coprime_morph // (coprimeSg sLD_Ms).
  have [sQiLD sLD_M] := (subset_trans sQij sLLD, subset_trans sLD_Ms sMsM).
  have{regLK}: 'C_(L <*> D / Qi)(K1 / Qi) = 1.
    rewrite -coprime_quotient_cent ?(subset_trans sK1K) ?(solvableS sLD_M) //=.
    rewrite -(setIidPr sLD_Ms) setIAC defCMsK1 quotientS1 //= -/Ks joingC.
    rewrite norm_joinEl // -(setIidPl sKsQ) -setIA -group_modr // tiQD mul1g.
    have [-> | ntLKs] := eqVneq (Ks :&: L) 1; first exact: sub1G.
    by rewrite subIset ?(implyP regLK) // prime_meetG. 
  apply: (prime_Frobenius_sol_kernel_nil defLK1b).
    by apply: solvableS (quotient_sol _ solM); rewrite join_subG !quotientS.
  by rewrite -(card_isog (quotient_isog _ _)) ?coprime_TIg // (coprimeSg sQiQ).
have ltQ0Q: Q0 \proper Q.
  rewrite properEneq subsetIl andbT; apply: contraNneq not_nilMs => defQ0.
  rewrite -dprodEsd // in defQD; last by rewrite centsC -defQ0 subsetIr.
  by rewrite (dprod_nil defQD) (pgroup_nil qQ).
have [nQK coQK] := (subset_trans sKM nQM, pnat_coprime qQ q'K).
have solQ := pgroup_sol qQ. (* must come late: Coq diverges on solQ <> solMs *)
have [coDK coQD] := (coprimeSg sDMs coMsK, pnat_coprime qQ q'D).
have nQ0K: K \subset 'N(Q0) by rewrite normsI ?norms_cent.
have nQ0D: D \subset 'N(Q0) by rewrite cents_norm // centsC subsetIr.
have nQ0DK: D <*> K \subset 'N(Q0) by apply/joing_subP.
have [|Q1 [DKinvQ1 nsQ01 minQ1b nregQ1b]] := Qi_rec _ _ (subxx _) ltQ0Q.
  by rewrite inE /psubgroup (pgroupS _ qQ) ?subsetIl.
have{Qi_rec nregQ1b DKinvQ1} [tiQ0Ks defQ1]: Q0 :&: Ks = 1 /\ Q1 :=: Q.
  move: nregQ1b; rewrite negb_imply; case/andP=> sKsQ1 not_sKsQ0.
  split=> //; first by rewrite setIC prime_TIg.
  have [] := setIdP DKinvQ1; case/andP; case/eqVproper=> // ltQ1Q _ _.
  have [Q2 [_ _ _]] := Qi_rec Q1 DKinvQ1 (normal_sub nsQ01) ltQ1Q.
  by rewrite sKsQ1 implybT.
have [nsQ0Q minQb]: Q0 <| Q /\ minnormal Qb (M / Q0) by rewrite /Qb -defQ1.
have{Q1 defQ1 minQ1b nsQ01} abelQb: q.-abelem Qb.
  have qQb: q.-group Qb := quotient_pgroup _ qQ; have solQb := pgroup_sol qQb.
  by rewrite -is_abelem_pgroup // (minnormal_solvable_abelem minQb).
have [cQbQb [sQ0Q nQ0Q]] := (abelem_abelian abelQb, andP nsQ0Q).
have nQ0M: M \subset 'N(Q0) by rewrite -mulMsK -mulQD -mulgA !mul_subG.
have nsQ0M: Q0 <| M by rewrite /normal subIset ?sQM.
have sFM_QCQ: 'F(M) \subset Q <*> 'C_M(Q).
  have [_ /= mulQQ' cQQ' _] := dprodP (nilpotent_pcoreC q (Fitting_nil M)).
  rewrite -{3}mulQQ' p_core_Fitting cent_joinEr ?subsetIr //= -/Q in cQQ' *.
  by rewrite mulgS // subsetI (subset_trans (pcore_sub _ _) (Fitting_sub M)).
have sQCQ_CMsQb: Q <*> 'C_M(Q) \subset 'C_Ms(Qb | 'Q).
  rewrite join_subG !(subsetI _ Ms) sQMs /= !sub_astabQ nQ0Q /= -/Q0 -/Qb.
  rewrite -abelianE cQbQb quotient_cents ?subsetIr //= andbC subIset ?nQ0M //=.
  rewrite -(coprime_mulG_setI_norm mulMsK) ?norms_cent //= -/Ms.
  suffices ->: 'C_K(Q) = 1 by rewrite mulg1 subsetIl.
  have: ~~ (Q \subset Ks); last apply: contraNeq => ntCKQ.
    have [_ _ _ [_]] := Ptype_structure PmaxM hallK.
    by move/(_ q); rewrite pi_of_prime //; case/(_ (eqxx q) _ sylQ_M).
  rewrite -[Ks](cent_semiprime prMsK _ ntCKQ) ?subsetIl //.
  by rewrite subsetI sQMs centsC subsetIr.
have nCQb: M \subset 'N('C(Qb | 'Q)).
  by rewrite (subset_trans _ (astab_norm _ _)) ?actsQ.
have defFM: 'C_Ms(Qb | 'Q) = 'F(M).
  apply/eqP; rewrite eqEsubset andbC (subset_trans sFM_QCQ) //=.
  rewrite Fitting_max //=; first by rewrite /normal subIset ?sMsM //= normsI.
  rewrite -(coprime_mulG_setI_norm mulQD) ?(subset_trans sMsM) //= -/Q.
  rewrite mulg_nil ?(nilpotentS (subsetIl _ _)) ?(pgroup_nil qQ) //= -/Q.
  rewrite (centsS (subsetIl _ _)) //= -/Q.
  have cDQ0: 'C_D(Qb | 'Q) \subset 'C(Q0) by rewrite subIset // centsC subsetIr.
  rewrite (stable_factor_cent cDQ0) ?(coprimegS (subsetIl _ _) coQD) //.
  by rewrite /stable_factor commGC -sub_astabQR ?subsetIr // subIset ?nQ0D.
have{sFM_QCQ sQCQ_CMsQb} ->: Q <*> 'C_M(Q) = 'F(M).
  by apply/eqP; rewrite eqEsubset sFM_QCQ andbT -defFM.
have ltFM_Ms: 'F(M) \proper Ms.
  rewrite properEneq -{2}defFM subsetIl andbT.
  by apply: contraNneq not_nilMs => <-; apply: Fitting_nil.
have sQFM: Q \subset 'F(M) by rewrite -[Q]p_core_Fitting pcore_sub.
have not_cDQb: ~~ (D / Q0 \subset 'C(Qb)).
  apply: contra (proper_subn ltFM_Ms) => cDQb; rewrite -mulQD mulG_subG sQFM /=.
  by rewrite -defFM subsetI sDMs sub_astabQ nQ0D.
have [_ minQbP] := mingroupP minQb.
have regQbDb: 'C_Qb(D / Q0) = 1.
  apply: contraNeq not_cDQb => ntCQDb; rewrite centsC; apply/setIidPl.
  apply: minQbP (subsetIl _ _); rewrite ntCQDb /= -/Qb -(setIidPl cQbQb) -setIA.
  by rewrite -centM -quotientMl //= mulQD normsI ?norms_cent ?quotient_norms.
have tiQ0 R: q^'.-group R -> Q0 :&: R = 1.
  by move/(pnat_coprime (pgroupS sQ0Q qQ))/coprime_TIg.
have oKb: #|K / Q0| = p by rewrite -(card_isog (quotient_isog _ (tiQ0 _ _))).
have oKsb: #|Ks / Q0| = q.
  by rewrite -(card_isog (quotient_isog _ tiQ0Ks)) ?(subset_trans sKsQ).
have regDK: 'C_D(K) = 1.
  by rewrite -(setIidPl sDMs) -setIA setIC coprime_TIg ?(coprimeSg sKsQ).
have{tiQ0} frobDKb: [Frobenius D <*> K / Q0 = (D / Q0) ><| (K / Q0)].
  have ntDb: D / Q0 != 1 by apply: contraNneq not_cDQb => ->; apply: sub1G.
  have ntKb: K / Q0 != 1 by rewrite -(isog_eq1 (quotient_isog _ (tiQ0 _ _))).
  apply/Frobenius_semiregularP => // [|xb].
    by apply: quotient_coprime_sdprod; rewrite ?sdprodEY ?coprime_TIg.
  have [f [_ ker_f _ im_f]] := restrmP (coset_morphism Q0) nQ0DK.
  have{ker_f} inj_f: 'injm f by rewrite ker_f ker_coset setIC tiQ0.
  rewrite /= /quotient -!im_f ?joing_subl ?joing_subr //.
  rewrite 2!inE andbC => /andP[/morphimP[x DKx Kx ->{xb}]].
  rewrite morph_injm_eq1 // -injm_subcent1 ?joing_subl // => ntx.
  rewrite -{3}(setIidPl sDMs) -setIA prMsK ?inE ?ntx //.
  by rewrite setICA regDK setIg1 morphim1.
have defKsb: 'C_Qb(K / Q0) = Ks / Q0.
  rewrite /Ks -mulQD coprime_cent_mulG // regDK mulg1.
  by rewrite coprime_quotient_cent ?subsetIl.
have{frobDKb regQbDb} [p_pr oQb cQbD']:
  [/\ prime p, #|Qb| = (q ^ p)%N & (D / Q0)^`(1) \subset 'C(Qb)].
- have ntQb: Qb != 1 by rewrite -subG1 quotient_sub1 ?proper_subn.
  have prQbK: semiprime Qb (K / Q0).
    move=> xb; rewrite 2!inE andbC; case/andP; case/morphimP=> x nQ0x Kx -> ntx.
    have{ntx} ntx: x != 1 by apply: contraNneq ntx => ->; rewrite morph1.
    transitivity ('C_Q[x] / Q0); last first.
      rewrite -(coprime_quotient_cent (subsetIl Q _) nQ0K coQK solQ) /= -/Q0.
      by rewrite -/Q -(setIidPl sQMs) -!setIA prMsK // !inE ntx.
    rewrite -!cent_cycle -quotient_cycle //; rewrite -!cycle_subG in Kx nQ0x.  
    by rewrite coprime_quotient_cent ?(coprimegS Kx).
  have:= Frobenius_primact frobDKb _ _ _ ntQb _ prQbK regQbDb.
  have [nQDK solDK] := (subset_trans sDKM nQM, solvableS sDKM solM).
  rewrite !quotient_sol ?quotient_norms // coprime_morph ?(pnat_coprime qQ) //=.
  rewrite -/Qb oKb defKsb prime_cyclic oKsb // subsetI der_sub /=.
  by case=> //= -> -> ->.
have{cQbD'} sM''FM: M'' \subset 'F(M).
  have nQMs := subset_trans sMsM nQM.
  rewrite [M'']dergSn -/M' -defMs -(quotientSGK _ sQFM) ?comm_subG //.
  rewrite (quotient_der 1) //= -/Ms -mulQD quotientMidl -quotient_der //= -/Q.
  by rewrite quotientS // -defFM subsetI sub_astabQ !comm_subG ?quotient_der. 
have sQ0Ms := subset_trans sQ0Q sQMs.
have ->: 'C_Ms(Ks / Q0 | 'Q) = 'F(M).
  have sFMcKsb: 'F(M) \subset 'C_Ms(Ks / Q0 | 'Q).
    by rewrite -defFM setIS ?astabS ?quotientS.
  have nCMsKsbM: M \subset 'N('C_Ms(Ks / Q0 | 'Q)).
    rewrite -{1}mulMsK mulG_subG sub_der1_norm ?subsetIl //= -/Ms; last first.
      by rewrite {1}defMs (subset_trans sM''FM sFMcKsb).
    rewrite normsI // (subset_trans _ (astab_norm _ _)) ?actsQ //.
    by rewrite cents_norm // centsC subsetIr.
  apply/eqP; rewrite eqEsubset sFMcKsb -defFM subsetI subsetIl.
  rewrite sub_astabQ /= -/Q0 subIset ?(subset_trans sMsM) //= andbT centsC.
  apply/setIidPl; apply: minQbP (subsetIl _ _).
  rewrite andbC normsI ?norms_cent ?quotient_norms //= -/Qb.
  have: Ks / Q0 != 1 by rewrite -cardG_gt1 oKsb prime_gt1.
  apply: subG1_contra; rewrite (quotientGI _ sQ0Ms) quotient_astabQ /= -/Q0.
  by rewrite subsetI quotientS // centsC subsetIr.
have ->: 'C_M(Qb | 'Q) = 'F(M).
  apply/eqP; rewrite eqEsubset -{2}defFM setSI //= andbT.
  rewrite -(coprime_mulG_setI_norm mulMsK) //= -defFM mulG_subG subxx /=.
  rewrite subsetI subsetIr -(quotientSGK _ sQ0Ms) 1?subIset ?nQ0K //= -/Q0.
  rewrite quotientIG; last by rewrite sub_astabQ normG trivg_quotient sub1G.
  rewrite quotient_astabQ /= -/Q0 prime_TIg ?sub1G ?oKb //.
  rewrite centsC -subsetIidl defKsb; apply: contra (@subset_leq_card _ _ _)  _.
  by rewrite -ltnNge oQb oKsb (ltn_exp2l 1) prime_gt1.
suffices ->: q \in \beta(M) by do 2!split=> //; last rewrite {1}defMs.
apply: contraR not_cDQb; rewrite negb_forall_in; case/exists_inP=> Q1 sylQ1.
rewrite negbK {Q1 sylQ1}(eq_Hall_pcore sylQ_M sylQ1) -/Q => nnQ.
have sD_DK': D \subset (D <*> K)^`(1).
  rewrite -{1}(coprime_cent_prod nDK) ?nilpotent_sol // regDK mulg1.
  by rewrite commgSS ?joing_subl ?joing_subr.
rewrite quotient_cents // (subset_trans sD_DK') //.
have nQDK := subset_trans sDKM nQM; have nCQDK := norms_cent nQDK.
rewrite der1_min // -(isog_abelian (second_isog nCQDK)) setIC /=.
rewrite -ker_conj_aut (isog_abelian (first_isog_loc _ _)) //=; set A := _ @* _.
have norm_q := normal_norm (pcore_normal q _).
rewrite {norm_q}(isog_abelian (quotient_isog (norm_q _ _) _)) /=; last first.
  by rewrite coprime_TIg ?coprime_morphr //= (pnat_coprime (pcore_pgroup q _)).
have AutA: A \subset [Aut Q] := Aut_conj_aut _ _.
have [|//] := Aut_narrow qQ (mFT_odd _) nnQ _ AutA (morphim_odd _ (mFT_odd _)).
exact: morphim_sol (solvableS sDKM solM).
Qed.

(* This is B & G, Corollary 15.3(a). *)
Corollary cent_Hall_sigma_sdprod M H pi :
    M \in 'M -> pi.-Hall(M`_\sigma) H -> H :!=: 1 ->
  exists X, [/\  gval X \subset M, cyclic X, \tau2(M).-group X
              & 'C_(M`_\sigma)(H) ><| X = 'C_M(H)].
Proof.
move=> maxM hallH ntH; have hallMs := Msigma_Hall maxM.
have nsMsM: M`_\sigma <| M := pcore_normal _ M; have [sMsM nMsM] := andP nsMsM.
have sMs := pHall_pgroup hallMs; have [sHMs piH _] := and3P hallH.
have k'CH: \kappa(M)^'.-group 'C_M(H).
  apply/idPn; rewrite negb_and cardG_gt0 all_predC negbK => /hasP[p piCHp kMp].
  have PmaxM: M \in 'M_'P by apply/PtypeP; split; last exists p.
  have [X]: exists X, X \in 'E_p^1('C_M(H)).
    by apply/p_rank_geP; rewrite p_rank_gt0.
  case/pnElemP; case/subsetIP=> sXM cHX abelX dimX; have [pX _] := andP abelX.
  have [K hallK sXK] := Hall_superset (mmax_sol maxM) sXM (pi_pgroup pX kMp).
  have E1X: X \in 'E^1(K) by apply/nElemP; exists p; apply/pnElemP.
  have [q q_pr rqH] := rank_witness H; have [S sylS] := Sylow_exists q H.
  have piSq: q \in \pi(S).
    by rewrite -p_rank_gt0 (p_rank_Sylow sylS) -rqH rank_gt0.
  have [_ [defNK defNX] _ [_ not_sylCP _] _] := Ptype_structure PmaxM hallK.
  have{defNX} [defNX _] := defNX X E1X.
  have [[_ nsKs] [_ mulKKs _ _]] := (dprod_normal2 defNK, dprodP defNK).
  have s'K := sub_pgroup (@kappa_sigma' _ _) (pHall_pgroup hallK).
  have [_ hallKs] := coprime_mulGp_Hall mulKKs s'K (pgroupS (subsetIl _ _) sMs).
  have [sSH _] := andP sylS.
  have sylS_Ms := subHall_Sylow hallH (pnatPpi piH (piSg sSH piSq)) sylS.
  have [sSMs _] := andP sylS_Ms; have sS := pgroupS sSMs sMs.
  have sylS_M := subHall_Sylow hallMs (pnatPpi sS piSq) sylS_Ms.
  have sSKs: S \subset 'C_(M`_\sigma)(K).
    rewrite (sub_normal_Hall hallKs) //= -defNX subsetI (pHall_sub sylS_M) /=.
    by rewrite cents_norm // centsC (centsS sSH).
  by have [_ /negP] := not_sylCP q (piSg sSKs piSq) S sylS_M.
have solCH := solvableS (subsetIl M 'C(H)) (mmax_sol maxM).
have [X hallX] := Hall_exists \sigma(M)^' solCH; exists X.
have nsCsH: 'C_(M`_\sigma)(H) <| 'C_M(H) by rewrite /normal setSI // normsIG.
have hallCs: \sigma(M).-Hall('C_M(H)) 'C_(M`_\sigma)(H).
  by rewrite -(setIidPl sMsM) -setIA (setI_normal_Hall nsMsM) ?subsetIl.
rewrite (sdprod_normal_p'HallP nsCsH hallX hallCs).
have [-> | ntX] := eqsVneq X 1; first by rewrite sub1G cyclic1 pgroup1.
have [sXCH s'X _] := and3P hallX; have [sXM cHX] := subsetIP sXCH.
have sk'X: \sigma_kappa(M)^'.-group X.
  apply/pgroupP=> p p_pr p_dv_X; apply/norP=> /=.
  by split; [apply: (pgroupP s'X) | apply: (pgroupP (pgroupS sXCH k'CH))].
have [K hallK] := Hall_exists \kappa(M) (mmax_sol maxM).
have [U complU] := ex_kappa_compl maxM hallK; have [hallU _ _] := complU.
have [a Ma sXaU] := Hall_Jsub (mmax_sol maxM) hallU sXM sk'X.
have [_ _ cycX _ _] := kappa_structure maxM complU.
rewrite -(cyclicJ _ a) -(pgroupJ _ _ a); have [||//] := cycX _ sXaU.
  by rewrite -(isog_eq1 (conj_isog X a)).
rewrite -(normsP nMsM a Ma) centJ -conjIg -(isog_eq1 (conj_isog _ a)).
by rewrite (subG1_contra _ ntH) // subsetI sHMs centsC.
Qed.

(* This is B & G, Corollary 15.3(b). *)
Corollary sigma_Hall_tame M H pi x a :
    M \in 'M -> pi.-Hall(M`_\sigma) H -> x \in H -> x ^ a \in H ->
  exists2 b, b \in 'N_M(H) & x ^ a = x ^ b.
Proof.
move=> maxM hallH Hx Hxa; have [sHMs piH _] := and3P hallH.
have SMxM: M \in 'M_\sigma[x] by rewrite inE maxM cycle_subG (subsetP sHMs).
have SMxMa: (M :^ a^-1)%G \in 'M_\sigma[x].
  by rewrite inE mmaxJ maxM cycle_subG /= MsigmaJ mem_conjgV (subsetP sHMs).
have [-> | ntx] := eqVneq x 1; first by exists 1; rewrite ?group1 ?conj1g.
have ell1x: \ell_\sigma(x) == 1%N.
  by apply/ell_sigma1P; split=> //; apply/set0Pn; exists M.
have ntH: H :!=: 1 by apply/trivgPn; exists x.
have [[transR _ _ _] _] := FT_signalizer_context ell1x.
have [c Rc defMc] := atransP2 transR SMxM SMxMa.
pose b := c * a; have def_xa: x ^ a = x ^ b.
  by have [_ cxc] := setIP Rc; rewrite conjgM {3}/conjg -(cent1P cxc) mulKg.
have Mb: b \in M.
  by rewrite -(norm_mmax maxM) inE conjsgM -(congr_group defMc) actKV.
have nsMsM: M`_\sigma <| M := pcore_normal _ _; have [sMsM _] := andP nsMsM.
have [nsHM | not_nsHM] := boolP (H <| M).
  by exists b; rewrite // (mmax_normal maxM) ?setIid.
have neqMFs: M`_\F != M`_\sigma.
  apply: contraNneq not_nsHM => eq_MF_Ms.
  have nilMs: nilpotent M`_\sigma by apply/Fcore_eq_Msigma.
  rewrite (eq_Hall_pcore (nilpotent_pcore_Hall _ nilMs) hallH).
  exact: char_normal_trans (pcore_char _ _) nsMsM.
have [K hallK] := Hall_exists \kappa(M) (mmax_sol maxM).
pose q := #|'C_(M`_\sigma)(K)|.
have [D hallD] := Hall_exists q^' (solvableS sMsM (mmax_sol maxM)).
have [[_ sMFs _ _]] := Fcore_structure maxM; case/(_ K D) => //; rewrite -/q.
set Q := 'O_q(M) => _ [_ q_pr piMFq _] [sylQ nilD _] _ _.
have sQMs: Q \subset M`_\sigma.
  by apply: subset_trans sMFs; rewrite -[Q](p_core_Fcore piMFq) pcore_sub.
have sylQ_Ms: q.-Hall(M`_\sigma) Q := pHall_subl sQMs sMsM sylQ.
have nsQM: Q <| M := pcore_normal q M; have [_ qQ _] := and3P sylQ.
have nsQ_Ms: Q <| M`_\sigma := normalS sQMs sMsM nsQM.
have defMs: Q ><| D = M`_\sigma := sdprod_normal_p'HallP nsQ_Ms hallD sylQ_Ms.
have [_ mulQD nQD tiQD] := sdprodP defMs; rewrite -/Q in mulQD nQD tiQD.
have nQH := subset_trans sHMs (normal_norm nsQ_Ms).
have nsQHM: Q <*> H <| M.
  rewrite -(quotientGK nsQM) -quotientYK // cosetpre_normal //= -/Q.
  have nilMsQ: nilpotent (M`_\sigma / Q).
    by rewrite -mulQD quotientMidl -(isog_nil (quotient_isog _ _)).
  have hallMsQpi := nilpotent_pcore_Hall pi nilMsQ.
  rewrite (eq_Hall_pcore hallMsQpi (quotient_pHall nQH hallH)).
  by rewrite (char_normal_trans (pcore_char _ _)) ?quotient_normal.
have tiQH: Q :&: H = 1.
  apply: coprime_TIg (p'nat_coprime (pi_pgroup qQ _) piH).
  apply: contra not_nsHM => pi_q; rewrite (joing_idPr _) // in nsQHM.
  by rewrite (normal_sub_max_pgroup (Hall_max hallH)) ?(pi_pgroup qQ).
have defM: Q * 'N_M(H) = M.
  have hallH_QH: pi.-Hall(Q <*> H) H.
    by rewrite (pHall_subl (joing_subr _ _) _ hallH) // join_subG sQMs.
  have solQH := solvableS (normal_sub nsQHM) (mmax_sol maxM).
  rewrite -{2}(Hall_Frattini_arg solQH nsQHM hallH_QH) /= norm_joinEr //.
  by rewrite -mulgA [H * _]mulSGid // subsetI (subset_trans sHMs sMsM) normG.
move: Mb; rewrite -{1}defM; case/mulsgP=> z n Qz Nn defb; exists n => //.
rewrite def_xa defb conjgM [x ^ z](conjg_fixP _) // -in_set1 -set1gE -tiQH.
rewrite inE {1}commgEr groupMr // -mem_conjgV groupV /=.
rewrite (normsP (normal_norm nsQM)) ?Qz; last first.
  by rewrite groupV (subsetP sMsM) // (subsetP sHMs).
rewrite commgEl groupMl ?groupV //= -(conjsgK n H) mem_conjgV -conjgM -defb.
by have [_ nHn] := setIP Nn; rewrite (normP nHn) -def_xa.
Qed.

(* This is B & G, Corollary 15.4. *)
(* This result does not appear to be needed for the actual proof. *)
Corollary nilpotent_Hall_sigma H :
  nilpotent H -> Hall G H -> exists2 M, M \in 'M & H \subset M`_\sigma.
Proof.
move=> nilH /Hall_pi/=hallH; have [_ piH _] := and3P hallH.
have [-> | ntH] := eqsVneq H 1.
  by have [M maxM] := any_mmax gT; exists M; rewrite ?sub1G.
pose p := pdiv #|H|; have piHp: p \in \pi(H) by rewrite pi_pdiv cardG_gt1.
pose S := 'O_p(H)%G; have sylS: p.-Sylow(H) S := nilpotent_pcore_Hall p nilH.
have [sSH pS _] := and3P sylS.
have ntS: S :!=: 1 by rewrite -rank_gt0 (rank_Sylow sylS) p_rank_gt0.
have [M maxNM] := mmax_exists (mFT_norm_proper ntS (mFT_pgroup_proper pS)).
have [maxM sNM] := setIdP maxNM; exists M => //.
have sSM: S \subset M := subset_trans (normG _) sNM.
have sylS_G := subHall_Sylow hallH (pnatPpi piH piHp) sylS.
have sylS_M := pHall_subl sSM (subsetT M) sylS_G.
have sMp: p \in \sigma(M) by apply/exists_inP; exists S.
have sSMs: S \subset M`_\sigma.
  by rewrite (sub_Hall_pcore (Msigma_Hall maxM)) ?(pi_pgroup pS).
rewrite -(nilpotent_Fitting nilH) FittingEgen gen_subG.
apply/bigcupsP=> [[q /= _] piHq]; have [-> // | p'q] := eqVneq q p.
have sylS_Ms := pHall_subl sSMs (pcore_sub _ _) sylS_M.
have [X [_ cycX t2X defCS]] := cent_Hall_sigma_sdprod maxM sylS_Ms ntS.
have{defCS} [nCMsCS _ defCS _ _] := sdprod_context defCS.
have t2'CMs: \tau2(M)^'.-group 'C_(M`_\sigma)(S).
  apply: pgroupS (subsetIl _ _) (sub_pgroup _ (pcore_pgroup _ _)) => r.
  by apply: contraL => /andP[].
have [hallCMs hallX] := coprime_mulGp_Hall defCS t2'CMs t2X.
have sHqCS: 'O_q(H) \subset 'C_M(S).
  rewrite (setIidPr (subset_trans (cent_sub _) sNM)).
  rewrite (sub_nilpotent_cent2 nilH) ?pcore_sub //.
  exact: pnat_coprime pS (pi_pgroup (pcore_pgroup _ _) _).
have [t2q | t2'q] := boolP (q \in \tau2(M)); last first.
  apply: subset_trans (subsetIl _ 'C(S)).
  by rewrite (sub_normal_Hall hallCMs) // (pi_pgroup (pcore_pgroup _ _)).
have sylHq := nilpotent_pcore_Hall q nilH.
have sylHq_G := subHall_Sylow hallH (pnatPpi piH piHq) sylHq.
have sylHq_CS := pHall_subl sHqCS (subsetT _) sylHq_G.
have [Q sylQ] := Sylow_exists q X; have [sQX _] := andP sylQ.
have sylQ_CS := subHall_Sylow hallX t2q sylQ.
case/andP: t2q => _.
rewrite eqn_leq andbC ltnNge (leq_trans (p_rankS q (subsetT _))) //.
rewrite -(rank_Sylow sylHq_G) (rank_Sylow sylHq_CS) -(rank_Sylow sylQ_CS).
by rewrite (leq_trans (rankS sQX)) // -abelian_rank1_cyclic ?cyclic_abelian.
Qed.
  
(* This is B & G, Corollary 15.5. *)
(* We have changed the condition K != 1 to the equivalent M \in 'M_'P, as     *)
(* avoids a spurrious quantification on K.                                    *)
(* The text is quite misleading here, since Corollary 15.3(a) is needed for   *)
(* bith the nilpotent and the non-nilpotent case -- indeed, it is not really  *)
(* needed in the non-nilpotent case!                                          *)
Corollary Fitting_structure M (H := M`_\F) (Y := 'O_\sigma(M)^'('F(M))) :
    M \in 'M ->
  [/\ (*a*) cyclic Y /\ \tau2(M).-group Y,
      (*b*) [/\ M^`(2) \subset 'F(M),
                H \* 'C_M(H) = 'F(M)
              & 'F(M`_\sigma) \x Y = 'F(M)],
      (*c*) H \subset M^`(1) /\ nilpotent (M^`(1) / H)
    & (*d*) M \in 'M_'P -> 'F(M) \subset M^`(1)].
Proof.
move=> maxM; have nilF := Fitting_nil M.
have sHF: H \subset 'F(M) := Fcore_sub_Fitting M.
have nsMsM: M`_\sigma <| M := pcore_normal _ _; have [sMsM nMsM] := andP nsMsM.
have sMs: \sigma(M).-group M`_\sigma := pcore_pgroup _ _.
have nsFM: 'F(M) <| M := Fitting_normal M; have [sFM nFM] := andP nsFM.
have sYF: Y \subset 'F(M) := pcore_sub _ _; have sYM := subset_trans sYF sFM.
have defF: 'F(M`_\sigma) \x Y = 'F(M).
  rewrite -(nilpotent_pcoreC \sigma(M) nilF); congr (_ \x _).
  apply/eqP; rewrite eqEsubset pcore_max ?(pgroupS (Fitting_sub _)) //=.
    rewrite Fitting_max ?(nilpotentS (pcore_sub _ _)) //=.
    by rewrite -(pcore_setI_normal _ nsFM) norm_normalI ?(subset_trans sMsM).
  rewrite /normal (char_norm_trans (Fitting_char _)) ?(subset_trans sFM) //.
  by rewrite Fitting_max ?Fitting_nil // (char_normal_trans (Fitting_char _)).
have [[ntH sHMs sMsM' _] nnil_struct] := Fcore_structure maxM.
have hallH: \pi(H).-Hall(M`_\sigma) H := pHall_subl sHMs sMsM (Fcore_Hall M).
have [X [_ cycX t2X defCH]] := cent_Hall_sigma_sdprod maxM hallH ntH.
have hallX: \sigma(M)^'.-Hall('C_M(H)) X.
  have [_ mulCsH_X _ _] := sdprodP defCH.
  have [|//] := coprime_mulpG_Hall mulCsH_X (pgroupS (subsetIl _ _) sMs).
  by apply: sub_pgroup t2X => p /andP[].
have sYX: Y \subset X.
  rewrite (normal_sub_max_pgroup (Hall_max hallX)) ?pcore_pgroup //.
  rewrite /normal (char_norm_trans (pcore_char _ _)) ?subIset ?nFM //= -/Y.
  have [_ _ cFsY _] := dprodP defF.
  rewrite subsetI sYM (sub_nilpotent_cent2 nilF) //= -/Y -/H.
  exact: pnat_coprime (pgroupS sHMs sMs) (pcore_pgroup _ _).
have [cycY t2Y]: cyclic Y /\ \tau2(M).-group Y.
  by rewrite (cyclicS sYX cycX) (pgroupS sYX t2X).
have [K hallK] := Hall_exists \kappa(M) (mmax_sol maxM).
have [U complU] := ex_kappa_compl maxM hallK.
have [[defM _ cM'M'b] defM' _ _ _] := kappa_structure maxM complU.
have d_holds: M \in 'M_'P -> 'F(M) \subset M^`(1).
  rewrite inE maxM andbT -(trivg_kappa maxM hallK) => ntK.
  rewrite -(dprodW defF) mulG_subG (subset_trans (Fitting_sub _)) //= -/Y.
  have{defM'} [[defM' _] nsM'M] := (defM' ntK, der_normal 1 M).
  have hallM': \kappa(M)^'.-Hall(M) M^`(1).
    by apply/(sdprod_normal_pHallP nsM'M hallK); rewrite /= -defM'.
  rewrite (sub_normal_Hall hallM') ?(sub_pgroup _ t2Y) // => p.
  by case/andP=> _; apply: contraL => /rank_kappa->.
have defF_H: 'C_M(H) \subset 'F(M) -> H \* 'C_M(H) = 'F(M).
  move=> sCHF; apply/eqP; rewrite cprodE ?subsetIr // eqEsubset ?mul_subG //=.
  have hallH_F := pHall_subl sHF sFM (Fcore_Hall M).
  have nsHF := normalS sHF sFM (Fcore_normal M).
  have /dprodP[_] := nilpotent_pcoreC \pi(H) nilF.
  rewrite (normal_Hall_pcore hallH_F nsHF) /= -/H => defF_H cHFH' _.
  by rewrite -defF_H mulgS // subsetI (subset_trans (pcore_sub _ _)).
have [eqHMs | neqHMs] := eqVneq H M`_\sigma.
  split=> //; [split=> // | by rewrite eqHMs abelian_nil].
    by rewrite (subset_trans _ sHF) //= eqHMs der1_min ?comm_subG.
  rewrite defF_H // -(sdprodW defCH) -eqHMs mulG_subG subIset ?sHF //=.
  rewrite Fitting_max ?abelian_nil ?cyclic_abelian //.
  rewrite -(normal_Hall_pcore hallX) ?(char_normal_trans (pcore_char _ _)) //.
    by rewrite norm_normalI // eqHMs norms_cent.
  move: defCH; rewrite -dprodEsd; first by case/dprod_normal2.
  by rewrite -eqHMs (centsS (subsetIl _ _)); case/subsetIP: (pHall_sub hallX).
pose q := #|'C_(M`_\sigma)(K)|; pose Q := 'O_q(M).
have [D hallD] := Hall_exists q^' (solvableS sMsM (mmax_sol maxM)).
case/(_ K D): nnil_struct => //=; rewrite -/H -/q -/Q.
move=> [_ _ defMs] [_ _ piHq _] [sylQ nilD _] _ [_ -> [defF_Q _ _] _].
have sQH: Q \subset H by rewrite -[Q](p_core_Fcore piHq) pcore_sub.
split=> //; rewrite -?{}defMs; split=> //.
  by rewrite defF_H // -defF_Q joingC sub_gen // subsetU ?setIS ?centS.
have sQMs := subset_trans sQH sHMs; have sylQ_Ms := pHall_subl sQMs sMsM sylQ.
have nsQ_Ms: Q <| M`_\sigma := normalS sQMs sMsM (pcore_normal _ _).
have defMs: Q ><| D = M`_\sigma := sdprod_normal_p'HallP nsQ_Ms hallD sylQ_Ms.
have [_ <- _ _] := sdprodP defMs; rewrite -quotientMidl mulgA (mulGSid sQH).
by rewrite quotientMidl quotient_nil.
Qed.

(* This is B & G, Corollary 15.6. *)
(* Note that the proof of the F-core noncyclicity given in the text only      *)
(* applies to the nilpotent case, and we need to use a different assertion of *)
(* 15.2 if Msigma is not nilpotent.                                           *)
Corollary Ptype_cyclics M K (Ks := 'C_(M`_\sigma)(K)) :
    M \in 'M_'P -> \kappa(M).-Hall(M) K ->
  [/\ Ks != 1, cyclic Ks, Ks \subset M^`(2), Ks \subset M`_\F
    & ~~ cyclic M`_\F].
Proof.
move=> PmaxM hallK; have [ntK maxM] := setIdP PmaxM.
rewrite -(trivg_kappa maxM hallK) in ntK.
have [_ _ [ntKs _] _ _] := Ptype_structure PmaxM hallK.
have [_ _ [_ _ _ [cycZ _ _ _ _] [_ _ _ defM]]] := Ptype_embedding PmaxM hallK.
have{cycZ} cycKs: cyclic Ks := cyclicS (joing_subr _ _) cycZ.
have solM': solvable M^`(1) := solvableS (der_sub 1 M) (mmax_sol maxM).
have sMsM' := Msigma_der1 maxM.
have{defM} sKsM'': Ks \subset M^`(2).
  have coM'K: coprime #|M^`(1)| #|K|.
    by rewrite (coprime_sdprod_Hall_r defM) (pHall_Hall hallK).
  have [_] := coprime_der1_sdprod defM coM'K solM' (subxx _).
  exact: subset_trans (setSI _ sMsM').
have [eqMFs | neqMFs] := eqVneq M`_\F M`_\sigma.
  split=> //; rewrite eqMFs ?subsetIl //; apply: contra ntKs => cycMs.
  rewrite -subG1 (subset_trans sKsM'') // (sameP trivgP derG1P) /= -derg1.
  have cycF: cyclic 'F(M).
    have [[cycY _] [_ _ defF] _ _] := Fitting_structure maxM.
    have [[x defMs] [y defY]] := (cyclicP cycMs, cyclicP cycY).
    rewrite defMs (nilpotent_Fitting (abelian_nil (cycle_abelian _))) in defF.
    have [_ mulXY cxy _] := dprodP defF.
    rewrite -mulXY defY -cycleM ?cycle_cyclic //.
      by apply/cent1P; rewrite -cycle_subG sub_cent1 -cycle_subG -defY.
    by rewrite /order -defMs -defY coprime_pcoreC.
  apply: abelianS (cyclic_abelian cycF).
  apply: subset_trans (cent_sub_Fitting (mmax_sol maxM)).
  rewrite der1_min ?normsI ?normG ?norms_cent ?gFnorm //=.
  rewrite -ker_conj_aut (isog_abelian (first_isog_loc _ _)) ?gFnorm //=.
  exact: abelianS (Aut_conj_aut _ _) (Aut_cyclic_abelian cycF).
have [D hallD] := Hall_exists #|Ks|^' (solvableS sMsM' solM').
have [_ /(_ K D)[]//=] := Fcore_structure maxM; rewrite -/Ks.
set q := #|Ks|; set Q := 'O_q(M) => _ [_ q_pr piMFq bMq] [sylQ _ _] _ _.
have sQMF: Q \subset M`_\F by rewrite -[Q]p_core_Fcore ?pcore_sub.
have qKs: q.-group Ks := pnat_id q_pr.
have sKsM := subset_trans sKsM'' (der_sub 2 M).
split=> //; first by apply: subset_trans sQMF; rewrite (sub_Hall_pcore sylQ).
apply: contraL (beta_sub_alpha bMq) => /(cyclicS sQMF)cycQ; rewrite -leqNgt.
by rewrite leqW // -(rank_Sylow sylQ) -abelian_rank1_cyclic ?cyclic_abelian.
Qed.

(* This is B & G, Theorem 15.7. *)
(* We had to change the statement of the Theorem, because the first equality  *)
(* of part (c) does not appear to be valid: if M is of type F, we know very   *)
(* little of the action E1 on the Sylow subgroups of E2, and so E2 might have *)
(* a Sylow subgroup that meets F(M) but is also centralised by E1 and hence   *)
(* intesects M' trivially; luckily, only the inclusion M' \subset F(M) seems  *)
(* to be needed in the sequel.                                                *)
(* We have also restricted the quantification on the Ei to part (c), and      *)
(* factored and simplified some of the assertions of parts (e2) and (e3); it  *)
(* appears they could perhaps be simplified futher, since the assertions on   *)
(* Op(H) and Op'(H) do not appear to be used in the Peterfalvi revision of    *)
(* the character theory part of the proof.                                    *)
(*   Proof notes: we had to correct/complete several arguments of the B & G   *)
(* text. The use of 12.6(d) for parts (c) and (d), p. 120, l. 5 from the      *)
(* bottom, is inapropriate as tau2 could be empty. The assertion X1 != Z0 on  *)
(* l. 5, p. 121 needs to be strengthened to ~~ (X1 \subset Z0) in order to    *)
(* prove that #|Z0| is prime -- only then are the assertions equivalent. The  *)
(* use of Lemma 10.13(b), l. 7, p. 121, requires that B be maximal in G, not  *)
(* only in P as is stated l. 6; proving the stronger assertion requires using *)
(* Corollary 15.3(b), which the text does not mention. The regularity         *)
(* property stated l. 11-13 is too weak to be used in the type P1 case -- the *)
(* regularity assumption need to be restricted to a subgroup of prime order.  *)
(* Finally, the cyclicity of Z(H) is not actually needed in the proof.        *)
Theorem nonTI_Fitting_structure M g (H := (M`_\F)%G) :
  let X := ('F(M) :&: 'F(M) :^ g)%G in
    M \in 'M -> g \notin M -> X :!=: 1 ->
  [/\ (*a*) M \in 'M_'F :|: 'M_'P1 /\ H :=: M`_\sigma,
      (*b*) X \subset H /\ cyclic X,
      (*c*) M^`(1) \subset 'F(M) /\ M`_\sigma \x 'O_\sigma(M)^'('F(M)) = 'F(M),
      (*d*) forall E E1 E2 E3, sigma_complement M E E1 E2 E3 -> 
            [/\ E3 :=: 1, E2 <| E, E / E2 \isog E1 & cyclic (E / E2)]
    & (*e*) (*1*) [/\ M \in 'M_'F, abelian H & 'r(H) = 2]
         \/ let p := #|X| in [/\ prime p, ~~ abelian 'O_p(H), cyclic 'O_p^'(H)
          & (*2*) {in \pi(H), forall q, exponent (M / H) %| q.-1}
         \/ (*3*) [/\ #|'O_p(H)| = (p ^ 3)%N, M \in 'M_'P1 & #|M / H| %| p.+1]
  ]].
Proof.
move=> X maxM notMg ntX; have nilH: nilpotent H := Fcore_nil M.
have /andP[sHM nHM]: H <| M := Fcore_normal M.
have [[cycY t2Y] [_ _ defF] _ _] := Fitting_structure maxM.
set Y := 'O_\sigma(M)^'('F(M)) in cycY t2Y defF *.
have not_cycMp: {in \pi(X), forall p, ~~ cyclic 'O_p(M)}.
  move=> p; rewrite mem_primes => /and3P[p_pr _ p_dv_X].
  apply: contra notMg => cycMp.
  have hallMp := nilpotent_pcore_Hall p (Fitting_nil M).
  have{cycMp} defNx1: {in 'F(M), forall x1, #[x1] = p -> 'N(<[x1]>) = M}.
    move=> x1; rewrite /order -cycle_subG => sX1F oX1.
    rewrite (mmax_normal maxM) //; last by rewrite -cardG_gt1 oX1 prime_gt1.
    rewrite (char_normal_trans _ (pcore_normal p M)) ?sub_cyclic_char //=.
    by rewrite -p_core_Fitting (sub_Hall_pcore hallMp) // /pgroup oX1 pnat_id.
  have [x1 Xx1 ox1] := Cauchy p_pr p_dv_X; have [Fx1 Fgx1] := setIP Xx1.
  rewrite -(norm_mmax maxM) inE -{1}(defNx1 (x1 ^ g^-1)) -?mem_conjg ?orderJ //.
  by rewrite cycleJ normJ actKV -(defNx1 x1).
have{cycY} sX: \sigma(M).-group X.
  apply: sub_pgroup (pgroup_pi X) => p piXp.
  apply: contraR (not_cycMp p piXp) => s'p; rewrite -p_core_Fitting.
  by apply: cyclicS (sub_pcore _ _) cycY => p1; move/eqnP->.
have sXMs: X \subset M`_\sigma.
  by rewrite (sub_Hall_pcore (Msigma_Hall maxM)) // subIset ?Fitting_sub.
have E1X_facts p X1 (C1 := 'C_H(X1)%G):
  X1 \in 'E_p^1(X) -> [/\ C1 \notin 'U, 'r(C1) <= 2 & abelian C1].
- move=> EpX1; have [sX1X /andP[pX1 _] _] := pnElemP EpX1.
  have piXp: p \in \pi(X) by rewrite -p_rank_gt0; apply/p_rank_geP; exists X1.
  have not_sCX1M: ~~ ('C(X1) \subset M).
    have [[sX1F sX1Fg] sFM] := (subsetIP sX1X, Fitting_sub M).
    apply: contra notMg => sCX1M; rewrite -groupV.
    have [trCX1 _ _] := sigma_group_trans maxM (pnatPpi sX piXp) pX1.
    have [||c cX1c] := trCX1 g^-1; rewrite ?(subset_trans _ sFM) ?sub_conjgV //.
    by case=> m Mm ->; rewrite groupM // (subsetP sCX1M).
  have ltCX1_G: 'C(X1) \proper G := mFT_cent_proper (nt_pnElem EpX1 isT).
  have ltC1G: C1 \proper G := sub_proper_trans (subsetIr H _) ltCX1_G.
  have{ltCX1_G} nonuniqC1: C1 \notin 'U.
    have sC1M: C1 \subset M by rewrite subIset ?Fcore_sub.
    apply: contra not_sCX1M => uniqC1.
    by rewrite (sub_uniq_mmax (def_uniq_mmax uniqC1 maxM sC1M)) ?subsetIr.
  split=> //; first by rewrite leqNgt (contra (rank3_Uniqueness _)).
  have sC1H: C1 \subset H := subsetIl _ _.
  have dprodC1: 'F(C1) = C1 := nilpotent_Fitting (nilpotentS sC1H nilH).
  apply/center_idP; rewrite -{2}dprodC1 -(center_bigdprod dprodC1).
  apply: eq_bigr => r _; apply/center_idP; apply: contraR nonuniqC1.
  move/(nonabelian_Uniqueness (pcore_pgroup _ _)).
  exact: uniq_mmaxS (pcore_sub _ _) ltC1G.
pose p := pdiv #|X|; have piXp: p \in \pi(X) by rewrite pi_pdiv cardG_gt1.
have /p_rank_geP[X1 EpX1]: 0 < 'r_p(X) by rewrite p_rank_gt0.
have [sMp ntX1] := (pnatPpi sX piXp, nt_pnElem EpX1 isT).
have [p_pr oX1] := (pnElem_prime EpX1, card_pnElem EpX1 : #|X1| = p).
have [sX1X abelX1 dimX1] := pnElemP EpX1; have [pX1 _] := andP abelX1.
have [nonuniqC1 rC1 cC1C1] := E1X_facts p X1 EpX1.
have [cycX b'p]: cyclic X /\ p \in \beta(M)^'.
  have [E hallE] := ex_sigma_compl maxM.
  have [_ _] :=  sigma_compl_embedding maxM hallE.
  case/(_ g notMg); set X2 := _ :&: _ => cycX2 b'X2 _.
  have sXMg: X \subset M :^ g by rewrite subIset // conjSg Fitting_sub orbT.
  have{sXMg} sXX2: X \subset X2 by rewrite subsetI sXMs.
  by rewrite (pnatPpi b'X2 (piSg sXX2 piXp)) (cyclicS sXX2).
have b'H: \beta(M)^'.-group H.
  apply: sub_pgroup (pgroup_pi _) => r piHr; have [-> // | p'r] := eqVneq r p.
  apply/existsP; exists 'O_r(M)%G; rewrite /= Fcore_pcore_Sylow // negbK.
  apply/implyP; rewrite ltnNge -rank_pgroup ?pcore_pgroup ?(leq_trans _ rC1) //.
  rewrite rankS // subsetI /= -{1}(p_core_Fcore piHr) pcore_sub //.
  rewrite -p_core_Fitting (sub_nilpotent_cent2 (Fitting_nil M)) ?pcore_sub //.
    exact: subset_trans sX1X (subsetIl _ _).
  exact: pnat_coprime pX1 (pi_pgroup (pcore_pgroup r _) _).
have [K hallK] := Hall_exists \kappa(M) (mmax_sol maxM).
have [sKM kK _] := and3P hallK; have s'K := sub_pgroup (@kappa_sigma' _ M) kK.
have [U complU] := ex_kappa_compl maxM hallK.
have [[defM cycK _] defM' _ _ exU0] := kappa_structure maxM complU.
have{b'p} FP1maxM: M \in 'M_'F :|: 'M_'P1.
  apply: contraR b'p; rewrite inE /=; case/norP=> notFmaxF notP1maxF.
  have PmaxM: M \in 'M_'P by apply/setDP.
  by have [_ _ _ _ [| <- //]] := Ptype_structure PmaxM hallK; apply/setDP.
have defH: H :=: M`_\sigma.
  apply/eqP; apply/idPn=> neqHMs; pose q := #|'C_(M`_\sigma)(K)|.
  have solMs: solvable M`_\sigma := solvableS (pcore_sub _ _) (mmax_sol maxM).
  have [D hallD] := Hall_exists q^' solMs.
  have [_ /(_ K D)[] // _ [_ _ piHq /idPn[]]] := Fcore_structure maxM.
  exact: pnatPpi b'H piHq.
have{sXMs} sXH: X \subset H by rewrite defH.
have{b'H} sM'F: M^`(1) \subset 'F(M).
  rewrite Fitting_max ?der_normal // (isog_nil (quotient1_isog _)).
  suffices <-: M`_\beta = 1 by apply: Mbeta_quo_nil.
  apply/eqP; rewrite trivg_card1 (card_Hall (Mbeta_Hall maxM)).
  rewrite -(partn_part _ (beta_sub_sigma maxM)) -(card_Hall (Msigma_Hall maxM)).
  by rewrite /= -defH partG_eq1.
have{defF} defF: M`_\sigma \x Y = 'F(M).
  by rewrite -defF -defH nilpotent_Fitting.
split=> // [E E1 E2 E3 complEi | {Y t2Y defF sM'F}].
  have [[sE3E' _] _ [cycE1 _] [_ defE] _]:= sigma_compl_context maxM complEi.
  have [hallE _ _ hallE3 _] := complEi; have [sE3E t3E3 _] := and3P hallE3.
  have E3_1: E3 :=: 1.
    have [sEM s'E _] := and3P hallE; have sE'M' := dergS 1 sEM.
    have sE3F: E3 \subset 'F(M) := subset_trans sE3E' (subset_trans sE'M' sM'F).
    rewrite -(setIidPr sE3F) coprime_TIg // -(dprod_card defF) coprime_mull. 
    rewrite (pnat_coprime (pcore_pgroup _ _) (pgroupS sE3E s'E)).
    exact: p'nat_coprime (sub_pgroup (@tau3'2 _ M) t2Y) t3E3.
  have{defE} defE: E2 ><| E1 = E by rewrite -defE E3_1 sdprod1g.
  have [-> _ mulE21 nE21 tiE21] := sdprod_context defE.
  by rewrite -mulE21 quotientMidl quotient_cyclic // isog_sym quotient_isog.
have{defM'} defM_P1: M \in 'M_'P1 -> H ><| K = M /\ M^`(1) = H.
  move=> P1maxM; have [PmaxM _] := setIdP P1maxM.
  have U1: U :=: 1 by apply/eqP; rewrite (trivg_kappa_compl maxM complU).
  have ntK: K :!=: 1 by rewrite (trivg_kappa maxM hallK); case/setDP: PmaxM.
  by have [<- _] := defM' ntK; rewrite -{1}defM U1 sdprodg1 -defH.
pose P := 'O_p(H); have sylP: p.-Sylow(H) P := nilpotent_pcore_Hall p nilH.
have [sPH pP _] := and3P sylP.
have [cHH | {not_cycMp} not_cHH] := boolP (abelian H); [left | right].
  have [-> | P1maxM] := setUP FP1maxM; last first.
    have [PmaxM _] := setIdP P1maxM.
    have [ntKs _ sKsM'' _ _] := Ptype_cyclics PmaxM hallK.
    case/eqP: (subG1_contra sKsM'' ntKs); apply/derG1P.
    by rewrite /= -derg1; have [_ ->] := defM_P1 P1maxM.
  split=> //; apply/eqP; rewrite eqn_leq (leq_trans _ rC1) //=; last first.
    by rewrite rankS // subsetIidl (centsS sX1X) // (sub_abelian_cent cHH).
  apply: leq_trans (rankS (pcore_sub p _)).
  rewrite ltnNge -abelian_rank1_cyclic ?(abelianS sPH) //=.
  by rewrite p_core_Fcore ?(piSg sXH) ?not_cycMp.
have sX1P: X1 \subset P by rewrite (sub_Hall_pcore sylP) ?(subset_trans sX1X).
have [_ mulPHp' cPHp' _] := dprodP (nilpotent_pcoreC p nilH : P \x _ = H).
have cHp'Hp': abelian 'O_p^'(H).
  by rewrite (abelianS _ cC1C1) // subsetI pcore_sub (centsS sX1P).
have not_cPP: ~~ abelian P.
  by apply: contra not_cHH => cPP; rewrite -mulPHp' abelianM cPP cHp'Hp'.
have{E1X_facts} pX: p.-group X.
  apply: sub_pgroup (pgroup_pi _) => q; rewrite -p_rank_gt0.
  case/p_rank_geP=> X2 EqX2; have [_ _ cC2C2] := E1X_facts _ _ EqX2.
  case/pnElemP: EqX2 => sX2X /andP[qX2 _] _; have sX2H := subset_trans sX2X sXH.
  apply: contraR not_cPP => q'p; rewrite (abelianS _ cC2C2) // subsetI sPH.
  by rewrite (sub_nilpotent_cent2 nilH) ?(p'nat_coprime (pi_pgroup qX2 _) pP).
have sXP: X \subset P by rewrite (sub_Hall_pcore sylP).
pose Z0 := 'Ohm_1('Z(P)); have sZ0ZP: Z0 \subset 'Z(P) := Ohm_sub 1 _.
have{sZ0ZP} [sZ0P cPZ0] := subsetIP sZ0ZP.
have not_sX1Z0: ~~ (X1 \subset Z0).
  apply: contra not_cPP => sX1Z0; apply: abelianS cC1C1.
  by rewrite subsetI sPH (centsS sX1Z0) // centsC.
pose B := X1 <*> Z0; have sBP: B \subset P by rewrite join_subG sX1P.
have defB: X1 \x Z0 = B by rewrite dprodEY ?prime_TIg ?oX1 ?(centsS sX1P).
have pZP: p.-group 'Z(P) := pgroupS (center_sub _) pP.
have abelZ0: p.-abelem Z0 by rewrite Ohm1_abelem ?center_abelian.
have{abelZ0} abelB: p.-abelem B by rewrite (dprod_abelem _ defB) abelX1.
have sylP_Ms: p.-Sylow(M`_\sigma) P by rewrite -defH.
have sylP_G: p.-Sylow(G) P := subHall_Sylow (Msigma_Hall_G maxM) sMp sylP_Ms.
have max_rB A: p.-abelem A -> B \subset A -> 'r_p(A) <= 2.
  move=> abelA /joing_subP[sX1A _]; have [pA cAA _] := and3P abelA.
  suffices [a [nX1a sAaP]]: exists a, a \in 'N(X1) /\ A :^ a \subset P.
    rewrite -rank_pgroup // -(rankJ _ a) (leq_trans _ rC1) ?rankS //= subsetI.
    by rewrite -(normP nX1a) centJ conjSg (subset_trans sAaP) ?(centsS sX1A).
  have [a _ sAaP] := Sylow_Jsub sylP_G (subsetT A) pA.
  have [x1 defX1]: exists x1, X1 :=: <[x1]>.
    by apply/cyclicP; rewrite prime_cyclic ?oX1.
  have Px1: x1 \in P by rewrite -cycle_subG -defX1.
  have Px1a: x1 ^ a \in P. 
    by rewrite (subsetP sAaP) // memJ_conjg -cycle_subG -defX1.
  have [b nPb def_xb] := sigma_Hall_tame maxM sylP_Ms Px1 Px1a.
  exists (a * b^-1); rewrite !inE !actM !sub_conjgV defX1 /= -!cycleJ def_xb.
  by have{nPb} [_ nPb] := setIP nPb; rewrite (normP nPb).
have rpB: 'r_p(B) = 2.
  apply/eqP; rewrite eqn_leq max_rB // -(p_rank_dprod p defB).
  rewrite p_rank_abelem ?dimX1 // ltnS p_rank_Ohm1 -rank_pgroup // rank_gt0.
  by rewrite center_nil_eq1 ?(pgroup_nil pP) ?(subG1_contra sXP).
have oZ0: #|Z0| = p.
  apply/eqP; rewrite -(eqn_pmul2l (cardG_gt0 X1)) (dprod_card defB) oX1.
  by rewrite (card_pgroup (abelem_pgroup abelB)) -p_rank_abelem ?rpB.
have p2maxElemB: [group of B] \in 'E_p^2(G) :&: 'E*_p(G).
  rewrite !inE subsetT abelB -p_rank_abelem // rpB /=.
  apply/maxgroupP; rewrite !inE subsetT /= -/B; split=> // A.
  case/pElemP=> _ abelA sBA; have [pA _] := andP abelA.
  apply/eqP; rewrite eq_sym eqEcard sBA (card_pgroup pA).
  rewrite (card_pgroup (abelem_pgroup abelB)) -!p_rank_abelem // rpB.
  by rewrite leq_exp2l ?prime_gt1 ?max_rB.
have{not_sX1Z0} defX: X :=: X1.
  have sX_CPB: X \subset 'C_P(B).
    rewrite centY !subsetI sXP sub_abelian_cent ?cyclic_abelian //=.
    by rewrite centsC (centsS sXP).
  have [C defCPB]: exists C, X1 \x C = 'C_P(B).
    have [_ [C]] := basic_p2maxElem_structure p2maxElemB pP sBP not_cPP.
    case=> _ _ defCPB _; exists C; rewrite defCPB // !inE joing_subl abelX1.
    by rewrite -val_eqE eqEsubset negb_and not_sX1Z0 /= dimX1.
  have defX: X1 \x (C :&: X) = X by rewrite (dprod_modl defCPB) // (setIidPr _).
  by move/eqP: ntX1; case/(cyclic_pgroup_dprod_trivg pX cycX): defX; case.
have cycHp': cyclic 'O_p^'(H).
  rewrite abelian_rank1_cyclic // leqNgt; apply: contra nonuniqC1 => rHp'.
  apply: (uniq_mmaxS (setIS H (centS sX1P))).
    by rewrite mFT_sol_proper nilpotent_sol // (nilpotentS (subsetIl _ _)).
  apply: cent_uniq_Uniqueness (subsetIr _ _) (leq_trans rHp' (rankS _)).
    exact: nonabelian_Uniqueness pP not_cPP.
  by rewrite subsetI pcore_sub.
rewrite {1}defX oX1 /= -[M`_\F]/(gval H) -/P; split=> //.
pose Z q := 'Ohm_1('Z('O_q(H)))%G.
have charZ q: Z q \char H.
  have:= char_trans (center_char _) (pcore_char q H).
  exact: char_trans (Ohm_char 1 _).
have{cycHp'} oZ: {in \pi(H), forall q, #|Z q| = q}.
  move=> q piHp; have [-> // | p'q] := eqVneq q p.
  have qHq: q.-group 'O_q(H) := pcore_pgroup q H.
  have sHqHp': 'O_q(H) \subset 'O_p^'(H) by apply: sub_pcore => r /eqnP->.
  rewrite /= (center_idP (abelianS sHqHp' cHp'Hp')).
  apply: Ohm1_cyclic_pgroup_prime (cyclicS sHqHp' cycHp') qHq _.
  by rewrite -rank_gt0 (rank_Sylow (nilpotent_pcore_Hall q nilH)) p_rank_gt0.
have regZq_dv_q1 A q:
  A \subset 'N(H) -> q \in \pi(H) -> semiregular (Z q) A -> #|A| %| q.-1.
- move=> nHA piHq regA.
  by rewrite -(oZ q piHq) regular_norm_dvd_pred // (char_norm_trans (charZ q)).
have [FmaxM | {U complU defM exU0}P1maxM] := setUP FP1maxM.
  left=> q piHq; have K1: K :=: 1 by apply/eqP; rewrite (trivg_kappa maxM).
  have ntU: U :!=: 1 by rewrite (trivg_kappa_compl maxM complU) 2!inE FmaxM.
  rewrite K1 sdprodg1 -defH in defM; have [_ mulHU nHU tiHU] := sdprodP defM.
  rewrite -mulHU quotientMidl -(exponent_isog (quotient_isog nHU tiHU)).
  have [U0 [sU0U <- frobMsU0]] := exU0 ntU; have nHU0 := subset_trans sU0U nHU.
  apply: dvdn_trans (exponent_dvdn U0) _; apply: regZq_dv_q1 => // x U0x.
  apply/trivgP; rewrite -(Frobenius_reg_ker frobMsU0 U0x) setSI //= -defH.
  exact: (char_sub (charZ _)).
have{defM_P1} [[defM defM'] [PmaxM _]] := (defM_P1 P1maxM, setIdP P1maxM).
have [_ mulHK nHK tiHK] := sdprodP defM; have p'K := pi'_p'group s'K sMp.
have coHK: coprime #|H| #|K| by rewrite defH (pnat_coprime (pcore_pgroup _ _)).
have{coHK} coPK: coprime #|P| #|K| := coprimeSg sPH coHK.
have oMH: #|M / H| = #|K|.
  by rewrite -mulHK quotientMidl -(card_isog (quotient_isog nHK tiHK)).
pose Ks := 'C_H(K); have prKs: prime #|Ks|.
  have [Ms _ [_ _ _ _ [_]]] := Ptype_embedding PmaxM hallK.
  by rewrite inE P1maxM -defH; do 2!case.
have sKsP: Ks \subset P.
  have sKsM'': Ks \subset M^`(2) by rewrite /Ks defH; case/Ptype_cyclics: hallK.
  rewrite (subset_trans sKsM'') 1?der1_min //= -derg1 defM' ?gFnorm //.
  by rewrite -mulPHp' quotientMidl quotient_abelian.
have oKs: #|Ks| = p.
  apply/eqP; apply: pnatPpi pP (piSg sKsP _).
  by rewrite mem_primes prKs cardG_gt0 dvdnn.
have [prHK ntKs]: semiprime H K /\ Ks != 1.
  by rewrite /Ks defH; case/Ptype_structure: hallK => // [[_ _ [_ ? _]] _ []].
have [K_dv_p1 | {regZq_dv_q1}] := altP (@implyP (Ks :==: Z0) (#|K| %| p.-1)).
  left=> q piHq; rewrite (dvdn_trans (exponent_dvdn _)) // oMH.
  have [eqZqKs | neqZqKs] := eqVneq Ks (Z q).
    have def_q: q = p by rewrite -(oZ q piHq) -eqZqKs.
    by rewrite def_q K_dv_p1 // eqZqKs def_q.
  apply: regZq_dv_q1 => // x Kx; rewrite -(setIidPl (char_sub (charZ q))).
  rewrite -setIA prHK {x Kx}// setIC (prime_TIg prKs) //.
  have q_pr: prime q by rewrite mem_primes in piHq; case/and3P: piHq.
  apply: contra neqZqKs => sKsZq; rewrite eqEsubset sKsZq /=.
  by rewrite prime_meetG ?oZ // (setIidPr sKsZq).
rewrite {Z oZ charZ}negb_imply; case/andP; move/eqP=> defKs not_K_dv_p1.
have nPK: K \subset 'N(P) := char_norm_trans (pcore_char p H) nHK.
have defZP: 'Z(P) = Ks.
  apply/eqP; rewrite eqEsubset andbC {1}defKs Ohm_sub subsetI subIset ?sPH //.
  have nZPK: K \subset 'N('Z(P)) := char_norm_trans (center_char _) nPK.
  have coZPK: coprime #|'Z(P)| #|K| := coprimeSg (center_sub _) coPK.
  rewrite centsC (coprime_odd_faithful_Ohm1 pZP) ?mFT_odd //.
  by rewrite /= -/Z0 -defKs centsC subsetIr.
have rPle2: 'r(P) <= 2.
  case/setIP: p2maxElemB; case/pnElemP=> _ _ dimB pmaxB.
  have Ep2B: [group of B] \in 'E_p^2(P) by apply/pnElemP.
  rewrite leqNgt; apply: contra not_K_dv_p1 => rPgt2.
  have tiKcP: 'C_K(P) = 1.
    apply/trivgP/subsetP=> x => /setIP[Kx cPx].
    apply: contraR ntX1 => ntx; rewrite -subG1.
    have [_ _ _ <-] := dprodP defB; rewrite subsetIidl -defKs.
    rewrite -[Ks](prHK x) 1?inE ?ntx // (subset_trans sX1P) //=.
    by rewrite subsetI sPH sub_cent1.
  rewrite (card_isog (quotient1_isog _)) -tiKcP -ker_conj_aut.
  rewrite (card_isog (first_isog_loc _ nPK)) /=.
  set A := _ @* _; have AutA: A \subset Aut P := Aut_conj_aut _ _.
  have solA: solvable A by rewrite morphim_sol ?abelian_sol ?cyclic_abelian.
  have oddA: odd #|A| by rewrite morphim_odd ?mFT_odd.
  have nnP: p.-narrow P.
    apply/implyP=> _; apply/set0Pn; exists [group of B].
    by rewrite inE Ep2B (subsetP (pmaxElemS p (subsetT P))) // inE pmaxB inE.
  have [x defK] := cyclicP cycK; have Kx: x \in K by rewrite defK cycle_id.
  have nPx := subsetP nPK x Kx; rewrite /A defK morphim_cycle //.
  have Axj: conj_aut [group of P] x \in A by exact: mem_morphim.
  have [_ _ -> //] := Aut_narrow pP (mFT_odd _) nnP solA AutA oddA.
  by rewrite morph_p_elt // (mem_p_elt p'K).
have{rPle2} dimP: logn p #|P| = 3.
  have [S [_ <- _] [C cycC]] := mFT_rank2_Sylow_cprod sylP_G rPle2 not_cPP.
  case=> defP defZS; congr (logn p #|(_ : {set _})|).
  suffices defC: 'Ohm_1(C) = C by rewrite -defC defZS cprod_center_id in defP.
  suffices <-: 'Z(P) = C by rewrite defZP (@Ohm1_id _ p) // prime_abelem.
  have [_ <- _] := cprodP (center_cprod defP).
  by rewrite -defZS (center_idP (cyclic_abelian cycC)) mulSGid ?Ohm_sub.
have oP: #|P| = (p ^ 1.*2.+1)%N by rewrite (card_pgroup pP) dimP.
right; split; rewrite // {}oMH.
have esP: extraspecial P by apply: (p3group_extraspecial pP); rewrite ?dimP.
have defPK: P ><| K = P <*> K by rewrite sdprodEY // coprime_TIg.
have copK: coprime p #|K| by rewrite -oX1 (coprimeSg sX1P).
have [x|] := repr_extraspecial_prime_sdprod_cycle pP esP defPK cycK oP copK.
  move/prHK=> defCHx /=; rewrite /= -/P -{1}(setIidPl sPH) -setIA defCHx -/Ks.
  by rewrite -defZP setIA setIid.
by rewrite addn1 subn1 (negPf not_K_dv_p1) orbF.
Qed.

(* A subset of the above, that does not require the non-TI witness. *)
Lemma nonTI_Fitting_facts M :
    M \in 'M -> ~~ normedTI 'F(M)^# G M ->
  [/\ M \in 'M_'F :|: 'M_'P1, M`_\F = M`_\sigma & M^`(1) \subset 'F(M)].
Proof.
move=> maxM nonTI; suff: [exists (y | y \notin M), 'F(M) :&: 'F(M) :^ y != 1].
  by case/exists_inP=> y notMy /nonTI_Fitting_structure[] // [[-> ?] _ []].
rewrite -negb_forall_in; apply: contra nonTI => /forall_inP tiF.
apply/normedTI_P; rewrite normD1 setTI gFnorm setD_eq0 subG1.
split=> // [|g _]; first by rewrite (trivg_Fitting (mmax_sol maxM)) mmax_neq1.
by apply: contraR => /tiF; rewrite -setI_eq0 conjD1g -setDIl setD_eq0 subG1.
Qed.

(* This is B & G, Theorem 15.8, due to Feit and Thompson (1991). *)
(* We handle the non-structural step on l. 5, p. 122 by choosing A not to be  *)
(* a q-group, if possible, so that when it turns out to be we know q is the   *)
(* only prime in tau2(H). Since this uniqueness does not appear to be used    *)
(* later we could also eliminate this complication.                           *)
(*   We also avoid the circularity in proving that A is a q-group and that Q  *)
(* is non-abelian by deriving that Q is in U from 14.2(e) rather than 12.13.  *)
Theorem tau2_P2type_signalizer M Mstar U K r R H (q := #|K|) :
    M \in 'M_'P2 -> kappa_complement M U K -> Mstar \in 'M('C(K)) ->
    r.-Sylow(U) R -> H \in 'M('N(R)) -> ~~ \tau2(H)^'.-group H ->
  [/\ prime q, \tau2(H) =i (q : nat_pred) & \tau2(M)^'.-group M].
Proof.
move: Mstar => L P2maxM complU maxCK_L sylR maxNR_H not_t2'H.
have [[PmaxM notP1maxM] [hallU hallK _]] := (setDP P2maxM, complU). 
have q_pr: prime q by have [_ _ _ _ []] := Ptype_structure PmaxM hallK.
have [[maxH _] [maxM _]] := (setIdP maxNR_H, setDP PmaxM).
have [maxL sCKL] := setIdP maxCK_L; have hallLs := Msigma_Hall maxL.
have [_ sUHs] := P2type_signalizer P2maxM complU maxCK_L sylR maxNR_H.
set D := H :&: L => defUK [_ sKFD hallD] {r R sylR maxNR_H}.
set uniq_q := _ =i _.
have{not_t2'H} [q1 t2Hq neq_q]: exists2 q1, q1 \in \tau2(H) & q1 = q -> uniq_q.
  move: not_t2'H; rewrite negb_and cardG_gt0 all_predC negbK /= has_filter.
  set s := filter _ _ => nts.
  have mem_s: s =i \tau2(H).
    move=> q1; rewrite mem_filter; apply: andb_idr => /= t2q1.
    by rewrite (partition_pi_mmax maxH) t2q1 !orbT.
  have [all_q | ] := altP (@allP _ (pred1 q) s); last first.
    by case/allPn=> q1; rewrite mem_s=> t2q1; move/eqnP=> ne_q1q; exists q1.
  have s_q1: head q s \in s by case: (s) nts => // q1 s' _; exact: predU1l.
  exists (head q s) => [|def_q q1]; rewrite -mem_s //.
  by apply/idP/idP; [exact: all_q | move/eqnP->; rewrite -def_q].
have [A /= Eq2A Eq2A_H] := ex_tau2Elem hallD t2Hq; rewrite -/D in Eq2A.
have [b'q qmaxA]: q1 \notin \beta(G) /\ A \in 'E*_q1(G).
  by have [-> ->] := tau2_not_beta maxH t2Hq.
have [sDH s'HD _] := and3P hallD.
have [sAH abelA dimA] := pnElemP Eq2A_H; have [qA _] := andP abelA.
have [[nsAD _] _ _ _] := tau2_compl_context maxH hallD t2Hq Eq2A.
have cKA: A \subset 'C(K).
  have sFD: 'F(D) \subset D := Fitting_sub _; have sFH := subset_trans sFD sDH.
  have cFF: abelian 'F(D).
    exact: sigma'_nil_abelian maxH sFH (pgroupS sFD s'HD) (Fitting_nil _).
  exact: sub_abelian_cent2 cFF (Fitting_max nsAD (pgroup_nil qA)) sKFD.
have sAL: A \subset L := subset_trans cKA sCKL.
pose Ks := 'C_(M`_\sigma)(K).
have [PmaxL hallKs defK]:
  [/\ L \in 'M_'P, \kappa(L).-Hall(L) Ks & 'C_(L`_\sigma)(Ks) = K].
- have [L1 [? _] [defL1 [? _] [? _] _ _]] := Ptype_embedding PmaxM hallK.
  suffices ->: L = L1 by []; apply/set1P; rewrite defL1 // in maxCK_L.
  by apply/nElemP; exists q; rewrite p1ElemE // !inE subxx eqxx.
have sKLs: K \subset L`_\sigma by rewrite -defK subsetIl.
have sLq: q \in \sigma(L).
  by rewrite -pnatE // -pgroupE (pgroupS sKLs) ?pcore_pgroup.
have sLq1: q1 \in \sigma(L).
  apply: contraLR sLq => s'Lq1; rewrite -negnK negbK /= -pnatE // -pgroupE.
  have s'LA: \sigma(L)^'.-group A by exact: pi_pgroup qA _.
  have [E hallE sAE] := Hall_superset (mmax_sol maxL) sAL s'LA.
  have EqA_E: A \in 'E_q1^2(E) by exact/pnElemP.
  have [[sEL s'E _] t2Lq1] := (and3P hallE, sigma'2Elem_tau2 maxL hallE EqA_E).
  have [_ [sCAE _ _] _ _] := tau2_compl_context maxL hallE t2Lq1 EqA_E.
  by apply: pgroupS (subset_trans _ sCAE) s'E; rewrite centsC.
have sALs: A \subset L`_\sigma by rewrite sub_Hall_pcore ?(pi_pgroup qA).
have solL: solvable L`_\sigma := solvableS (pcore_sub _ _) (mmax_sol maxL).
pose Q := 'O_q(L)%G; have{solL} [Ds hallDs] := Hall_exists q^' solL.
have sQFL: Q \subset 'F(L) by rewrite -[gval Q]p_core_Fitting pcore_sub.
have [sAFL sylQ]: A \subset 'F(L) /\ q.-Sylow(L) Q.
  have [defLF | neqLF] := eqVneq L`_\F L`_\sigma.
    split; first by rewrite (subset_trans sALs) // -defLF Fcore_sub_Fitting.
    by rewrite Fcore_pcore_Sylow // defLF mem_primes q_pr cardG_gt0 cardSg.
  have [_ /(_ _ Ds hallKs neqLF)] := Fcore_structure maxL.
  rewrite /= defK -/q -/Q; case=> // _ _ [-> _ nsQ0L] _ [_ _ [_ _ <-] _].
  rewrite subsetI sALs sub_astabQ quotient_cents // (subset_trans sAL) //.
  exact: normal_norm nsQ0L.
have{sLq1} neqHL: H :!=: L.
  by apply: contraTneq t2Hq => ->; rewrite negb_and negbK /= sLq1.
have def_q1: q1 = q.
  have uniqQ: Q \in 'U.
    have [_ _ _ [_ uniqQ _] _] := Ptype_structure PmaxL hallKs.
    apply/uniq_mmaxP; exists L; case/uniqQ: sylQ => //=; rewrite defK.
    by rewrite pi_of_prime ?inE.
  apply: contraNeq neqHL => q'q1.
  rewrite (eq_uniq_mmax (def_uniq_mmax _ maxL sAL) maxH sAH) //.
  rewrite (cent_uniq_Uniqueness uniqQ) ?(rank_abelem abelA) ?dimA //.
  rewrite (sub_nilpotent_cent2 (Fitting_nil L)) //.
  exact: pnat_coprime (pcore_pgroup _ _) (pi_pgroup qA _).
split=> //; first exact: neq_q.
rewrite {q1 neq_q}def_q1 in qA Eq2A Eq2A_H t2Hq abelA dimA qmaxA b'q.
have{b'q} b'q: q \notin \beta(L) by rewrite -predI_sigma_beta // inE /= sLq.
have P1maxL: L \in 'M_'P1.
  apply: contraR b'q => notP1maxL.
  by have [_ _ _ _ [|<- //]] := Ptype_structure PmaxL hallKs; apply/setDP.
have nilLs: nilpotent L`_\sigma.
  rewrite (sameP (Fcore_eq_Msigma maxL) eqP); apply: contraR b'q => neqLF.
  have [_ /(_ _ Ds hallKs neqLF)] := Fcore_structure maxL.
  by rewrite /= defK -/q -/Q; case=> // _ [_ _ _ ->] _ _ _.
have defL': L^`(1) = L`_\sigma.
  have [Us complUs] := ex_kappa_compl maxL hallKs.
  have [_ [|<- _ _ _ _]] := kappa_structure maxL complUs.
    by rewrite (trivg_kappa maxL hallKs) //; case/setDP: PmaxL.
  suffices ->: Us :=: 1 by rewrite sdprodg1.
  by apply/eqP; rewrite (trivg_kappa_compl maxL complUs).
have [ntK sKLs']: K :!=: 1 /\ K \subset L`_\sigma^`(1).
  by rewrite -defL' -defK; case/Ptype_cyclics: hallKs.
have [sQL qQ _] := and3P sylQ.
have not_cQQ: ~~ abelian Q.
  have sKL: K \subset L := subset_trans sKLs (pcore_sub _ _).
  have sKQ: K \subset Q by rewrite (sub_Hall_pcore sylQ) /pgroup ?pnat_id.
  have sQLs: Q \subset L`_\sigma by rewrite sub_Hall_pcore ?(pi_pgroup qQ).
  have defLs: 'O_q^'(L`_\sigma) * Q = L`_\sigma.
    rewrite -(setIidPl sQLs) pcore_setI_normal ?pcore_normal //.
    by have [_] := dprodP (nilpotent_pcoreC q^' nilLs); rewrite pcoreNK.
  apply: contra ntK => cQQ; rewrite -subG1 /= -(derG1P cQQ) -subsetIidl.
  rewrite -(pprod_focal_coprime defLs) ?subsetIidl ?pcore_normal //.
  by rewrite coprime_sym (coprimeSg sKQ) ?coprime_pcoreC.
pose X := 'C_A(H`_\sigma)%G.
have [sXA cHsX]: X \subset A /\ X \subset 'C(H`_\sigma) by apply/subsetIP.
have{not_cQQ} oX: #|X| = q.
  by have [_ []] := nonabelian_tau2 maxH hallD t2Hq Eq2A qQ not_cQQ.
have neqXK: X :!=: K.
  apply: contraNneq neqHL => defX; rewrite (eq_mmax maxH maxL) //.
  have [_ <- _ _] := sdprodP (sdprod_sigma maxH hallD).
  by rewrite mulG_subG subsetIr (subset_trans _ sCKL) // centsC -defX.
have{neqXK sXA} not_sXM: ~~ (X \subset M).
  apply: contra neqXK => sXM; rewrite eqEcard oX leqnn andbT; apply/joing_idPl.
  have [[sKM kK _] cKX] := (and3P hallK, subset_trans sXA cKA).
  apply: sub_pHall hallK _ (joing_subl _ _) _; last by rewrite join_subG sKM.
  by rewrite /= (cent_joinEr cKX) pgroupM {2}/pgroup oX andbb.
have{not_sXM} not_sCUM: ~~ ('C(U) \subset M).
  exact: contra (subset_trans (centsS sUHs cHsX)) not_sXM.
apply/pgroupP=> r r_pr _; apply: contra not_sCUM => /= t2Mr.
have [hallUK _ _ _ _] := kappa_compl_context maxM complU.
have [[B Er2B _] [sUKM _]] := (ex_tau2Elem hallUK t2Mr, andP hallUK).
have [[nsBUK _] [sCBUK _ _] _ _ ] := tau2_compl_context maxM hallUK t2Mr Er2B.
apply: subset_trans (centS _) (subset_trans sCBUK sUKM).
have [sBUK /andP[rB _] _] := pnElemP Er2B.
have maxU_UK := Hall_max (pHall_subl (joing_subl _ _) sUKM hallU).
rewrite (normal_sub_max_pgroup maxU_UK) // (pi_pgroup rB) //.
apply: contraL t2Mr; rewrite negb_and negbK /= inE /=.
by case: (r \in _) => //=; move/rank_kappa->.
Qed.

(* This is B & G, Theorem 15.9, parts (a) and (b), due to D. Sibley and Feit  *)
(* and Thompson, respectively.                                                *)
(* We have dropped part (c) because it is not used later, and localizing the  *)
(* quantification on r would complicate the proof needlessly.                 *)
Theorem nonFtype_signalizer_base M x :
   M \in 'M -> x \in M`_\sigma^# ->
   ~~ ('C[x] \subset M) -> 'N[x] \notin 'M_'F ->
 [/\ (*a*) M \in 'M_'F, 'N[x] \in 'M_'P2
   & (*b*) exists2 E : {group gT}, \sigma(M)^'.-Hall(M) E
         & cyclic (gval E) /\ [Frobenius M = M`_\sigma ><| E]].
Proof.
move=> maxM Ms1x not_sCxM notFmaxN; have ell1x := Msigma_ell1 maxM Ms1x.
have [[ntx Ms_x] [y cxy notMy]] := (setD1P Ms1x, subsetPn not_sCxM).
have SMxM: M \in 'M_\sigma[x] by rewrite inE maxM cycle_subG.
have SMxMy: (M :^ y)%G \in 'M_\sigma[x].
  by rewrite inE mmaxJ maxM gen_subG -(normP cxy) /= MsigmaJ conjSg sub1set.
have neq_MyM: M :^ y != M by rewrite (sameP eqP normP) norm_mmax.
have SMx_gt1: #|'M_\sigma[x]| > 1.
  by rewrite (cardD1 M) SMxM (cardD1 (M :^ y)%G) inE /= SMxMy neq_MyM.
have [_ [//|uniqN _ t2Nx]] := FT_signalizer_context ell1x.
rewrite inE (negPf notFmaxN) /= => P2maxN /(_ M SMxM)[_ st2NsM _ hallMN].
pose r := pdiv #[x]; have pixr: r \in \pi(#[x]) by rewrite pi_pdiv order_gt1.
have t2Nr := pnatPpi t2Nx pixr; have sMr := st2NsM r t2Nr.
have [[PmaxN _] [_ s'N_MN _]] := (setDP P2maxN, and3P hallMN).
have [K hallK] := Hall_exists \kappa('N[x]) (sigma_compl_sol hallMN).
have [U hallU] := Hall_exists \kappa('N[x])^' (sigma_compl_sol hallMN).
have hallK_N := subHall_Hall hallMN (@kappa_sigma' _ _) hallK.
have [[sKMN kK _] [sUMN k'U _]] := (and3P hallK, and3P hallU).
have mulUK:  U * K = M :&: 'N[x].
  apply/eqP; rewrite eqEcard mulG_subG sUMN sKMN.
  rewrite coprime_cardMg ?(p'nat_coprime k'U) //= mulnC.
  by rewrite (card_Hall hallU) (card_Hall hallK) partnC ?cardG_gt0.
have complU: kappa_complement 'N[x] U K.
  split=> //; last by rewrite mulUK groupP.
  apply: (subHall_Hall hallMN) => [p|]; first by case/norP.
  rewrite pHallE sUMN /= (card_Hall hallU) eq_sym; apply/eqP.
  apply: eq_in_partn => p piMNp; rewrite inE /= negb_or /=.
  by rewrite [~~ _](pnatPpi s'N_MN).
have prK: prime #|K| by case/Ptype_structure: hallK_N => // _ _ _ _ [].
have ntK: K :!=: 1 by rewrite -cardG_gt1 prime_gt1.
have [maxN _] := setDP PmaxN.
have [defUK cUU regUK]: [/\ U ><| K = M :&: 'N[x], abelian U & 'C_U(K) = 1].
  have [_ defM _ regUK -> //] := kappa_compl_context maxN complU.
  have [[_ UK _ defUK] _ _ _] := sdprodP defM.
  by rewrite (cent_semiregular regUK) // defUK; case/sdprodP: defUK => _ <-.
have [[R sylR] [s'Nr rrN]] := (Sylow_exists r (M :&: 'N[x]), andP t2Nr).
have [[sRMN rR _] sylR_N] := (and3P sylR, subHall_Sylow hallMN s'Nr sylR).
have [nsUMN _ _ nUK _] := sdprod_context defUK.
have [[sRM sRN] [sKM _]] := (subsetIP sRMN, subsetIP sKMN).
have sRU: R \subset U.
  rewrite (sub_normal_Hall hallU nsUMN sRMN) (pi_pgroup rR) //.
  by apply: contraL rrN; move/rank_kappa->.
have sNRM: 'N(R) \subset M.
  apply: (norm_noncyclic_sigma maxM sMr rR sRM).
  rewrite (odd_pgroup_rank1_cyclic rR) ?mFT_odd //.
  by rewrite (p_rank_Sylow sylR_N) (eqnP rrN).
have sylR_U := pHall_subl sRU sUMN sylR.
have maxNRM: M \in 'M('N(R)) by rewrite inE maxM.
have [L maxCK_L] := mmax_exists (mFT_cent_proper ntK).
have FmaxM: M \in 'M_'F; last split=> //.
  by have [] := P2type_signalizer P2maxN complU maxCK_L sylR_U maxNRM.
have nilMs: nilpotent M`_\sigma by rewrite notP1type_Msigma_nil ?FmaxM.
have sMsF: M`_\sigma \subset 'F(M) by rewrite Fitting_max ?pcore_normal.
have defR: R :=: 'O_r(U) := nilpotent_Hall_pcore (abelian_nil cUU) sylR_U.
have nRK: K \subset 'N(R) by rewrite defR (char_norm_trans (pcore_char r U)).
have ntR: R :!=: 1.
  rewrite -rank_gt0 (rank_Sylow sylR_N) p_rank_gt0.
  by rewrite (partition_pi_mmax maxN) t2Nr !orbT.
have not_nilRK: ~~ nilpotent (R <*> K).
  apply: contra ntR => nilRK; rewrite -subG1 -regUK subsetI sRU.
  rewrite (sub_nilpotent_cent2 nilRK) ?joing_subl ?joing_subr //.
  by rewrite (coprimegS sRU) ?(pnat_coprime kK).
have{not_nilRK} not_sKMs: ~~ (K \subset M`_\sigma).
  apply: contra not_nilRK => sKMs; apply: nilpotentS nilMs.
  by rewrite join_subG (sub_Hall_pcore (Msigma_Hall maxM)) // (pi_pgroup rR).
have s'MK: \sigma(M)^'.-group K.
  rewrite /pgroup pnatE //; apply: contra not_sKMs; rewrite /= -pnatE // => sK.
  by rewrite (sub_Hall_pcore (Msigma_Hall maxM)).
have [E hallE sKE] := Hall_superset (mmax_sol maxM) sKM s'MK.
have [[E1 hallE1] [E3 hallE3]] := ex_tau13_compl hallE.
have [E2 hallE2 complEi] := ex_tau2_compl hallE hallE1 hallE3.
have [[_ t1E1 _] [sEM _]] := (and3P hallE1, andP hallE).
have E2_1: E2 :=: 1.
  have [sE2E t2E2 _] := and3P hallE2.
  rewrite -(setIidPl sE2E) coprime_TIg ?(pnat_coprime t2E2 (pgroupS sEM _)) //.
  apply: contraR ntR => not_t2'M.
  have:= tau2_P2type_signalizer P2maxN complU maxCK_L sylR_U maxNRM not_t2'M.
  case=> _ _ t2'N; rewrite -(setIidPl sRN) coprime_TIg //.
  by rewrite (pnat_coprime (pi_pgroup rR t2Nr)).
have E3_1: E3 :=: 1.
  have ntX: 'F(M) :&: 'F(M) :^ y != 1.
    apply/trivgPn; exists x; rewrite // inE mem_conjg !(subsetP sMsF) //.
    by rewrite /conjg invgK mulgA (cent1P cxy) mulgK.
  have [_ _ _ defE _] := nonTI_Fitting_structure maxM notMy ntX.
  by case/defE: complEi.
have [cycE defE]: cyclic E /\ E :=: E1.
  have [_ _ [cycE1 _] [<- _] _] := sigma_compl_context maxM complEi.
  by rewrite E2_1 E3_1 !sdprod1g.
have [ntMs ntE] := (Msigma_neq1 maxM, subG1_contra sKE ntK).
have defM := sdprod_sigma maxM hallE.
exists E => //; split=> //; apply/Frobenius_semiregularP=> // z Ez.
have{Ez} [ntz szE1] := setD1P Ez; rewrite defE -cycle_subG in szE1.
pose q := pdiv #[z]; have pizq: q \in \pi(#[z]) by rewrite pi_pdiv order_gt1.
have szM: <[z]> \subset M by rewrite (subset_trans _ sEM) ?defE.
have [_ k'M] := setIdP FmaxM; have k'q := pnatPpi k'M (piSg szM pizq).
have t1q := pnatPpi t1E1 (piSg szE1 pizq).
move: pizq; rewrite -p_rank_gt0 => /p_rank_geP[Z].
rewrite /= -(setIidPr szM) pnElemI -setIdE => /setIdP[EqZ sZz].
apply: contraNeq k'q => ntCMsx /=.
rewrite unlock 3!inE /= t1q; apply/exists_inP; exists Z => //.
by rewrite (subG1_contra _ ntCMsx) ?setIS //= -cent_cycle centS.
Qed.

End Section15.


