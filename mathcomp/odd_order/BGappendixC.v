(* (c) Copyright Microsoft Corporation and Inria. All rights reserved.        *)
Require Import ssreflect ssrbool ssrfun eqtype choice ssrnat seq div fintype.
Require Import tuple finfun bigop ssralg finset prime binomial poly polydiv.
Require Import fingroup morphism quotient automorphism action finalg zmodp.
Require Import gproduct cyclic commutator pgroup abelian frobenius BGsection1.
Require Import matrix mxalgebra mxabelem vector falgebra fieldext galois.
Require Import finfield ssrnum algC classfun character integral_char inertia.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory FinRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section AppendixC.

Variables (gT : finGroupType) (p q : nat) (H P P0 U Q : {group gT}).
Let nU := ((p ^ q).-1 %/ p.-1)%N.

(* External statement of the finite field assumption. *)
CoInductive finFieldImage : Prop :=
  FinFieldImage (F : finFieldType) (sigma : {morphism P >-> F}) of
     isom P [set: F] sigma & sigma @*^-1 <[1 : F]> = P0
   & exists2 sigmaU : {morphism U >-> {unit F}},
     'injm sigmaU & {in P & U, morph_act 'J 'U sigma sigmaU}.

(* These correspond to hypothesis (A) of B & G, Appendix C, Theorem C.        *)
Hypotheses (pr_p : prime p) (pr_q : prime q) (coUp1 : coprime nU p.-1).
Hypotheses (defH : P ><| U = H) (fieldH : finFieldImage).
Hypotheses (oP : #|P| = (p ^ q)%N) (oU : #|U| = nU).

(* These correspond to hypothesis (B) of B & G, Appendix C, Theorem C.        *)
Hypotheses (abelQ : q.-abelem Q) (nQP0 : P0 \subset 'N(Q)).
Hypothesis nU_P0Q : exists2 y, y \in Q & P0 :^ y \subset 'N(U).

Section ExpandHypotheses.

(* Negation of the goal of B & G, Appendix C, Theorem C.                      *)
Hypothesis ltqp : (q < p)%N.

(* From the fieldH assumption. *)
Variables (fT : finFieldType) (charFp : p \in [char fT]).
Local Notation F := (PrimeCharType charFp).
Local Notation galF := [splittingFieldType 'F_p of F].
Let Fpq : {vspace F} := fullv.
Let Fp : {vspace F} := 1%VS.

Hypothesis oF : #|F| = (p ^ q)%N.
Let oF_p : #|'F_p| = p. Proof. exact: card_Fp. Qed.
Let oFp : #|Fp| = p. Proof. by rewrite card_vspace1. Qed.
Let oFpq : #|Fpq| = (p ^ q)%N. Proof. by rewrite card_vspacef. Qed.
Let dimFpq : \dim Fpq = q. Proof. by rewrite primeChar_dimf oF pfactorK. Qed.

Variables (sigma : {morphism P >-> F}) (sigmaU : {morphism U >-> {unit F}}).
Hypotheses (inj_sigma : 'injm sigma) (inj_sigmaU : 'injm sigmaU).
Hypothesis im_sigma : sigma @* P = [set: F].
Variable s : gT.
Hypotheses (sP0P : P0 \subset P) (sigma_s : sigma s = 1) (defP0 : <[s]> = P0).

Let psi u : F := val (sigmaU u).
Let inj_psi : {in U &, injective psi}.
Proof. by move=> u v Uu Uv /val_inj/(injmP inj_sigmaU)->. Qed.

Hypothesis sigmaJ : {in P & U, forall x u, sigma (x ^ u) = sigma x * psi u}.

Let Ps : s \in P. Proof. by rewrite -cycle_subG defP0. Qed.
Let P0s : s \in P0. Proof. by rewrite -defP0 cycle_id. Qed.

Let nz_psi u : psi u != 0. Proof. by rewrite -unitfE (valP (sigmaU u)). Qed.

Let sigma1 : sigma 1%g = 0. Proof. exact: morph1. Qed.
Let sigmaM : {in P &, {morph sigma : x1 x2 / (x1 * x2)%g >-> x1 + x2}}.
Proof. exact: morphM. Qed.
Let sigmaV : {in P, {morph sigma : x / x^-1%g >-> - x}}.
Proof. exact: morphV. Qed.
Let sigmaX n : {in P, {morph sigma : x / (x ^+ n)%g >-> x *+ n}}.
Proof. exact: morphX. Qed.

Let psi1 : psi 1%g = 1. Proof. by rewrite /psi morph1. Qed.
Let psiM : {in U &, {morph psi : u1 u2 / (u1 * u2)%g >-> u1 * u2}}.
Proof. by move=> u1 u2 Uu1 Uu2; rewrite /psi morphM. Qed.
Let psiV : {in U, {morph psi : u / u^-1%g >-> u^-1}}.
Proof. by move=> u Uu; rewrite /psi morphV. Qed.
Let psiX n : {in U, {morph psi : u / (u ^+ n)%g >-> u ^+ n}}.
Proof. by move=> u Uu; rewrite /psi morphX // val_unitX. Qed.

Let sigmaE := (sigma1, sigma_s, mulr1, mul1r,
               (sigmaJ, sigmaX, sigmaM, sigmaV), (psi1, psiX, psiM, psiV)).

Let psiE u : u \in U -> psi u = sigma (s ^ u).
Proof. by move=> Uu; rewrite !sigmaE. Qed.

Let nPU : U \subset 'N(P). Proof. by have [] := sdprodP defH. Qed.
Let memJ_P : {in P & U, forall x u, x ^ u \in P}.
Proof. by move=> x u Px Uu; rewrite /= memJ_norm ?(subsetP nPU). Qed.
Let in_PU := (memJ_P, in_group).

Let sigmaP0 : sigma @* P0 =i Fp.
Proof.
rewrite -defP0 morphim_cycle // sigma_s => x.
apply/cycleP/vlineP=> [] [n ->]; first by exists n%:R; rewrite scaler_nat.
by exists (val n); rewrite -{1}[n]natr_Zp -in_algE rmorph_nat zmodXgE.
Qed.

Let nt_s : s != 1%g.
Proof. by rewrite -(morph_injm_eq1 inj_sigma) // sigmaE oner_eq0. Qed.

Let p_gt0 : (0 < p)%N. Proof. exact: prime_gt0. Qed.
Let q_gt0 : (0 < q)%N. Proof. exact: prime_gt0. Qed.
Let p1_gt0 : (0 < p.-1)%N. Proof. by rewrite -subn1 subn_gt0 prime_gt1. Qed.

(* This is B & G, Appendix C, Remark I. *)
Let not_dvd_q_p1 : ~~ (q %| p.-1)%N.
Proof.
rewrite -prime_coprime // -[q]card_ord -sum1_card -coprime_modl -modn_summ.
have:= coUp1; rewrite /nU predn_exp mulKn //= -coprime_modl -modn_summ.
congr (coprime (_ %% _) _); apply: eq_bigr => i _.
by rewrite -{1}[p](subnK p_gt0) subn1 -modnXm modnDl modnXm exp1n.
Qed.

(* This is the first assertion of B & G, Appendix C, Remark V. *)
Let odd_p : odd p.
Proof.
by apply: contraLR ltqp => /prime_oddPn-> //; rewrite -leqNgt prime_gt1.
Qed.

(* This is the second assertion of B & G, Appendix C, Remark V. *)
Let odd_q : odd q.
Proof.
apply: contraR not_dvd_q_p1 => /prime_oddPn-> //.
by rewrite -subn1 dvdn2 odd_sub ?odd_p.
Qed.

Let qgt2 : (2 < q)%N. Proof. by rewrite odd_prime_gt2. Qed.
Let pgt4 : (4 < p)%N. Proof. by rewrite odd_geq ?(leq_ltn_trans qgt2). Qed.
Let qgt1 : (1 < q)%N. Proof. exact: ltnW. Qed.

Local Notation Nm := (galNorm Fp Fpq).
Local Notation uval := (@FinRing.uval _).

Let cycFU (FU : {group {unit F}}) : cyclic FU.
Proof. exact: field_unit_group_cyclic. Qed.
Let cUU : abelian U.
Proof. by rewrite cyclic_abelian // -(injm_cyclic inj_sigmaU) ?cycFU. Qed.

(* This is B & G, Appendix C, Remark VII. *)
Let im_psi (x : F) : (x \in psi @: U) = (Nm x == 1).
Proof.
have /cyclicP[u0 defFU]: cyclic [set: {unit F}] by exact: cycFU.
have o_u0: #[u0] = (p ^ q).-1 by rewrite orderE -defFU card_finField_unit oF.
have ->: psi @: U = uval @: (sigmaU @* U) by rewrite morphimEdom -imset_comp.
have /set1P[->]: (sigmaU @* U)%G \in [set <[u0 ^+ (#[u0] %/ nU)]>%G].
  rewrite -cycle_sub_group ?inE; last first.
    by rewrite o_u0 -(divnK (dvdn_pred_predX p q)) dvdn_mulr.
  by rewrite -defFU subsetT card_injm //= oU.
rewrite divnA ?dvdn_pred_predX // -o_u0 mulKn //.
have [/= alpha alpha_gen Dalpha] := finField_galois_generator (subvf Fp).
have{Dalpha} Dalpha x1: x1 != 0 -> x1 / alpha x1 = x1^-1 ^+ p.-1.
  move=> nz_x1; rewrite -[_ ^+ _](mulVKf nz_x1) -exprS Dalpha ?memvf // exprVn.
  by rewrite dimv1 oF_p prednK ?prime_gt0.
apply/idP/(Hilbert's_theorem_90 alpha_gen (memvf _)) => [|[u [_ nz_u] ->]].
  case/imsetP=> /= _ /cycleP[n ->] ->; rewrite expgAC; set u := (u0 ^+ n)%g.
  have nz_u: (val u)^-1 != 0 by rewrite -unitfE unitrV (valP u).
  by exists (val u)^-1; rewrite ?memvf ?Dalpha //= invrK val_unitX.
have /cycleP[n Du]: (insubd u0 u)^-1%g \in <[u0]> by rewrite -defFU inE.
have{Du} Du: u^-1 = val (u0 ^+ n)%g by rewrite -Du /= insubdK ?unitfE.
by rewrite Dalpha // Du -val_unitX mem_imset // expgAC mem_cycle.
Qed.

(* This is B & G, Appendix C, Remark VIII. *)
Let defFU : sigmaU @* U \x [set u | uval u \in Fp] = [set: {unit F}].
Proof.
have fP v: in_alg F (uval v) \is a GRing.unit by rewrite rmorph_unit ?(valP v).
pose f (v : {unit 'F_p}) := FinRing.unit F (fP v).
have fM: {in setT &, {morph f: v1 v2 / (v1 * v2)%g}}.
  by move=> v1 v2 _ _; apply: val_inj; rewrite /= -in_algE rmorphM.
pose galFpU := Morphism fM @* [set: {unit 'F_p}].
have ->: [set u | uval u \in Fp] = galFpU.
  apply/setP=> u; rewrite inE /galFpU morphimEdom.
  apply/idP/imsetP=> [|[v _ ->]]; last by rewrite /= rpredZ // memv_line.
  case/vlineP=> v Du; have nz_v: v != 0.
    by apply: contraTneq (valP u) => v0; rewrite unitfE /= Du v0 scale0r eqxx.
  exists (insubd (1%g : {unit 'F_p}) v); rewrite ?inE //.
  by apply: val_inj; rewrite /= insubdK ?unitfE.
have oFpU: #|galFpU| = p.-1.
  rewrite card_injm ?card_finField_unit ?oF_p //.
  by apply/injmP=> v1 v2 _ _ []/(fmorph_inj [rmorphism of in_alg F])/val_inj.
have oUU: #|sigmaU @* U| = nU by rewrite card_injm.
rewrite dprodE ?coprime_TIg ?oUU ?oFpU //; last first.
  by rewrite (sub_abelian_cent2 (cyclic_abelian (cycFU [set: _]))) ?subsetT.
apply/eqP; rewrite eqEcard subsetT coprime_cardMg oUU oFpU //=.
by rewrite card_finField_unit oF divnK ?dvdn_pred_predX.
Qed.

(* This is B & G, Appendix C, Remark IX. *)
Let frobH : [Frobenius H = P ><| U].
Proof.
apply/Frobenius_semiregularP=> // [||u /setD1P[ntu Uu]].
- by rewrite -(morphim_injm_eq1 inj_sigma) // im_sigma finRing_nontrivial.
- rewrite -cardG_gt1 oU ltn_divRL ?dvdn_pred_predX // mul1n -!subn1.
  by rewrite ltn_sub2r ?(ltn_exp2l 0) ?(ltn_exp2l 1) ?prime_gt1.
apply/trivgP/subsetP=> x /setIP[Px /cent1P/commgP].
rewrite inE -!(morph_injm_eq1 inj_sigma) ?(sigmaE, in_PU) //.
rewrite -mulrN1 addrC -mulrDr mulf_eq0 subr_eq0 => /orP[] // /idPn[].
by rewrite (inj_eq val_inj (sigmaU u) 1%g) morph_injm_eq1.
Qed.

(* From the abelQ assumption of Peterfalvi, Theorem (14.2) to the assumptions *)
(* of part (B) of the assumptions of Theorem C.                               *)
Let p'q : q != p. Proof. by rewrite ltn_eqF. Qed.
Let cQQ : abelian Q. Proof. exact: abelem_abelian abelQ. Qed.
Let p'Q : p^'.-group Q. Proof. exact: pi_pgroup (abelem_pgroup abelQ) _. Qed.

Let pP : p.-group P. Proof. by rewrite /pgroup oP pnat_exp ?pnat_id. Qed.
Let coQP : coprime #|Q| #|P|. Proof. exact: p'nat_coprime p'Q pP. Qed.
Let sQP0Q : [~: Q, P0] \subset Q. Proof. by rewrite commg_subl. Qed.

(* This is B & G, Appendix C, Remark X. *)
Let defQ : 'C_Q(P0) \x [~: Q, P0] = Q.
Proof. by rewrite dprodC coprime_abelian_cent_dprod // (coprimegS sP0P). Qed.

(* This is B & G, Appendix C, Remark XI. *)
Let nU_P0QP0 : exists2 y, y \in [~: Q, P0] & P0 :^ y \subset 'N(U).
Proof.
have [_ /(mem_dprod defQ)[z [y [/setIP[_ cP0z] QP0y -> _]]]] := nU_P0Q.
by rewrite conjsgM (normsP (cent_sub P0)) //; exists y.
Qed.

Let E := [set x : galF | Nm x == 1 & Nm (2%:R - x) == 1].

Let E_1 : 1 \in E.
Proof. by rewrite !inE -addrA subrr addr0 galNorm1 eqxx. Qed.

(* This is B & G, Appendix C, Lemma C.1. *)
Let Einv_gt1_le_pq : E = [set x^-1 | x in E] -> (1 < #|E|)%N -> (p <= q)%N.
Proof.
rewrite (cardsD1 1) E_1 ltnS card_gt0 => Einv /set0Pn[/= a /setD1P[not_a1 Ea]].
pose tau (x : F) := (2%:R - x)^-1.
have Etau x: x \in E -> tau x \in E.
  rewrite inE => Ex; rewrite Einv (mem_imset (fun y => y^-1)) //.
  by rewrite inE andbC opprD addNKr opprK.
pose Pa := \prod_(beta in 'Gal(Fpq / Fp)) (beta (1 - a) *: 'X + 1).
have galPoly_roots: all (root (Pa - 1)) (enum Fp).
  apply/allP=> x; rewrite mem_enum => /vlineP[b ->].
  rewrite rootE !hornerE horner_prod subr_eq0 /=; apply/eqP.
  pose h k := (1 - a) *+ k + 1; transitivity (Nm (h b)).
    apply: eq_bigr => beta _; rewrite !(rmorphB, rmorphD, rmorphMn) rmorph1 /=.
    by rewrite -mulr_natr -scaler_nat natr_Zp hornerD hornerZ hornerX hornerC.
  elim: (b : nat) => [|k IHk]; first by rewrite /h add0r galNorm1.
  suffices{IHk}: h k / h k.+1 \in E.
    rewrite inE -invr_eq1 => /andP[/eqP <- _].
    by rewrite galNormM galNormV /= [galNorm _ _ (h k)]IHk mul1r invrK.
  elim: k => [|k IHk]; first by rewrite /h add0r mul1r addrAC Etau.
  have nz_hk1: h k.+1 != 0.
    apply: contraTneq IHk => ->; rewrite invr0 mulr0.
    by rewrite inE galNorm0 eq_sym oner_eq0.
  congr (_ \in E): (Etau _ IHk); apply: canLR (@invrK _) _; rewrite invfM invrK.
  apply: canRL (mulKf nz_hk1) _; rewrite mulrC mulrBl divfK // mulrDl mul1r.
  by rewrite {2}/h mulrS -2!addrA addrK addrAC -mulrSr.
have sizePa: size Pa = q.+1.
  have sizePaX (beta : {rmorphism F -> F}) : size (beta (1 - a) *: 'X + 1) = 2.
    rewrite -mul_polyC size_MXaddC oner_eq0 andbF size_polyC fmorph_eq0.
    by rewrite subr_eq0 eq_sym (negbTE not_a1).
  rewrite size_prod => [|i _]; last by rewrite -size_poly_eq0 sizePaX.
  rewrite (eq_bigr (fun _ => 2)) => [|beta _]; last by rewrite sizePaX.
  rewrite sum_nat_const muln2 -addnn -addSn addnK.
  by rewrite -galois_dim ?finField_galois ?subvf // dimv1 divn1 dimFpq.
have sizePa1: size (Pa - 1) = q.+1.
  by rewrite size_addl // size_opp size_poly1 sizePa.
have nz_Pa1 : Pa - 1 != 0 by rewrite -size_poly_eq0 sizePa1.
by rewrite -ltnS -oFp -sizePa1 cardE max_poly_roots ?enum_uniq.
Qed.

(* This is B & G, Appendix C, Lemma C.2. *)
Let E_gt1 : (1 < #|E|)%N.
Proof.
have [q_gt4 | q_le4] := ltnP 4 q.
  pose inK x := enum_rank_in (classes1 H) (x ^: H).
  have inK_E x: x \in H -> enum_val (inK x) = x ^: H.
    by move=> Hx; rewrite enum_rankK_in ?mem_classes. 
  pose j := inK s; pose k := inK (s ^+ 2)%g; pose e := gring_classM_coef j j k.
  have cPP: abelian P by rewrite -(injm_abelian inj_sigma) ?zmod_abelian.
  have Hs: s \in H by rewrite -(sdprodW defH) -[s]mulg1 mem_mulg.
  have DsH n: (s ^+ n) ^: H = (s ^+ n) ^: U.
    rewrite -(sdprodW defH) classM (abelian_classP _ cPP) ?groupX //.
    by rewrite class_support_set1l.
  have injJU: {in U &, injective (conjg s)}.
    by move=> u v Uu Uv eq_s_uv; apply/inj_psi; rewrite ?psiE ?eq_s_uv.
  have ->: #|E| = e.
    rewrite /e /gring_classM_coef !inK_E ?groupX //.
    transitivity #|[set u in U | s^-1 ^ u * s ^+ 2 \in s ^: U]%g|.
      rewrite -(card_in_imset (sub_in2 _ inj_psi)) => [|u /setIdP[] //].
      apply: eq_card => x; rewrite inE -!im_psi.
      apply/andP/imsetP=> [[/imsetP[u Uu ->] /imsetP[v Uv Dv]]{x} | ].
        exists u; rewrite // inE Uu /=; apply/imsetP; exists v => //.
        by apply: (injmP inj_sigma); rewrite ?(sigmaE, in_PU) // mulN1r addrC.
      case=> u /setIdP[Uu /imsetP[v Uv /(congr1 sigma)]].
      rewrite ?(sigmaE, in_PU) // mulN1r addrC => Dv ->.
      by rewrite Dv !mem_imset.
    rewrite DsH (DsH 1%N) expg1; have [w Uw ->] := repr_class U (s ^+ 2).
    pose f u := (s ^ (u * w), (s^-1 ^ u * s ^+ 2) ^ w).
    rewrite -(@card_in_imset _ _ f) => [|u v]; last first.
      by move=> /setIdP[Uu _] /setIdP[Uv _] [/injJU/mulIg-> //]; apply: groupM.
    apply: eq_card => [[x1 x2]]; rewrite inE -andbA.
    apply/imsetP/and3P=> [[u /setIdP[Uu sUs2u'] [-> ->]{x1 x2}] | []].
      rewrite /= conjgM -(rcoset_id Uw) class_rcoset !memJ_conjg mem_orbit //.
      by rewrite sUs2u' -conjMg conjVg mulKVg.
    case/imsetP=> u Uu /= -> sUx2 /eqP/(canRL (mulKg _)) Dx2.
    exists (u * w^-1)%g; last first.
      by rewrite /f /= conjMg -conjgM mulgKV conjVg -Dx2.
    rewrite inE !in_PU // Uw -(memJ_conjg _ w) -class_rcoset rcoset_id //.
    by rewrite conjMg -conjgM mulgKV conjVg -Dx2.
  pose chi_s2 i := 'chi[H]_i s ^+ 2 * ('chi_i (s ^+ 2)%g)^* / 'chi_i 1%g.
  have De: e%:R = #|U|%:R / #|P|%:R * (\sum_i chi_s2 i).
    have Ks: s \in enum_val j by rewrite inK_E ?class_refl.
    have Ks2: (s ^+ 2)%g \in enum_val k by rewrite inK_E ?groupX ?class_refl.
    rewrite (gring_classM_coef_sum_eq Ks Ks Ks2) inK_E //; congr (_ * _).
    have ->: #|s ^: H| = #|U| by rewrite (DsH 1%N) (card_in_imset injJU).
    by rewrite -(sdprod_card defH) mulnC !natrM invfM mulrA mulfK ?neq0CG.
  pose linH := [pred i | P \subset cfker 'chi[H]_i].
  have nsPH: P <| H by have [] := sdprod_context defH.
  have sum_linH: \sum_(i in linH) chi_s2 i = #|U|%:R.
    have isoU: U \isog H / P := sdprod_isog defH.
    have abHbar: abelian (H / P) by rewrite -(isog_abelian isoU).
    rewrite (card_isog isoU) -(card_Iirr_abelian abHbar) -sumr_const.
    rewrite (reindex _ (mod_Iirr_bij nsPH)) /chi_s2 /=.
    apply: eq_big => [i | i _]; rewrite ?mod_IirrE ?cfker_mod //.
    have lin_i: ('chi_i %% P)%CF \is a linear_char.
      exact/cfMod_lin_char/char_abelianP.
    rewrite lin_char1 // divr1 -lin_charX // -normCK.
    by rewrite normC_lin_char ?groupX ?expr1n.
  have degU i: i \notin linH -> 'chi_i 1%g = #|U|%:R.
    case/(Frobenius_Ind_irrP (FrobeniusWker frobH)) => {i}i _ ->.
    rewrite cfInd1 ?normal_sub // -(index_sdprod defH) lin_char1 ?mulr1 //.
    exact/char_abelianP.
  have ub_linH' m (s_m := (s ^+ m)%g):
    (0 < m < 5)%N -> \sum_(i in predC linH) `|'chi_i s_m| ^+ 2 <= #|P|%:R.
  - case/andP=> m_gt0 m_lt5; have{m_gt0 m_lt5} P1sm: s_m \in P^#.
      rewrite !inE groupX // -order_dvdn -(order_injm inj_sigma) // sigmaE.
      by rewrite andbT order_primeChar ?oner_neq0 ?gtnNdvd ?(leq_trans m_lt5).
    have ->: #|P| = (#|P| * (s_m \in s_m ^: H))%N by rewrite class_refl ?muln1.
    have{P1sm} /eqP <-: 'C_H[s ^+ m] == P.
      rewrite eqEsubset (Frobenius_cent1_ker frobH) // subsetI normal_sub //=.
      by rewrite sub_cent1 groupX // (subsetP cPP).
    rewrite mulrnA -second_orthogonality_relation ?groupX // big_mkcond.
    by apply: ler_sum => i _; rewrite normCK; case: ifP; rewrite ?mul_conjC_ge0.
  have sqrtP_gt0: 0 < sqrtC #|P|%:R by rewrite sqrtC_gt0 ?gt0CG.
  have{De ub_linH'}: `|(#|P| * e)%:R - #|U|%:R ^+ 2| <= #|P|%:R * sqrtC #|P|%:R.
    rewrite natrM De mulrCA mulrA divfK ?neq0CG // (bigID linH) /= sum_linH.
    rewrite mulrDr addrC addKr mulrC mulr_suml /chi_s2.
    rewrite (ler_trans (ler_norm_sum _ _ _)) // -ler_pdivr_mulr // mulr_suml.
    apply: ler_trans (ub_linH' 1%N isT); apply: ler_sum => i linH'i.
    rewrite ler_pdivr_mulr // degU ?divfK ?neq0CG //.
    rewrite normrM -normrX norm_conjC ler_wpmul2l ?normr_ge0 //.
    rewrite -ler_sqr ?qualifE ?normr_ge0 ?(@ltrW _ 0) // sqrtCK. 
    apply: ler_trans (ub_linH' 2 isT); rewrite (bigD1 i) ?ler_paddr //=.
    by apply: sumr_ge0 => i1 _; rewrite exprn_ge0 ?normr_ge0.
  rewrite natrM real_ler_distl ?rpredB ?rpredM ?rpred_nat // => /andP[lb_Pe _]. 
  rewrite -ltC_nat -(ltr_pmul2l (gt0CG P)) {lb_Pe}(ltr_le_trans _ lb_Pe) //.
  rewrite ltr_subr_addl (@ler_lt_trans _ ((p ^ q.-1)%:R ^+ 2)) //; last first.
    rewrite  -!natrX ltC_nat ltn_sqr oU ltn_divRL ?dvdn_pred_predX //.
    rewrite -(subnKC qgt1) /= -!subn1 mulnBr muln1 -expnSr.
    by rewrite ltn_sub2l ?(ltn_exp2l 0) // prime_gt1.
  rewrite -mulrDr -natrX -expnM muln2 -subn1 doubleB -addnn -addnBA // subn2.
  rewrite expnD natrM -oP ler_wpmul2l ?ler0n //.
  apply: ler_trans (_ : 2%:R * sqrtC #|P|%:R <= _).
    rewrite mulrDl mul1r ler_add2l -(@expr_ge1 _ 2) ?(ltrW sqrtP_gt0) // sqrtCK.
    by rewrite oP natrX expr_ge1 ?ler0n ?ler1n.
  rewrite -ler_sqr ?rpredM ?rpred_nat ?qualifE ?(ltrW sqrtP_gt0) //.
  rewrite exprMn sqrtCK -!natrX -natrM leC_nat -expnM muln2 oP.
  rewrite -(subnKC q_gt4) doubleS (expnS p _.*2.+1) -(subnKC pgt4) leq_mul //.
  by rewrite ?leq_exp2l // !doubleS !ltnS -addnn leq_addl.
have q3: q = 3 by apply/eqP; rewrite eqn_leq qgt2 andbT -ltnS -(odd_ltn 5).
rewrite (cardsD1 1) E_1 ltnS card_gt0; apply/set0Pn => /=.
pose f (c : 'F_p) : {poly 'F_p} := 'X * ('X - 2%:R%:P) * ('X - c%:P) + ('X - 1).
have fc0 c: (f c).[0] = -1 by rewrite !hornerE.
have fc2 c: (f c).[2%:R] = 1 by rewrite !(subrr, hornerE) /= addrK.
have /existsP[c nz_fc]: [exists c, ~~ [exists d, root (f c) d]].
  have nz_f_0 c: ~~ root (f c) 0 by rewrite /root fc0 oppr_eq0.
  rewrite -negb_forall; apply/negP=> /'forall_existsP/fin_all_exists[/= rf rfP].
  suffices inj_rf: injective rf.
    by have /negP[] := nz_f_0 (invF inj_rf 0); rewrite -{2}[0](f_invF inj_rf).
  move=> a b eq_rf_ab; apply/oppr_inj/(addrI (rf a)).
  have: (f a).[rf a] = (f b).[rf a] by rewrite {2}eq_rf_ab !(rootP _).
  rewrite !(hornerXsubC, hornerD, hornerM) hornerX => /addIr/mulfI-> //.
  rewrite mulf_neq0 ?subr_eq0 1?(contraTneq _ (rfP a)) // => -> //.
  by rewrite /root fc2.
have{nz_fc} /= nz_fc: ~~ root (f c) _ by apply/forallP; rewrite -negb_exists.
have sz_fc_lhs: size ('X * ('X - 2%:R%:P) * ('X - c%:P)) = 4.
  by rewrite !(size_mul, =^~ size_poly_eq0) ?size_polyX ?size_XsubC.
have sz_fc: size (f c) = 4 by rewrite size_addl ?size_XsubC sz_fc_lhs.
have irr_fc: irreducible_poly (f c) by apply: cubic_irreducible; rewrite ?sz_fc.
have fc_monic : f c \is monic.
  rewrite monicE lead_coefDl ?size_XsubC ?sz_fc_lhs // -monicE.
  by rewrite !monicMl ?monicXsubC ?monicX.
pose inF := [rmorphism of in_alg F]; pose fcF := map_poly inF (f c).
have /existsP[a fcFa_0]: [exists a : F, root fcF a].
  suffices: ~~ coprimep (f c) ('X ^+ #|F| - 'X).
    apply: contraR; rewrite -(coprimep_map inF) negb_exists => /forallP-nz_fcF.
    rewrite -/fcF rmorphB rmorphX /= map_polyX finField_genPoly.
    elim/big_rec: _ => [|x gF _ co_fcFg]; first exact: coprimep1.
    by rewrite coprimep_mulr coprimep_XsubC nz_fcF.
  have /irredp_FAdjoin[L dimL [z /coprimep_root fcz0 _]] := irr_fc.
  pose finL := [vectType 'F_p of FinFieldExtType L].
  set fcL := map_poly _ _ in fcz0; pose inL := [rmorphism of in_alg L].
  rewrite -(coprimep_map inL) -/fcL rmorphB rmorphX /= map_polyX.
  apply: contraL (fcz0 _) _; rewrite hornerD hornerN hornerXn hornerX subr_eq0.
  have ->: #|F| = #|{: finL}%VS| by rewrite oF card_vspace dimL sz_fc oF_p q3.
  by rewrite card_vspacef (expf_card (z : finL)).
have Fp_fcF: fcF \is a polyOver Fp.
  by apply/polyOverP => i; rewrite coef_map /= memvZ ?memv_line.
pose G := 'Gal(Fpq / Fp).
have galG: galois Fp Fpq by rewrite finField_galois ?subvf.
have oG: #|G| = 3 by rewrite -galois_dim // dimv1 dimFpq q3.
have Fp'a: a \notin Fp.
  by apply: contraL fcFa_0 => /vlineP[d ->]; rewrite fmorph_root.
have DfcF: fcF = \prod_(beta in G) ('X - (beta a)%:P).
  pose Pa : {poly F} := minPoly Fp a.
  have /eqP szPa: size Pa == 4.
    rewrite size_minPoly eqSS.
    rewrite (sameP eqP (prime_nt_dvdP _ _)) ?adjoin_deg_eq1 //.
    by rewrite adjoin_degreeE dimv1 divn1 -q3 -dimFpq field_dimS ?subvf.
  have dvd_Pa_fcF: Pa %| fcF by apply: minPoly_dvdp fcFa_0.
  have{dvd_Pa_fcF} /eqP <-: Pa == fcF.
    rewrite -eqp_monic ?monic_minPoly ?monic_map // -dvdp_size_eqp //.
    by rewrite szPa size_map_poly sz_fc.
  have [r [srG /map_uniq Ur defPa]]:= galois_factors (subvf _) galG a (memvf a).
  rewrite -/Pa big_map in defPa; rewrite defPa big_uniq //=.
  apply/eq_bigl/subset_cardP=> //; apply/eqP.
  by rewrite -eqSS (card_uniqP Ur) oG -szPa defPa size_prod_XsubC.
exists a; rewrite !inE; apply/and3P; split.
- by apply: contraNneq Fp'a => ->; apply: mem1v.
- apply/eqP; transitivity ((- 1) ^+ #|G| * fcF.[inF 0]).
    rewrite DfcF horner_prod -prodrN; apply: eq_bigr => beta _.
    by rewrite rmorph0 hornerXsubC add0r opprK.
  by rewrite -signr_odd mulr_sign oG horner_map fc0 rmorphN1 opprK.
apply/eqP; transitivity (fcF.[inF 2%:R]); last by rewrite horner_map fc2 rmorph1.
rewrite DfcF horner_prod; apply: eq_bigr => beta _.
by rewrite hornerXsubC rmorphB !rmorph_nat.
Qed.

Section AppendixC3.

Import GroupScope.

Variables y : gT.
Hypotheses (QP0y : y \in [~: Q, P0]) (nUP0y : P0 :^ y \subset 'N(U)).
Let Qy : y \in Q. Proof. by rewrite (subsetP sQP0Q). Qed.

Let t := s ^ y.
Let P1 := P0 :^ y.

(* This is B & G, Appendix C, Lemma C.3, Step 1. *)
Let splitH x :
     x \in H ->
  exists2 u, u \in U & exists2 v, v \in U & exists2 s1, s1 \in P0
  & x = u * s1 * v.
Proof.
case/(mem_sdprod defH) => z [v [Pz Uv -> _]].
have [-> | nt_z] := eqVneq z 1.
  by exists 1 => //; exists v => //; exists 1; rewrite ?mulg1.
have nz_z: sigma z != 0 by rewrite (morph_injm_eq1 inj_sigma).
have /(mem_dprod defFU)[]: finField_unit nz_z \in setT := in_setT _.
move=> _ [w [/morphimP[u Uu _ ->] Fp_w /(congr1 val)/= Dz _]].
have{Fp_w Dz} [n Dz]: exists n, sigma z = sigma ((s ^+ n) ^ u).
  move: Fp_w; rewrite {}Dz inE => /vlineP[n ->]; exists n.
  by rewrite -{1}(natr_Zp n) scaler_nat mulr_natr conjXg !sigmaE ?in_PU.
exists u^-1; last exists (u * v); rewrite ?groupV ?groupM //.
exists (s ^+ n); rewrite ?groupX // mulgA; congr (_ * _).
by apply: (injmP inj_sigma); rewrite -?mulgA ?in_PU.
Qed.

(* This is B & G, Appendix C, Lemma C.3, Step 2. *)
Let not_splitU s1 s2 u :
  s1 \in P0 -> s2 \in P0 -> u \in U -> s1 * u * s2 \in U ->
  (s1 == 1) && (s2 == 1) || (u == 1) && (s1 * s2 == 1).
Proof.
move=> P0s1 P0s2 Uu; have [_ _ _ tiPU] := sdprodP defH.
have [Ps1 Ps2]: s1 \in P /\ s2 \in P by rewrite !(subsetP sP0P).
have [-> | nt_s1 /=] := altP (s1 =P 1).
  by rewrite mul1g groupMl // -in_set1 -set1gE -tiPU inE Ps2 => ->.
have [-> | nt_u /=] := altP (u =P 1).
  by rewrite mulg1 -in_set1 -set1gE -tiPU inE (groupM Ps1).
rewrite (conjgC _ u) -mulgA groupMl // => Us12; case/negP: nt_u.
rewrite -(morph_injm_eq1 inj_sigmaU) // -in_set1 -set1gE.
have [_ _ _ <-] := dprodP defFU; rewrite !inE mem_morphim //= -/(psi u).
have{Us12}: s1 ^ u * s2 == 1.
  by rewrite -in_set1 -set1gE -tiPU inE Us12 andbT !in_PU.
rewrite -(morph_injm_eq1 inj_sigma) ?(in_PU, sigmaE) // addr_eq0.
move/eqP/(canRL (mulKf _))->; rewrite ?morph_injm_eq1 //.
by rewrite mulrC rpred_div ?rpredN //= -sigmaP0 mem_morphim.
Qed.

(* This is B & G, Appendix C, Lemma C.3, Step 3. *)
Let tiH_P1 t1 : t1 \in P1^# -> H :&: H :^ t1 = U.
Proof.
case/setD1P=>[nt_t1 P1t1]; set X := H :&: _.
have [nsPH sUH _ _ tiPU] := sdprod_context defH.
have sUX: U \subset X.
  by rewrite subsetI sUH -(normsP nUP0y t1 P1t1) conjSg.
have defX: (P :&: X) * U = X.
  by rewrite setIC group_modr // (sdprodW defH) setIAC setIid.
have [tiPX | ntPX] := eqVneq (P :&: X) 1; first by rewrite -defX tiPX mul1g.
have irrPU: acts_irreducibly U P 'J.
  apply/mingroupP; (split=> [|V /andP[ntV]]; rewrite astabsJ) => [|nVU sVP].
    by have [_ ->] := Frobenius_context frobH.
  apply/eqP; rewrite eqEsubset sVP; apply/subsetP=> x Px.
  have [-> // | ntx] := eqVneq x 1.
  have [z Vz ntz] := trivgPn _ ntV; have Pz := subsetP sVP z Vz.
  have nz_z: sigma z != 0%R by rewrite morph_injm_eq1.
  have uP: (sigma x / sigma z)%R \is a GRing.unit.
    by rewrite unitfE mulf_neq0 ?invr_eq0 ?morph_injm_eq1.
  have: FinRing.unit F uP \in setT := in_setT _.
  case/(mem_dprod defFU)=> _ [s1 [/morphimP[u Uu _ ->]]].
  rewrite inE => /vlineP[n Ds1] /(congr1 val)/= Dx _.
  suffices ->: x = (z ^ u) ^+ n by rewrite groupX ?memJ_norm ?(subsetP nVU).
  apply: (injmP inj_sigma); rewrite ?(in_PU, sigmaE) //.
  by rewrite -mulr_natr -scaler_nat natr_Zp -Ds1 -mulrA -Dx mulrC divfK.
have{ntPX defX irrPU} defX: X :=: H.
  rewrite -(sdprodW defH) -defX; congr (_ * _).
  have [_ -> //] := mingroupP irrPU; rewrite ?subsetIl //= -/X astabsJ ntPX.
  by rewrite normsI // normsG.
have nHt1: t1 \in 'N(H) by rewrite -groupV inE sub_conjgV; apply/setIidPl.
have oP0: #|P0| = p by rewrite -(card_injm inj_sigma) // (eq_card sigmaP0) oFp.
have{nHt1} nHP1: P1 \subset 'N(H).
  apply: prime_meetG; first by rewrite cardJg oP0.
  by apply/trivgPn; exists t1; rewrite // inE P1t1.
have{nHP1} nPP1: P1 \subset 'N(P).
  have /Hall_pi hallP: Hall H P by apply: Frobenius_ker_Hall frobH.
  by rewrite -(normal_Hall_pcore hallP nsPH) (char_norm_trans (pcore_char _ _)).
have sylP0: p.-Sylow(Q <*> P0) P0.
  rewrite /pHall -divgS joing_subr ?(pgroupS sP0P) //=.
  by rewrite norm_joinEr // coprime_cardMg ?(coprimegS sP0P) ?mulnK.
have sP1QP0: P1 \subset Q <*> P0.
  by rewrite conj_subG ?joing_subr ?mem_gen // inE Qy.
have nP10: P1 \subset 'N(P0).
  have: P1 \subset 'N(P :&: (Q <*> P0)) by rewrite normsI // normsG.
  by rewrite norm_joinEr // -group_modr // setIC coprime_TIg // mul1g.
have eqP10: P1 :=: P0.
  apply/eqP; rewrite eqEcard cardJg leqnn andbT.
  rewrite (comm_sub_max_pgroup (Hall_max sylP0)) //; last exact: normC.
  by rewrite pgroupJ (pHall_pgroup sylP0).
have /idPn[] := prime_gt1 pr_p.
rewrite -oP0 cardG_gt1 negbK -subG1 -(Frobenius_trivg_cent frobH) subsetI sP0P.
apply/commG1P/trivgP; rewrite -tiPU commg_subI // subsetI ?subxx //.
by rewrite sP0P -eqP10.
Qed.

(* This is B & G, Appendix C, Lemma C.3, Step 4. *)
Fact BGappendixC3_Ediv : E = [set x^-1 | x in E]%R.
Proof.
suffices sEV_E: [set x^-1 | x in E]%R \subset E.
  by apply/esym/eqP; rewrite eqEcard sEV_E card_imset //=; apply: invr_inj.
have /mulG_sub[/(subset_trans sP0P)/subsetP sP0H /subsetP sUH] := sdprodW defH.
have Hs := sP0H s P0s; have P1t: t \in P1 by rewrite memJ_conjg.
have nUP1 t1: t1 \in P1 -> U :^ t1 = U by move/(subsetP nUP0y)/normP.
have nUtn n u: u \in U -> u ^ (t ^+ n) \in U.
  by rewrite -mem_conjgV nUP1 ?groupV ?groupX.
have nUtVn n u: u \in U -> u ^ (t ^- n) \in U.
  by rewrite -mem_conjg nUP1 ?groupX.
have Qsti i: s ^- i * t ^+ i \in Q.
  by rewrite -conjXg -commgEl (subsetP sQP0Q) // commGC mem_commg ?groupX.
pose is_sUs m a j n u s1 v :=
  [/\ a \in U, u \in U, v \in U, s1 \in P0
    & s ^+ m * a ^ t ^+ j * s ^- n = u * s1 * v].
have split_sUs m a j n:
  a \in U -> exists u, exists s1, exists v, is_sUs m a j n u s1 v.
- move=> Ua; suffices: s ^+ m * a ^ t ^+ j * s ^- n \in H.
    by case/splitH=> u Uu [v Uv [s1 P0s1 Dusv1]]; exists u, s1, v.
  by rewrite 2?groupM ?groupV ?groupX // sUH ?nUtn.
have nt_sUs m j n a u s1 v:
  (m == n.+1) || (n == m.+1) -> is_sUs m a j n u s1 v -> s1 != 1.
- move/pred2P=> Dmn [Ua Uu Uv _ Dusv]; have{Dmn}: s ^+ m != s ^+ n.
    by case: Dmn => ->; last rewrite eq_sym; rewrite expgS eq_mulgV1 ?mulgK.
  apply: contraNneq => s1_1; rewrite {s1}s1_1 mulg1 in Dusv.
  have:= groupM Uu Uv; rewrite -Dusv => /(not_splitU _ _ (nUtn j a Ua))/orP.
  by rewrite !in_group // eq_invg1 -eq_mulgV1 => -[]// /andP[? /eqP->].
have sUs_modP m a j n u s1 v: is_sUs m a j n u s1 v -> a ^ t ^+ j = u * v.
  have [nUP /isom_inj/injmP/=quoUP_inj] := sdprod_isom defH.
  case=> Ua Uu Uv P0s1 /(congr1 (coset P)); rewrite (conjgCV u) -(mulgA _ u).
  rewrite coset_kerr ?groupV 2?coset_kerl ?groupX //; last first.
    by rewrite -mem_conjg (normsP nUP) // (subsetP sP0P).
  by move/quoUP_inj->; rewrite ?nUtn ?groupM.
have expUMp u v Uu Uv := expgMn p (centsP cUU u v Uu Uv).
have sUsXp m a j n u s1 v:
  is_sUs m a j n u s1 v -> is_sUs m (a ^+ p) j n (u ^+ p) s1 (v ^+ p).
- move=> Dusv; have{Dusv} [/sUs_modP Duv [Ua Uu Vv P0s1 Dusv]] := (Dusv, Dusv).
  split; rewrite ?groupX //; move: P0s1 Dusv; rewrite -defP0 => /cycleP[k ->].
  rewrite conjXg -!(mulgA _ (s ^+ k)) ![s ^+ k * _]conjgC 2!mulgA -expUMp //.
  rewrite {}Duv ![s ^+ m * _]conjgC !conjXg -![_ * _ * s ^- n]mulgA.
  move/mulgI/(congr1 (Frobenius_aut charFp \o sigma))=> /= Duv_p.
  congr (_ * _); apply/(injmP inj_sigma); rewrite ?in_PU //.
  by rewrite !{1}sigmaE ?in_PU // rmorphB !rmorphMn rmorph1 in Duv_p *.
have odd_P: odd #|P| by rewrite oP odd_exp odd_p orbT.
suffices EpsiV a: a \in U -> psi a \in E -> psi (a^-1 ^ t ^+ 3) \in E.
  apply/subsetP => _ /imsetP[x Ex ->].
  have /imsetP[a Ua Dx]: x \in psi @: U by rewrite im_psi; case/setIdP: Ex.
  suffices: psi (a^-1 ^ t ^+ (3 * #|P|)) \in E.
    rewrite Dx -psiV // -{2}(conjg1 a^-1); congr (psi (_ ^ _) \in E).
    by apply/eqP; rewrite -order_dvdn orderJ dvdn_mull ?order_dvdG.
  rewrite -(odd_double_half #|P|) odd_P addnC.
  elim: _./2 => [|n /EpsiV/EpsiV/=]; first by rewrite EpsiV -?Dx.
  by rewrite conjVg invgK -!conjgM -!expgD -!mulnSr !(groupV, nUtn) //; apply.
move=> Ua Ea; have{Ea} [b Ub Dab]: exists2 b, b \in U & psi a + psi b = 2%:R.
  case/setIdP: Ea => _; rewrite -im_psi => /imsetP[b Ub Db]; exists b => //.
  by rewrite -Db addrC subrK.
(* In the book k is arbitrary in Fp; however only k := 3 is used. *)
have [u2 [s2 [v2 usv2P]]] := split_sUs 3 (a * _) 2 1%N (groupM Ua (groupVr Ub)).
have{Ua} [u1 [s1 [v1 usv1P]]] := split_sUs 1%N a^-1 3 2 (groupVr Ua).
have{Ub} [u3 [s3 [v3 usv3P]]] := split_sUs 2 b 1%N 3 Ub.
pose s2def w1 w2 w3 := t * s2^-1 * t = w1 * s3 * w2 * t ^+ 2 * s1 * w3.
pose w1 := v2 ^ t^-1 * u3; pose w2 := v3 * u1 ^ t ^- 2; pose w3 := v1 * u2 ^ t.
have stXC m n: (m <= n)%N -> s ^- n ^ t ^+ m = s ^- m ^ t ^+ n * s ^- (n - m).
  move/subnK=> Dn; apply/(mulgI (s ^- (n - m) * t ^+ n))/(mulIg (t ^+ (n - m))).
  rewrite -{1}[in t ^+ n]Dn expgD !mulgA !mulgK -invMg -2!mulgA -!expgD.
  by rewrite addnC Dn (centsP (abelem_abelian abelQ)) ?mulgA.
wlog suffices Ds2: a b u1 v1 u2 v2 u3 v3 @w1 @w2 @w3 Dab usv1P usv2P usv3P /
  s2def w1 w2 w3; last first.
- apply/esym; rewrite -[_ * t]mulgA [_ * t]conjgC mulgA -(expgS _ 1) conjVg.
  rewrite /w2 mulgA; apply: (canRL (mulKVg _)); rewrite 2!mulgA -conjgE.
  rewrite conjMg conjgKV /w3 mulgA; apply: (canLR (mulgKV _)).
  rewrite /w1 -4!mulgA (mulgA u1) (mulgA u3) conjMg -conjgM mulKg -mulgA.
  have [[[Ua _ _ _ <-] [_ _ _ _ Ds2]] [Ub _ _ _ <-]] := (usv1P, usv2P, usv3P).
  apply: (canLR (mulKVg _)); rewrite -!invMg -!conjMg -{}Ds2 groupV in Ua *.
  rewrite -[t]expg1 2!conjMg -conjgM -expgS 2!conjMg -conjgM -expgSr mulgA.
  apply: (canLR (mulgK _)); rewrite 2!invMg -!conjVg invgK invMg invgK -4!mulgA.
  rewrite (mulgA _ s) stXC // mulgKV -!conjMg stXC // mulgKV -conjMg conjgM.
  apply: (canLR (mulKVg _)); rewrite -2!conjVg 2!mulgA -conjMg (stXC 1%N) //.
  rewrite mulgKV -conjgM -expgSr -mulgA -!conjMg; congr (_ ^ t ^+ 3).
  apply/(canLR (mulKVg _))/(canLR (mulgK _))/(canLR invgK).
  rewrite -!mulgA (mulgA _ b) mulgA invMg -!conjVg !invgK.
  by apply/(injmP inj_sigma); rewrite 1?groupM ?sigmaE ?memJ_P.
have [[Ua Uu1 Uv1 P0s1 Dusv1] /sUs_modP-Duv1] := (usv1P, usv1P).
have [[_ Uu2 Uv2 P0s2 _] [Ub Uu3 Uv3 P0s3 _]] := (usv2P, usv3P).
suffices /(congr1 sigma): s ^+ 2 = s ^ v1 * s ^ a^-1 ^ t ^+ 3.
  rewrite inE sigmaX // sigma_s sigmaM ?memJ_P -?psiE ?nUtn // => ->.
  by rewrite addrK -!im_psi !mem_imset ?nUtn.
rewrite groupV in Ua; have [Hs1 Hs3]: s1 \in H /\ s3 \in H by rewrite !sP0H.
have nt_s1: s1 != 1 by apply: nt_sUs usv1P.
have nt_s3: s3 != 1 by apply: nt_sUs usv3P.
have{sUsXp} Ds2p: s2def (w1 ^+ p) (w2 ^+ p) (w3 ^+ p).
  have [/sUsXp-usv1pP /sUsXp-usv2pP /sUsXp-usv3pP] := And3 usv1P usv2P usv3P.
  rewrite expUMp ?groupV // !expgVn in usv1pP usv2pP.
  rewrite !(=^~ conjXg _ _ p, expUMp) ?groupV -1?[t]expg1 ?nUtn ?nUtVn //.
  apply: Ds2 usv1pP usv2pP usv3pP => //.
  by rewrite !psiX // -!Frobenius_autE -rmorphD Dab rmorph_nat.
have{Ds2} Ds2: s2def w1 w2 w3 by apply: Ds2 usv1P usv2P usv3P.
wlog [Uw1 Uw2 Uw3]: w1 w2 w3 Ds2p Ds2 / [/\ w1 \in U, w2 \in U & w3 \in U].
  by move/(_ w1 w2 w3)->; rewrite ?(nUtVn, nUtVn 1%N, nUtn 1%N, in_group).
have{Ds2p} Dw3p: (w2 ^- p * w1 ^- p.-1 ^ s3 * w2) ^ t ^+ 2 = w3 ^+ p.-1 ^ s1^-1.
  rewrite -[w1 ^+ _](mulKg w1) -[w3 ^+ _](mulgK w3) -expgS -expgSr !prednK //.
  rewrite -(canLR (mulKg _) Ds2p) -(canLR (mulKg _) Ds2) 6!invMg !invgK.
  by rewrite mulgA mulgK [2]lock /conjg !mulgA mulVg mul1g mulgK.
have w_id w: w \in U -> w ^+ p.-1 == 1 -> w = 1.
  by move=> Uw /eqP/(canRL_in (expgK _) Uw)->; rewrite ?expg1n ?oU.
have{Uw3} Dw3: w3 = 1.
  apply: w_id => //; have:= @not_splitU s1^-1^-1 s1^-1 (w3 ^+ p.-1).
  rewrite !groupV mulVg eqxx andbT {2}invgK (negPf nt_s1) groupX //= => -> //.
  have /tiH_P1 <-: t ^+ 2 \in P1^#.
    rewrite 2!inE groupX // andbT -order_dvdn gtnNdvd // orderJ.
    by rewrite odd_gt2 ?order_gt1 // orderE defP0 (oddSg sP0P).
  by rewrite -mulgA -conjgE inE -{2}Dw3p memJ_conjg !in_group ?Hs1 // sUH.
have{Dw3p} Dw2p: w2 ^+ p.-1 = w1 ^- p.-1 ^ s3.
  apply/(mulIg w2)/eqP; rewrite -expgSr prednK // eq_mulVg1 mulgA.
  by rewrite (canRL (conjgK _) Dw3p) Dw3 expg1n !conj1g.
have{Uw1} Dw1: w1 = 1.
  apply: w_id => //; have:= @not_splitU s3^-1 s3 (w1 ^- p.-1).
  rewrite mulVg (negPf nt_s3) andbF -mulgA -conjgE -Dw2p !in_group //=.
  by rewrite eqxx andbT eq_invg1 /= => ->.
have{w1 w2 w3 Dw1 Dw3 w_id Uw2 Dw2p Ds2} Ds2: t * s2^-1 * t = s3 * t ^+ 2 * s1.
  by rewrite Ds2 Dw3 [w2]w_id ?mulg1 ?Dw2p ?Dw1 ?mul1g // expg1n invg1 conj1g.
have /centsP abP0: abelian P0 by rewrite -defP0 cycle_abelian.
have QP0ys := memJ_norm y (subsetP (commg_normr P0 Q) _ _).
have{QP0ys} memQP0 := (QP0ys, groupV, groupM); have nQ_P0 := subsetP nQP0.
have sQP0_Q: [~: Q, P0] \subset Q by rewrite commg_subl.
have /centsP abQP0 := abelianS sQP0_Q (abelem_abelian abelQ).
have{s2def} Ds312: s3 * s1 * s2 = 1.
  apply/set1P; rewrite -set1gE -(coprime_TIg coQP) inE.
  rewrite coset_idr ?(subsetP sP0P) ?nQ_P0 ?groupM //.
  rewrite -mulgA -[s2](mulgK s) [_ * s]abP0 // -[s2](mulKVg s).
  rewrite -!mulgA [s * _]mulgA [s1 * _]mulgA [s1 * _]abP0 ?groupM //.
  rewrite 2!(mulgA s3) [s^-1 * _]mulgA !(morphM, morphV) ?nQ_P0 ?in_group //=.
  have ->: coset Q s = coset Q t by rewrite coset_kerl ?groupV ?coset_kerr.
  have nQt: t \in 'N(Q) by rewrite -(conjGid Qy) normJ memJ_conjg nQ_P0.
  rewrite -morphV // -!morphM ?(nQt, groupM) ?groupV // ?nQ_P0 //= -Ds2.
  by rewrite 2!mulgA mulgK mulgKV mulgV morph1.
pose x := (y ^ s3)^-1 * y ^ s^-1 * (y ^ (s * s1)^-1)^-1 * y.
have{abP0} Dx: x ^ s^-1 = x.
  rewrite 3!conjMg !conjVg -!conjgM -!invMg (mulgA s) -(expgS _ 1).
  rewrite [x]abQP0 ?memQP0 // [rhs in y * rhs]abQP0 ?memQP0 //.
  apply/(canRL (mulKVg _)); rewrite 4!mulgA; congr (_ * _).
  rewrite [RHS]abQP0 ?memQP0 //; apply/(canRL (mulgK _))/eqP.
  rewrite -3!mulgA [rhs in y^-1 * rhs]abQP0 ?memQP0 // -eq_invg_sym eq_invg_mul.
  apply/eqP; transitivity (t ^+ 2 * s1 * (t^-1 * s2 * t^-1) * s3); last first.
    by rewrite -[s2]invgK -!invMg mulgA Ds2 -(mulgA s3) invMg mulKVg mulVg.
  rewrite (canRL (mulKg _) Ds312) -2![_ * t^-1]mulgA.
  have Dt1 si: si \in P0 -> t^-1 = (s^-1 ^ si) ^ y.
    by move=> P0si; rewrite {2}/conjg -conjVg -(abP0 si) ?groupV ?mulKg.
  by rewrite {1}(Dt1 s1) // (Dt1 s3^-1) ?groupV // -conjXg /conjg !{1}gnorm.
have{Dx memQP0} Dx1: x = 1.
  apply/set1P; rewrite -set1gE; have [_ _ _ <-] := dprodP defQ.
  rewrite setIAC (setIidPr sQP0_Q) inE -{2}defP0 -cycleV cent_cycle.
  by rewrite (sameP cent1P commgP) commgEl Dx mulVg eqxx !memQP0.
pose t1 := s1 ^ y; pose t3 := s3 ^ y.
have{x Dx1} Ds13: s1 * (t * t1)^-1 = (t3 * t)^-1 * s3.
  by apply/eqP; rewrite eq_sym eq_mulVg1 invMg invgK -Dx1 /x /conjg !gnorm.
suffices Ds1: s1 = s^-1.
  rewrite -(canLR (mulKg _) (canRL (mulgKV _) Dusv1)) Ds1 Duv1.
  by rewrite !invMg invgK /conjg !gnorm.
have [_ _ /trivgPn[u Uu nt_u] _ _] := Frobenius_context frobH.
apply: (conjg_inj y); apply: contraNeq nt_u.
rewrite -/t1 conjVg -/t eq_mulVg1 -invMg => nt_tt1.
have Hu := sUH u Uu; have P1tt1: t * t1 \in P1 by rewrite groupM ?memJ_conjg.
have /tiH_P1 defU: (t * t1)^-1 \in P1^# by rewrite 2!inE nt_tt1 groupV.
suffices: (u ^ s1) ^ (t * t1)^-1 \in U.
  rewrite -mem_conjg nUP1 // conjgE mulgA => /(not_splitU _ _ Uu).
  by rewrite groupV (negPf nt_s1) andbF mulVg eqxx andbT /= => /(_ _ _)/eqP->.
rewrite -defU inE memJ_conjg -conjgM Ds13 conjgM groupJ ?(groupJ _ Hs1) //.
by rewrite sUH // -mem_conjg nUP1 // groupM ?memJ_conjg.
Qed.

End AppendixC3.

Fact BGappendixC_inner_subproof : (p <= q)%N.
Proof.
have [y QP0y nUP0y] := nU_P0QP0.
by apply: Einv_gt1_le_pq E_gt1; apply: BGappendixC3_Ediv nUP0y.
Qed.

End ExpandHypotheses.

(* This is B & G, Appendix C, Theorem C. *)
Theorem prime_dim_normed_finField : (p <= q)%N.
Proof.
apply: wlog_neg; rewrite -ltnNge => ltqp.
have [F sigma /isomP[inj_sigma im_sigma] defP0] := fieldH.
case=> sigmaU inj_sigmaU sigmaJ.
have oF: #|F| = (p ^ q)%N by rewrite -cardsT -im_sigma card_injm.
have charFp: p \in [char F] := card_finCharP oF pr_p.
have sP0P: P0 \subset P by rewrite -defP0 subsetIl.
pose s := invm inj_sigma 1%R.
have sigma_s: sigma s = 1%R by rewrite invmK ?im_sigma ?inE.
have{defP0} defP0: <[s]> = P0.
  by rewrite -morphim_cycle /= ?im_sigma ?inE // morphim_invmE.
exact: BGappendixC_inner_subproof defP0 sigmaJ.
Qed.

End AppendixC.
