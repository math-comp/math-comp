(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
Require Import fingroup morphism perm automorphism quotient action zmodp.
Require Import gfunctor gproduct cyclic pgroup commutator nilpotent frobenius.
Require Import matrix mxalgebra mxrepresentation BGsection3 vector.
Require Import ssrnum algC classfun character inertia vcharacter.
Require Import PFsection1 PFsection2 PFsection4 PFsection5 PFsection6.

(******************************************************************************)
(* This file covers Peterfalvi, Section 7:                                    *)
(* Non-existence of a Certain Type of Group of Odd Order                      *)
(* Defined here:                                                              *)
(*    inDade ddA == the right inverse to the Dade isometry with respect to G, *)
(*                  L, A, given ddA : Dade_hypothesis G L A.                  *)
(*      phi^\rho == locally-bindable Notation for invDade ddA phi.            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Reserved Notation "alpha ^\rho" (at level 2, format "alpha ^\rho").

Section Seven.

Variables (gT : finGroupType) (G : {group gT}).
Implicit Types (L H P : {group gT}) (DH : gT -> {group gT}).

(* Properties of the inverse to the Dade isometry (Peterfalvi (7.1) to (7.3). *)
Section InverseDade.

Variables (A : {set gT}) (L : {group gT}).
Hypothesis ddA : Dade_hypothesis G L A.

Local Notation "alpha ^\tau" := (Dade ddA alpha).
Local Notation Atau := (Dade_support ddA).
Local Notation H := (Dade_signalizer ddA).

Let nsAL : A <| L. Proof. by have [] := ddA. Qed.
Let sAL : A \subset L. Proof. exact: normal_sub nsAL. Qed.
Let nAL : L \subset 'N(A). Proof. exact: normal_norm nsAL. Qed.
Let sLG : L \subset G. Proof. by have [] := ddA. Qed.

(* This is the Definition embedded in Peterfalvi, Hypothesis (7.1). *)
Fact invDade_subproof (chi : 'CF(G)) :
  is_class_fun <<L>>
    [ffun a => #|H a|%:R^-1 * (\sum_(x in H a) chi (x * a)%g) *+ (a \in A)].
Proof.
rewrite genGid; apply: intro_class_fun => [x y Lx Ly | x notLx]; last first.
  by rewrite (contraNF (subsetP sAL x)).
rewrite memJ_norm ?(subsetP nAL) // !mulrb; case: ifP => // Ax.
rewrite (DadeJ ddA) // cardJg; congr (_ * _).
rewrite big_imset /= => [|z y0 _ _ /=]; last exact: conjg_inj.
by apply: eq_bigr => u Hu; rewrite -conjMg cfunJ // (subsetP sLG).
Qed.
Definition invDade alpha := Cfun 1 (invDade_subproof alpha).  

Local Notation "alpha ^\rho" := (invDade alpha).

Fact invDade_is_linear : linear invDade.
Proof.
move=> mu alpha beta; apply/cfunP=> a; rewrite !cfunElock.
rewrite mulrnAr -mulrnDl mulrCA -mulrDr; congr (_ * _ *+ _).
by rewrite big_distrr -big_split; apply: eq_bigr => x _; rewrite !cfunE.
Qed.
Canonical invDade_linear := Linear invDade_is_linear.
Canonical invDade_additive := Additive invDade_is_linear.

Lemma invDade_on chi : chi^\rho \in 'CF(L, A).
Proof. by apply/cfun_onP=> x notAx; rewrite cfunElock (negPf notAx). Qed.

Lemma invDade_cfun1 : 1^\rho = '1_A.
Proof.
apply/cfunP=> x; rewrite cfuniE // cfunElock mulrb; case: ifP => //= Ax.
apply: canLR (mulKf (neq0CG _)) _; rewrite mulr1 -sumr_const.
apply: eq_bigr => u Hu; rewrite cfun1E (subsetP (subsetIl G 'C[x])) //.
have /sdprodP[_ <- _ _] := Dade_sdprod ddA Ax.
by rewrite mem_mulg // inE cent1id (subsetP sAL).
Qed.

(* This is Peterfalvi (2.7), restated using invDade. *)
Lemma invDade_reciprocity chi alpha :
  alpha \in 'CF(L, A) -> '[alpha^\tau, chi] = '[alpha, chi^\rho].
Proof.
move=> Aalpha; apply: general_Dade_reciprocity => //= a Aa.
by rewrite cfunElock Aa.
Qed.

(* This is Peterfalvi (7.2)(a). *)
Lemma DadeK alpha : alpha \in 'CF(L, A) -> (alpha^\tau)^\rho = alpha.
Proof.
move=> Aalpha; apply/cfunP=> a; rewrite cfunElock mulrb.
case: ifPn => [Aa | /cfun_on0-> //]; apply: canLR (mulKf (neq0CG _)) _.
rewrite mulr_natl -sumr_const; apply: eq_bigr => x Hx.
by rewrite (DadeE _ Aa) ?mem_class_support // mem_mulg ?set11.
Qed.

(* This is Peterfalvi (7.2)(b); note that by (7.2)(a) chi is in the image of  *)
(* tau iff chi = (chi^\rho)^\tau, and this condition is easier to write.      *)
Lemma leC_norm_invDade chi :
  '[chi^\rho] <= '[chi] ?= iff (chi == (chi^\rho)^\tau).
Proof.
have Achi_rho := invDade_on chi; rewrite -(Dade_isometry ddA) //.
set chi1 := _^\tau; rewrite -subr_eq0 -cfnorm_eq0; set mu := chi - chi1.
have owv: '[chi1, mu] = 0.
  by rewrite invDade_reciprocity ?raddfB //= DadeK ?subrr.
rewrite -(subrK chi1 chi) -/mu addrC cfnormD owv conjC0 !addr0.
split; first by rewrite -subr_ge0 addrC addKr cfnorm_ge0.
by rewrite eq_sym addrC -subr_eq0 addrK.
Qed.

(* This is Peterfalvi (7.3). *)
Lemma leC_cfnorm_invDade_support chi :
  '[chi^\rho] <= #|G|%:R^-1 * (\sum_(g in Atau) `|chi g| ^+ 2)
     ?= iff [forall a in A, forall u in H a, chi (u * a)%g == chi a].
Proof.
have nsAtauG: Atau <| G := Dade_support_normal ddA.
pose chi1 := chi * '1_Atau; set RHS := _ * _.
have inA1 a x: a \in A -> x \in H a -> (x * a)%g \in Dade_support1 ddA a.
  by move=> Aa Hx; rewrite mem_class_support ?mem_mulg ?set11.
have chi1E a x: a \in A -> x \in H a -> chi1 (x * a)%g = chi (x * a)%g.
  move=> Aa Hx; rewrite cfunE cfuniE // mulr_natr mulrb.
  by case: bigcupP => // [[]]; exists a; rewrite ?inA1.
have ->: chi^\rho = chi1^\rho.
  apply/cfunP => a; rewrite !cfunElock !mulrb; case: ifP => // Aa.
  by congr (_ * _); apply: eq_bigr => x /chi1E->.
have Achi1: chi1 \in 'CF(G, Atau).
  by apply/cfun_onP=> x ?; rewrite cfunE (cfun_onP (cfuni_on _ _)) ?mulr0.
have{Achi1 RHS} <-: '[chi1] = RHS.
  rewrite (cfnormE Achi1); congr (_ * _).
  by apply: eq_bigr => x Atau_x; rewrite cfunE cfuniE // Atau_x mulr1.
congr (_ <= _ ?= iff _): (leC_norm_invDade chi1).
apply/eqP/forall_inP=> [chi1_id a Aa | chi_id].
  apply/forall_inP => x Ha_x; rewrite -{2}[a]mul1g -!chi1E // chi1_id mul1g.
  by rewrite (DadeE _ Aa) ?inA1 ?Dade_id.
apply/cfunP => g; rewrite cfunE cfuniE // mulr_natr mulrb.
case: ifPn => [/bigcupP[a Aa] | /(cfun_onP (Dade_cfunS _ _))-> //].
case/imset2P=> _ z /rcosetP[x Hx ->] Gz ->{g}; rewrite !cfunJ {z Gz}//.
have{chi_id} chi_id := eqP (forall_inP (chi_id a Aa) _ _).
rewrite chi_id // (DadeE _ Aa) ?inA1 {x Hx}// cfunElock mulrb Aa.
apply: canRL (mulKf (neq0CG _)) _; rewrite mulr_natl -sumr_const.
by apply: eq_bigr => x Hx; rewrite chi1E ?chi_id.
Qed.

(* This is the norm expansion embedded in Peterfalvi (7.3). *)
Lemma cfnormE_invDade chi :
  '[chi^\rho] = #|L|%:R^-1 * (\sum_(a in A) `|chi^\rho a| ^+ 2).
Proof. by apply: cfnormE; exact: invDade_on. Qed.

End InverseDade.

(* Hypothesis (7.4) and Lemma (7.5). *)
Section DadeCoverInequality.

(* These declarations correspond to Peterfalvi, Hypothesis (7.4); as it is    *)
(* only instantiated twice after this section we leave it unbundled.          *)
Variables (I : finType) (L : I -> {group gT}) (A : I -> {set gT}).
Hypothesis ddA : forall i : I, Dade_hypothesis G (L i) (A i).

Local Notation Atau i := (Dade_support (ddA i)).
Local Notation "alpha ^\rho" := (invDade (ddA _) alpha).
Hypothesis disjointA : forall i j, i != j -> [disjoint Atau i & Atau j].

(* This is Peterfalvi (7.5), generalised to all class functions of norm 1. *)
Lemma Dade_cover_inequality (chi : 'CF(G)) (G0 := G :\: \bigcup_i Atau i) :
    '[chi] = 1 ->
  #|G|%:R^-1 * (\sum_(g in G0) `|chi g| ^+ 2 - #|G0|%:R)
    + \sum_i ('[chi^\rho]_(L i) - #|A i|%:R / #|L i|%:R) <= 0.
Proof.
move=> Nchi1; set vG := _^-1; rewrite sumrB /= addrCA mulrBr -addrA.
pose F (xi : 'CF(G)) (B : {set gT}) := vG * \sum_(g in B) `|xi g| ^+ 2.
have sumF xi: F xi G0 + \sum_i F xi (Atau i) = '[xi].
  rewrite (cfnormE (cfun_onG _)) -mulr_sumr -mulrDr; congr (_ * _).
  rewrite -partition_disjoint_bigcup //=; set U_A := \bigcup_i _.
  have sUG: U_A \subset G by apply/bigcupsP=> i _; apply: Dade_support_sub.
  by rewrite -(setIidPr sUG) addrC -big_setID.
have ->: \sum_i #|A i|%:R / #|L i|%:R = \sum_i F 1 (Atau i).
  apply: eq_bigr => i _; apply/eqP; rewrite /F.
  have [[/andP[sAL nAL] _ _ _ _] sHG] := (ddA i, Dade_signalizer_sub (ddA i)).
  rewrite -{1}[A i]setIid -cfdot_cfuni /normal ?sAL // -(invDade_cfun1 (ddA i)).
  rewrite leC_cfnorm_invDade_support; apply/forall_inP=> a Aa.
  by apply/forall_inP=> x Hx; rewrite !cfun1E groupMl // (subsetP (sHG a)).
have ->: vG * #|G0|%:R = F 1 G0.
  congr (_ * _); rewrite -sumr_const; apply: eq_bigr => x /setDP[Gx _].
  by rewrite cfun1E Gx normr1 expr1n.
rewrite -opprD sumF cfnorm1 -Nchi1 -sumF opprD addNKr -oppr_ge0 opprB -sumrB.
by rewrite sumr_ge0 // => i _; rewrite subr_ge0 leC_cfnorm_invDade_support.
Qed.

(*
set vG := _^-1; rewrite sumrB /= addrCA mulrBr -addrA.
pose F t (B : {set gT}) := vG * \sum_(g in B) `|'chi[G]_t g| ^+ 2.
have sumF t: F t G0 + \sum_i F t (Atau i) = 1.
  rewrite -(cfnorm_irr t) (cfnormE (cfun_onG _)) -mulr_sumr -mulrDr.
  congr (_ * _); rewrite -partition_disjoint_bigcup //=; set U_A := \bigcup_i _.
  have sUG: U_A \subset G by apply/bigcupsP=> i _; apply: Dade_support_sub.
  by rewrite -(setIidPr sUG) addrC -big_setID.
have ->: \sum_i #|A i|%:R / #|L i|%:R = \sum_i F 0 (Atau i).
  apply: eq_bigr => i _; apply/eqP; rewrite /F irr0.
  have [[/andP[sAL nAL] _ _ _ _] sHG] := (ddA i, Dade_signalizer_sub (ddA i)).
  rewrite -{1}[A i]setIid -cfdot_cfuni /normal ?sAL // -(invDade_cfun1 (ddA i)).
  rewrite leC_cfnorm_invDade_support; apply/forall_inP=> a Aa.
  by apply/forall_inP=> x Hx; rewrite !cfun1E groupMl // (subsetP (sHG a)).
have ->: vG * #|G0|%:R = F 0 G0.
  congr (_ * _); rewrite -sumr_const; apply: eq_bigr => x /setDP[Gx _].
  by rewrite irr0 cfun1E Gx normr1 expr1n.
rewrite -opprD sumF -(sumF r) opprD addNKr -oppr_ge0 opprB -sumrB.
by rewrite sumr_ge0 // => i _; rewrite subr_ge0 leC_cfnorm_invDade_support.
Qed.
*)

End DadeCoverInequality.

(* Hypothesis (7.6), and Lemmas (7.7) and (7.8) *)
Section Dade_seqIndC1.

(* In this section, A = H^# with H <| L. *)
Variables L H : {group gT}.
Let A := H^#.
Hypothesis ddA : Dade_hypothesis G L A.

Local Notation Atau := (Dade_support ddA).
Local Notation "alpha ^\tau" := (Dade ddA alpha).
Local Notation "alpha ^\rho" := (invDade ddA alpha).

Let calT := seqIndT H L.
Local Notation calS := (seqIndD H L H 1).
Local Notation Ind1H := ('Ind[gval L, gval H] 1).
Let uniqS : uniq calS := seqInd_uniq _ _.

Let h := #|H|%:R : algC.
Let e := #|L : H|%:R : algC.

Let nsAL : A <| L. Proof. by have [] := ddA. Qed.
Let sLG : L \subset G. Proof. by have [] := ddA. Qed.
Let nsHL : H <| L. Proof. by rewrite -normalD1. Qed.
Let sHL := normal_sub nsHL.
Let nHL := normal_norm nsHL.

Let nzh : h != 0 := neq0CG H.
Let nze : e != 0 := neq0CiG L H.
Let nzL : #|L|%:R != 0 := neq0CG L.

Let eh : e * h = #|L|%:R. Proof. by rewrite -natrM mulnC Lagrange. Qed.

Section InvDadeSeqInd.

Variables (xi0 : 'CF(L)) (S : seq 'CF(L)) (chi : 'CF(G)).
Implicit Types xi mu : 'CF(L).

Let d xi := xi 1%g / xi0 1%g.
Let psi xi := xi - d xi *: xi0.
Let c xi := '[(psi xi)^\tau, chi].

Let uc c xi mu := (c xi)^* * c mu / ('[xi] * '[mu]).
Let u c xi mu := uc c xi mu * ('[xi, mu] - xi 1%g * mu 1%g / (e * h)).

(* This is Peterfalvi (7.7); it is stated using a bespoke concrete Prop so as *)
(* to encapsulate the coefficient definitions given above.                    *)
CoInductive is_invDade_seqInd_sum : Prop :=
  InvDadeSeqIndSum (c := c) (u := u c) of
   (*a*) {in A, forall x, (chi^\rho) x = \sum_(xi <- S) (c xi)^* / '[xi] * xi x}
 & (*b*) '[chi^\rho] = \sum_(xi <- S) \sum_(mu <- S) u xi mu.

Lemma invDade_seqInd_sum : perm_eq calT (xi0 :: S) -> is_invDade_seqInd_sum.
Proof.
move=> defT; pose chi0 := \sum_(xi <- S) (c xi)^* / '[xi] *: xi.
have Txi0: xi0 \in calT by rewrite (perm_eq_mem defT) mem_head.
have sST : {subset S <= calT}.
  by move=> xi Sxi; rewrite (perm_eq_mem defT) mem_behead.
have nz_xi01 : xi0 1%g != 0 by apply: seqInd1_neq0 Txi0.
have part_a: {in A, chi^\rho =1 chi0}.
  pose phi := (chi^\rho - chi0) * '1_A.
  have Aphi : phi \in 'CF(L, A) := mul_cfuni_on A _.
  suffices: '[phi, chi^\rho - chi0] == 0; last clearbody phi.
    rewrite -(eq_cfdotr Aphi (eq_mul_cfuni _ nsAL)) cfnorm_eq0 => /eqP phi0.
    by move=> x Ax; rewrite -[chi0]add0r -phi0 cfunE eq_mul_cfuni ?cfunE ?subrK.
  have{Aphi} [Hphi phi1]: phi \in 'CF(L, H) /\ phi 1%g = 0.
    by move: Aphi; rewrite cfun_onD1 => /andP[-> /eqP].
  have{Hphi} def_phi: phi = e^-1 *: 'Ind ('Res[H] phi).
    apply/cfunP=> y; have [Hy | notHy] := boolP (y \in H); last first.
      by rewrite cfunE !(cfun_on0 _ notHy) ?mulr0 ?cfInd_normal.
    rewrite cfunE cfIndE // mulrA -invfM eh.
    apply: (canRL (mulKf nzL)); rewrite mulr_natl -sumr_const.
    by apply: eq_bigr => z Lz; rewrite cfResE ?memJ_norm ?cfunJ ?(subsetP nHL).
  have{def_phi} Tphi: phi \in <<calT>>%VS.
    rewrite def_phi memvZ // ['Res _]cfun_sum_cfdot linear_sum.
    apply: memv_suml => i _; rewrite linearZ memvZ ?memv_span //=.
    by apply/seqIndP; exists i; rewrite ?inE.
  have{Tphi} [z def_phi _] := free_span (seqInd_free nsHL _) Tphi.
  have {phi def_phi phi1} ->: phi = \sum_(xi <- S) z xi *: psi xi.
    rewrite def_phi (eq_big_perm _ defT) !big_cons /= 2!cfunE in phi1 *.
    rewrite (canRL (mulfK nz_xi01) (canRL (addrK _) phi1)) add0r addrC mulNr.
    rewrite sum_cfunE mulr_suml scaleNr scaler_suml -sumrB.
    by apply: eq_bigr => xi _; rewrite cfunE -mulrA -scalerA -scalerBr.
  rewrite cfdot_suml big1_seq //= => xi Sxi; have Txi := sST xi Sxi.
  rewrite cfdotZl cfdotBr -invDade_reciprocity -/(c xi); last first.
    rewrite cfun_onD1 !cfunE divfK // subrr eqxx andbT.
    by rewrite memvB ?memvZ //= ((seqInd_on _) setT).
  have [oSS /orthoPl o_xi0S]: pairwise_orthogonal S /\ orthogonal xi0 S.
    have:= seqInd_orthogonal nsHL setT; rewrite (eq_pairwise_orthogonal defT).
    by rewrite /= -cat1s pairwise_orthogonal_cat => /and3P[].
  rewrite cfdotBl cfdotC cfproj_sum_orthogonal {oSS}// cfdotZl cfdot_sumr.
  rewrite big1_seq ?mulr0 => [|mu Smu]; last by rewrite cfdotZr o_xi0S ?mulr0.
  by rewrite subr0 divfK ?(cfnorm_seqInd_neq0 _ Txi) // conjCK subrr mulr0.
split=> [x /part_a-> | ].
  by rewrite sum_cfunE; apply: eq_bigr => ?; rewrite cfunE.
rewrite (cfdotEl _ (invDade_on ddA _)) mulrC mulr_suml.
pose F xi mu x := uc c xi mu * (xi x * (mu x)^*) / #|L|%:R.
transitivity (\sum_(x in A) \sum_(xi <- S) \sum_(mu <- S) F xi mu x).
  apply: eq_bigr => x Ax; rewrite part_a // sum_cfunE -mulrA mulr_suml.
  apply: eq_bigr => xi _; rewrite mulrA -mulr_suml rmorph_sum; congr (_ * _).
  rewrite mulr_sumr; apply: eq_bigr => mu _; rewrite !cfunE (cfdotC mu).
  rewrite -{1}[mu x]conjCK -fmorph_div -rmorphM conjCK -4!mulrA 2!(mulrCA _^-1).
  by rewrite (mulrA _^-1) -invfM 2!(mulrCA (xi x)) mulrA 2!(mulrA _^*).
rewrite exchange_big; apply: eq_bigr => xi _; rewrite exchange_big /=.
apply: eq_big_seq => mu Smu; have Tmu := sST mu Smu.
rewrite /u eh (cfdotEr _ (seqInd_on nsHL Tmu)) (mulrC _^-1) -mulrBl mulrA.
rewrite -mulr_suml -mulr_sumr (big_setD1 1%g (group1 H)) /=; congr (_ * _ * _).
by rewrite addrC conj_Cnat ?addKr // (Cnat_seqInd1 Tmu).
Qed.

End InvDadeSeqInd.

Notation "1" := (1 : 'CF(_)) : classfun_scope.

(* This is Peterfalvi (7.8). *)
(* Our version is slightly stronger because we state the nontriviality of S   *)
(* directly than through the coherence premise (see the discussion of (5.2)). *)
Lemma Dade_Ind1_sub_lin (nu : {additive 'CF(L) -> 'CF(G)}) zeta :
    coherent_with calS L^# (Dade ddA) nu -> (1 < size calS)%N ->
    zeta \in irr L -> zeta \in calS -> zeta 1%g = e ->
  let beta := (Ind1H - zeta)^\tau in let calSnu := map nu calS in 
  let sumSnu := \sum_(xi <- calS) xi 1%g / e / '[xi] *: nu xi in 
  [/\ (*a1*) [/\ orthogonal calSnu 1%CF, '[beta, 1] = 1 & beta \in 'Z[irr G]],
      exists2 Gamma : 'CF(G),
      (*a2*) [/\ orthogonal calSnu Gamma, '[Gamma, 1] = 0
             & exists2 a, a \in Cint & beta = 1 - nu zeta + a *: sumSnu + Gamma]
    & (*b*) e <= (h - 1) / 2%:R ->
            '[(nu zeta)^\rho] >= 1 - e / h /\ '[Gamma] <= e - 1
    & (*c*) {in irr G, forall chi : 'CF(G), orthogonal calSnu chi ->
        [/\ {in A, forall x, chi^\rho x = '[beta, chi]}
          & '[chi^\rho] = #|A|%:R / #|L|%:R * '[beta, chi] ^+ 2]}].
Proof.
move=> [[Inu Znu] nu_tau] nt_calS /irrWnorm Nzeta1 Szeta zeta1.
set mu := _ - _ => beta calSnu sumSnu; pose S1 := rem zeta calS.
have defS: perm_eq calS (zeta :: S1) := perm_to_rem Szeta.
have defZS: 'Z[calS, L^#] =i 'Z[calS, A] by apply: zcharD1_seqInd.
have S1P xi: xi \in S1 -> xi != zeta /\ xi \in calS.
  by rewrite mem_rem_uniq // => /andP[].
have defT: perm_eql calT [:: Ind1H, zeta & S1].
  apply/perm_eqlP; have Tind1: Ind1H \in calT := seqIndT_Ind1 H L.
  by rewrite (perm_eqlP (perm_to_rem Tind1)) perm_cons -seqIndC1_rem.
have mu_vchar: mu \in 'Z[irr L, A] := cfInd1_sub_lin_vchar nsHL Szeta zeta1.
have beta_vchar: beta \in 'Z[irr G] by apply: Dade_vchar.
have [mu_on beta_on] := (zchar_on mu_vchar, zchar_on beta_vchar).
have{nt_calS} ntS1: (size S1 > 0)%N by rewrite size_rem // -subn1 subn_gt0.
case defS1: S1 ntS1 => // [phi S2] _.
have /S1P[neq_phi Sphi]: phi \in S1 by rewrite defS1 mem_head.
have nz_phi1: phi 1%g != 0 by rewrite (seqInd1_neq0 nsHL Sphi).
have NatS1e xi (Sxi : xi \in calS) := dvd_index_seqInd1 nsHL Sxi.
have oS1: {in calS, forall psi, '[psi, 1] = 0} by apply: seqInd_ortho_1.
have oS1H: {in calS, forall psi, '[psi, Ind1H] = 0} by apply: seqInd_ortho_Ind1.
have InuS: {in calS &, isometry nu} by apply: sub_in2 Inu; exact: seqInd_zcharW.
have ZnuS xi (Sxi : xi \in calS) := Znu xi (seqInd_zcharW  Sxi).
have S_Se xi (Sxi : xi \in calS) := seqInd_sub_lin_vchar nsHL Szeta zeta1 Sxi.
have oSnu1: orthogonal calSnu 1%CF.
  have dotSnu1 psi : psi \in calS -> '[nu psi, 1] = psi 1%g / e * '[nu zeta, 1].
    move=> Spsi; apply/eqP; rewrite -subr_eq0 -cfdotZl -cfdotBl.
    rewrite -raddfZ_Cnat ?NatS1e // -raddfB; have Spi := S_Se _ Spsi.
    rewrite nu_tau ?defZS // invDade_reciprocity ?(zchar_on Spi) //.
    rewrite invDade_cfun1 (eq_cfdotr (zchar_on Spi) (eq_cfuni nsAL)).
    by rewrite cfdotBl cfdotZl !oS1 // mulr0 subr0.
  suffices oz1: '[nu zeta, 1] = 0.
    by apply/orthoPr=> _ /mapP[psi Spsi ->]; rewrite dotSnu1 // oz1 mulr0.
  have norm_nu_zeta : '[nu zeta] = 1 by rewrite InuS // irrWnorm.
  have [et [t defz]] := vchar_norm1P (ZnuS _ Szeta) norm_nu_zeta.
  rewrite defz cfdotZl -{1}irr0 cfdot_irr mulr_natr mulrb; case: eqP => // t0.
  have /eqP/idPn[] := seqInd_ortho nsHL Sphi Szeta neq_phi.
  rewrite -InuS // defz t0 cfdotZr irr0 dotSnu1 // mulrCA -irr0 -t0.
  by rewrite -cfdotZr -defz norm_nu_zeta mulr1 mulf_neq0 ?invr_eq0.
have dot_beta_1: '[beta, 1] = 1.
  rewrite invDade_reciprocity // invDade_cfun1 (eq_cfdotr _ (eq_cfuni nsAL)) //.
  by rewrite cfdotBl -Frobenius_reciprocity cfRes_cfun1 ?cfnorm1 ?oS1 ?subr0.
have o_beta1: '[beta - 1, 1] = 0 by rewrite cfdotBl dot_beta_1 cfnorm1 subrr.
have [X SnuX [Gamma [def_beta1 _  oSnuG]]]:= orthogonal_split calSnu (beta - 1).
have oG1: '[Gamma, 1] = 0.
  rewrite -(addKr X Gamma) -def_beta1 addrC cfdotBl o_beta1.
  by rewrite (span_orthogonal oSnu1) ?subr0 // memv_span ?mem_head.
have oSS: pairwise_orthogonal calS by apply: seqInd_orthogonal.
have oSnuS: pairwise_orthogonal calSnu by apply: map_pairwise_orthogonal.
have [a_ def_a defX] := orthogonal_span oSnuS SnuX.
have{def_a} def_a: {in calS, forall xi, a_ (nu xi) = '[beta, nu xi] / '[xi]}.
  move=> xi Sxi; rewrite (canRL (subrK 1) def_beta1) !cfdotDl def_a InuS //.
  by rewrite (cfdotC 1) (orthoPl oSnuG) ?(orthoPr oSnu1) ?map_f ?conjC0 ?addr0.
pose a := '[beta, nu zeta] + 1; have Z1 := Cint1.
have{Z1} Za: a \in Cint by rewrite rpredD ?Cint_cfdot_vchar // ZnuS.
have {a_ def_a defX} defX: X = - nu zeta + a *: sumSnu.
  rewrite linear_sum defX big_map !(eq_big_perm _ defS) !big_cons /= addrCA.
  rewrite def_a // Nzeta1 !divr1 zeta1 divff // scalerDl !scale1r addrA.
  rewrite addrK; congr (_ + _); apply: eq_big_seq => xi /S1P[neq_xi Sxi].
  rewrite def_a // scalerA mulrA mulrDl mul1r; congr (_ / _ *: _).
  rewrite mulrC -(conj_Cnat (NatS1e _ Sxi)) -cfdotZr -raddfZ_Cnat ?NatS1e //.
  rewrite addrC; apply: canRL (subrK _) _; rewrite -!raddfB /= -/e.
  have Spi := S_Se xi Sxi; rewrite nu_tau ?defZS //.
  rewrite Dade_isometry ?(zchar_on Spi) // cfdotC cfdotBl cfdotZl !cfdotBr.
  by rewrite !oS1H ?(seqInd_ortho _ Sxi) // Nzeta1 subr0 !add0r mulrN1 opprK.
have Ind1H1: Ind1H 1%g = e by rewrite cfInd1 // cfun11 mulr1.
split=> // [ | chi /irrP[t def_chi] o_chiSnu].
  rewrite (canRL (subrK 1) def_beta1) defX addrC 2!addrA.
  exists Gamma; first by rewrite orthogonal_sym; split; last exists a.
  move=> lt_e_h2; pose v := h^-1; pose u := e^-1 * (1 - v); set w := 1 - e / h.
  have hu: h * u = e^-1 * (h - 1) by rewrite mulrCA (mulrBr h) mulr1 divff.
  have ->: '[(nu zeta)^\rho] = u * a ^+ 2 - v * a *+ 2 + w.
    have defT1: perm_eq calT [:: phi, Ind1H, zeta & S2].
      by rewrite defT defS1 (perm_catCA [::_ ; _] phi).
    have [c ua _ ->] := invDade_seqInd_sum (nu zeta) defT1.
    have def_c xi: xi \in calS -> c xi = '[xi, zeta].
      move=> S2xi; rewrite /c mulrC -{1}[xi]scale1r -(mulVf nz_phi1) -!scalerA.
      rewrite -scalerBr linearZ cfdotZl /=; set pi := _ - _.
      have Spi: pi \in 'Z[calS, A] by apply: sub_seqInd_zchar.
      rewrite -nu_tau ?defZS // Inu ?(zcharW Spi) ?seqInd_zcharW //.
      by rewrite cfdotBl !cfdotZl (seqInd_ortho _ Sphi) // mulr0 subr0 mulKf.
    have c2: c zeta = 1 by rewrite def_c.
    have c1: c Ind1H = a.
      by rewrite /a -c2 -cfdotDl -linearD !addrA subrK zeta1 -Ind1H1.
    have{def_c} c3 xi: xi \in S2 -> c xi = 0.
      move=> S2xi; have /S1P[neq_xi Sxi]: xi \in S1 by rewrite defS1 mem_behead.
      by rewrite def_c // (seqInd_ortho _ Sxi).
    rewrite !big_cons; have kill0 := (mul0r, mulr0, big1, conjC0).
    rewrite !big1_seq /ua; try by move=> psi /c3->; do 2?rewrite ?kill0 => *.
    rewrite !addr0 c1 c2 Nzeta1 cfnorm_Ind_cfun1 // -/e Ind1H1 zeta1 conjC1.
    rewrite cfdotC (seqInd_ortho_Ind1 _ _ Szeta) // !kill0 sub0r !mulrN !mulr1.
    rewrite divr1 !mul1r !invfM mulrBr !mulrA !mulfK ?divfK // -/w.
    rewrite aut_Cint // -[_ / h]mulrA -{1}[e^-1]mulr1 -2!mulrBr -/u -/v.
    by rewrite mulrC mulrA addrA (mulrC v) -[_ - _]addrA -opprD.
  have ->: '[Gamma] = e - 1 - h * (u * a ^+ 2 - v * a *+ 2).
    have /(canLR (addrK 1)) <-: '[beta] = e + 1.
      rewrite Dade_isometry // cfnormBd ?cfnorm_Ind_cfun1 ?Nzeta1 //.
      by rewrite cfdotC (seqInd_ortho_Ind1 _ _ Szeta) ?conjC0.
    rewrite -[beta](subrK 1) cfnormDd; last first.
      by rewrite cfdotBl dot_beta_1 cfnorm1 subrr.
    rewrite cfnorm1 addrK def_beta1 (addrC X) cfnormDd; last first.
      by rewrite (span_orthogonal oSnuG) // memv_span ?mem_head.
    do 2!apply: canRL (addrK _) _; rewrite -addrA; congr (_ + _).
    rewrite defX (addrC (- nu _)) cfnormB cfnormZ Cint_normK // InuS //.
    rewrite cfdotZl cfproj_sum_orthogonal // Nzeta1 zeta1 divff // divr1.
    rewrite !mulr1 aut_Cint // mulrBr mulrDr mulVKf // addrAC.
    rewrite mulrA mulrC hu -[e^-1](divfK nze) -expr2; congr (_ * _ - _ + 1).
    rewrite -mulrA -sum_seqIndC1_square // mulr_sumr cfnorm_sum_orthogonal //.
    apply: eq_big_seq => xi Sxi.
    have [nz_xi Nxi1] := (cfnorm_seqInd_neq0 nsHL Sxi, Cnat_seqInd1 Sxi).
    rewrite (normr_idP _) ?mulr_ge0 ?invr_ge0 ?ler0n ?cfnorm_ge0 ?Cnat_ge0 //.
    by rewrite mulrCA !exprMn ['[xi]]lock !mulrA divfK // -lock.
  apply/andP; rewrite -subr_ge0 addrK andbC -subr_ge0 addrC opprB subrK.
  rewrite pmulr_rge0 ?gt0CG // andbb -mulr_natr (mulrAC v).
  have v_ge0: 0 <= v by [rewrite invr_ge0 ler0n]; have L_gt0 := gt0CG L.
  have Lu: #|L|%:R * u = h - 1 by rewrite -eh -mulrA hu mulVKf.
  have h1ge0: 0 <= h - 1 by rewrite subr_ge0 ler1n cardG_gt0.
  have{h1ge0} u_ge0: 0 <= u by rewrite -Lu pmulr_rge0 in h1ge0.
  have [a_le0 | ] := boolP (a <= 0).
    by rewrite -mulrN -sqrrN addr_ge0 ?(u_ge0, mulr_ge0) ?oppr_ge0 ?ler0n.
  rewrite -real_ltrNge ?Creal_Cint // ltr_def => /andP[].
  move/(norm_Cint_ge1 Za)=> a_ge1 a_ge0; rewrite mulrA -mulrBl.
  rewrite (normr_idP _) // -(@mulVf _ 2%:R) ?pnatr_eq0 // in a_ge1.
  rewrite mulr_ge0 // subr_ge0 (ler_trans _ (ler_wpmul2l u_ge0 a_ge1)) // mulrA.
  by rewrite ler_wpmul2r ?ler0n // -(ler_pmul2l L_gt0) mulrA Lu -eh mulfK.
have Zchi: chi \in 'Z[irr G] by rewrite def_chi irr_vchar.
have def_chi0: {in A, chi^\rho =1 (fun _ => '[beta, chi])}.
  have defT1: perm_eq calT [:: zeta, Ind1H & S1].
    by rewrite defT (perm_catCA Ind1H zeta).
  move=> x Ax; have [_ Hx] := setD1P Ax.
  have [c _ -> // _] := invDade_seqInd_sum chi defT1.
  rewrite big_cons big1_seq ?addr0 /c => [|xi /S1P[neq_xi /= Sxi]]; last first.
    rewrite zeta1 -nu_tau ?defZS ?S_Se // raddfB cfdotBl raddfZ_Cnat ?NatS1e //.
    by rewrite cfdotZl !(orthoPr o_chiSnu) ?map_f // mulr0 subr0 conjC0 !mul0r.
  rewrite Ind1H1 zeta1 divff // scale1r -/beta aut_Cint ?Cint_cfdot_vchar //.
  by rewrite cfnorm_Ind_cfun1 ?cfInd_cfun1 // cfunE cfuniE // Hx mulr1 divfK.
split=> //; rewrite -mulrA mulrCA cfnormE_invDade; congr (_ * _).
rewrite mulr_natl -sumr_const; apply: eq_bigr => _ /def_chi0->.
by rewrite Cint_normK ?Cint_cfdot_vchar.
Qed.

End Dade_seqIndC1.

(* The other results of the section are specific to groups of odd order. *)
Hypothesis oddG : odd #|G|.

(* We explicitly factor out several intermediate results from the proof of    *)
(* (7.9) that are reused throughout the proof (including in (7.10) below).    *)

Import ssrint.
Lemma cfdot_real_vchar_even phi psi :
    phi \in 'Z[irr G] /\ cfReal phi  -> psi \in 'Z[irr G] /\ cfReal psi ->
  (2 %| '[phi, psi])%C = (2 %| '[phi, 1])%C || (2 %| '[psi, 1])%C.
Proof.
move=> [Zphi Rphi] [Zpsi Rpsi]; rewrite cfdot_vchar_r // (bigD1 (0 : 'I__)) //=.
rewrite addrC -irr0 (bigID [pred i | conjC_Iirr i < i]%N) /=.
set a1 := \sum_(i | _) _; set a2 := \sum_(i | _) _; suffices ->: a1 = a2.
  rewrite -mulr2n -mulr_natr (rpredDl _ (dvdC_mull _ _)) //; last first.
    by rewrite rpred_sum // => i; rewrite rpredM ?Cint_cfdot_vchar_irr.
  have /CintP[m1 ->] := Cint_cfdot_vchar_irr 0 Zphi.
  have /CintP[m2 ->] := Cint_cfdot_vchar_irr 0 Zpsi.
  rewrite [m1]intEsign [m2]intEsign !rmorphMsign mulrACA -!mulrA !rpredMsign.
  by rewrite -natrM !(dvdC_nat 2) Euclid_dvdM.
rewrite /a2 (reindex_inj (inv_inj (@conjC_IirrK _ _))) /=.
apply: eq_big => [t | t _]; last first.
  by rewrite !conjC_IirrE !cfdot_real_conjC ?aut_Cint ?Cint_cfdot_vchar_irr.
rewrite (inv_eq (@conjC_IirrK _ _)) conjC_IirrK -leqNgt ltn_neqAle val_eqE.
rewrite -!(inj_eq irr_inj) !conjC_IirrE irr0 cfConjC_cfun1 odd_eq_conj_irr1 //.
by rewrite andbA andbb.
Qed.

Section DisjointDadeOrtho.

Variables (L1 L2 H1 H2 : {group gT}).
Let A1 := H1^#.
Let A2 := H2^#.

Hypothesis ddA1 : Dade_hypothesis G L1 A1.
Hypothesis ddA2 : Dade_hypothesis G L2 A2.
Let Atau1 := Dade_support ddA1.
Let tau1 := Dade ddA1.
Let Atau2 := Dade_support ddA2.
Let tau2 := Dade ddA2.

Hypothesis disjointA : [disjoint Atau1 & Atau2].

Lemma disjoint_Dade_ortho phi psi : '[tau1 phi, tau2 psi] = 0.
Proof.
rewrite (cfdot_complement (Dade_cfunS _ _)) ?(cfun_onS _ (Dade_cfunS _ _)) //.
by rewrite subsetD disjoint_sym Dade_support_sub.
Qed.

Let odd_Dade_context L H : Dade_hypothesis G L H^# -> H <| L /\ odd #|L|.
Proof. by case=> nsAL sLG _ _ _; rewrite -normalD1 (oddSg sLG). Qed.

(* This lemma encapsulates uses of lemma (4.1) in sections 7 and 14. *)
Lemma disjoint_coherent_ortho nu1 nu2 chi1 chi2 :
    let S1 := seqIndD H1 L1 H1 1 in coherent_with S1 L1^# tau1 nu1 ->
    let S2 := seqIndD H2 L2 H2 1 in coherent_with S2 L2^# tau2 nu2 ->
    chi1 \in irr L1 -> chi1 \in S1 -> chi2 \in irr L2 -> chi2 \in S2 -> 
  '[nu1 chi1, nu2 chi2] = 0.
Proof.
move=> S1 cohS1 S2 cohS2 /irrP[i1 ->] Schi1 /irrP[i2 ->] Schi2.
have [[nsHL1 oddL1] [[Inu1 Znu1] nu1tau]] := (odd_Dade_context ddA1, cohS1).
have [[nsHL2 oddL2] [[Inu2 Znu2] nu2tau]] := (odd_Dade_context ddA2, cohS2).
pose nu_chiC L (nu : 'CF(L) -> 'CF(G)) i := map nu ('chi_i :: ('chi_i)^*)%CF.
have: orthonormal (nu_chiC L1 nu1 i1) && orthonormal (nu_chiC L2 nu2 i2).
  rewrite /orthonormal /= !andbT !Inu1 ?Inu2 ?seqInd_zcharW ?cfAut_seqInd //=.
  rewrite !cfnorm_conjC !cfnorm_irr (seqInd_conjC_ortho _ _ _ Schi1) ?eqxx //=.
  by rewrite (seqInd_conjC_ortho _ _ _ Schi2).
move/orthonormal_vchar_diff_ortho=> -> //.
  by split; apply/allP; rewrite /= !(Znu1, Znu2) ?seqInd_zcharW ?cfAut_seqInd.
rewrite -!raddfB !(nu1tau, nu2tau) ?zcharD1_seqInd ?seqInd_sub_aut_zchar //.
by rewrite !Dade1 disjoint_Dade_ortho !eqxx.
Qed.

(* This is Peterfalvi (7.9). *)
(* We have inlined Hypothesis (7.4) because although it is readily available  *)
(* for the proof of (7.10), it would be inconvenient to establish in (14.4).  *)
(* Note that our Delta corresponds to Delta - 1 in the Peterfalvi proof.      *)
Let beta L H ddA zeta := @Dade _ G L H^# ddA ('Ind[L, H] 1 - zeta).
Lemma Dade_sub_lin_nonorthogonal nu1 nu2 zeta1 zeta2 :
    let S1 := seqIndD H1 L1 H1 1 in coherent_with S1 L1^# tau1 nu1 -> 
    let S2 := seqIndD H2 L2 H2 1 in coherent_with S2 L2^# tau2 nu2 ->
    zeta1 \in irr L1 -> zeta1 \in S1 -> zeta1 1%g = #|L1 : H1|%:R ->
    zeta2 \in irr L2 -> zeta2 \in S2 -> zeta2 1%g = #|L2 : H2|%:R ->
  '[beta ddA1 zeta1, nu2 zeta2] != 0 \/ '[beta ddA2 zeta2, nu1 zeta1] != 0.
Proof.
move=> S1 cohS1 S2 cohS2 irr_zeta1 Szeta1 zeta1_1 irr_zeta2 Szeta2 zeta2_1.
apply/nandP; pose Delta ddA nu zeta := beta ddA zeta + nu zeta.
have Delta_context L H (A := H^#) ddA (tau := Dade ddA) nu zeta :
    let S := seqIndD H L H 1 in coherent_with S L^# tau nu ->
    zeta \in irr L -> zeta \in S -> zeta 1%g = #|L : H|%:R ->
  let D := Delta L H ddA nu zeta in '[D, 1] = 1 /\ D \in 'Z[irr G] /\ cfReal D.
- move=> S cohS irr_zeta Szeta zeta_1 D.
  have [[nsHL oddL] [[_ Znu] nu_tau]] := (odd_Dade_context ddA, cohS).
  have ntS: (size S > 1)%N by apply: seqInd_nontrivial Szeta.
  have [[nuS1_0 beta1_1 Zbeta] _ _] :=
    Dade_Ind1_sub_lin cohS ntS irr_zeta Szeta zeta_1.
  rewrite cfdotDl {}beta1_1 {nuS1_0}(orthoPr nuS1_0) ?map_f // addr0.
  rewrite rpredD ?{}Znu ?seqInd_zcharW {Zbeta}// /cfReal; do !split=> //.
  rewrite rmorphD /= -subr_eq0 opprD addrAC addrA -addrA addr_eq0 opprD.
  rewrite (cfConjC_Dade_coherent cohS) // opprK -Dade_conjC -!raddfB /=.
  rewrite nu_tau ?zcharD1_seqInd ?seqInd_sub_aut_zchar //=.
  by rewrite rmorphB /= conj_cfInd cfConjC_cfun1 opprB addrC addrA subrK.
have: ~~ (2 %| '[Delta L1 H1 ddA1 nu1 zeta1, Delta L2 H2 ddA2 nu2 zeta2])%C.
  have /Delta_context/(_ irr_zeta1 Szeta1 zeta1_1)[Delta1_1 ZR_Delta1] := cohS1.
  have /Delta_context/(_ irr_zeta2 Szeta2 zeta2_1)[Delta2_1 ZR_Delta2] := cohS2.
  by rewrite cfdot_real_vchar_even // Delta1_1 Delta2_1 (dvdC_nat 2 1).
rewrite cfdotDl !cfdotDr disjoint_Dade_ortho // add0r addrC cfdotC.
apply: contra => /andP[/eqP-> /eqP->]; rewrite conjC0 add0r addr0.
by rewrite (disjoint_coherent_ortho cohS1 cohS2) ?dvdC0.
Qed.

End DisjointDadeOrtho.

(* A numerical fact used in Sections 7 and 14. *)
Lemma odd_Frobenius_index_ler (R : numFieldType) (K L : {group gT}) :
    odd #|L| -> [Frobenius L with kernel K] ->
  #|L : K|%:R <= (#|K|%:R - 1) / 2%:R :> R.
Proof.
move=> oddL /existsP[H frobL]; rewrite ler_pdivl_mulr ?ltr0n // ler_subr_addl.
have ->: #|L : K| = #|H| by have [/index_sdprod] := Frobenius_context frobL.
by rewrite -natrM -mulrS ler_nat muln2 (ltn_odd_Frobenius_ker frobL).
Qed.

(* This final section factors the assumptions common to (7.10) and (7.11).    *)
(* We add solvability of the Frobenius groups, so as not to rely on the       *)
(* theorem of Thompson asserting the nilpotence of Frobenius kernels.         *)

Section CoherentFrobeniusPartition.

Variables (k : nat) (L H E : 'I_k -> {group gT}).

Local Notation A i := (gval (H i))^#.
Let h_ i : algC := #|H i|%:R.
Let e_ i : algC := #|L i : H i|%:R.
Let G0 := G :\: \bigcup_(i < k) class_support (H i)^# G.

Hypothesis k_ge2: (k >= 2)%N.

(*a*) Hypothesis frobeniusL_G :
  forall i, [/\ L i \subset G, solvable (L i) & [Frobenius L i = H i ><| E i]].

(*b*) Hypothesis normedTI_A : forall i, normedTI (A i) G (L i).

(*c*) Hypothesis card_coprime : forall i j, i != j -> coprime #|H i| #|H j|.

(* A numerical fact that is used in both (7.10) and (7.11) *)
Let e_bounds i : 1 < e_ i /\ e_ i <= (h_ i - 1) / 2%:R.
Proof.
have [/oddSg/(_ oddG)oddL _ frobL] := frobeniusL_G i.
rewrite ltr1n odd_Frobenius_index_ler ?(FrobeniusWker frobL) //.
by have [/index_sdprod <-] := Frobenius_context frobL; rewrite cardG_gt1.
Qed.

(* This is Peterfalvi (7.10). *)
Lemma coherent_Frobenius_bound : exists i, let e := e_ i in let h := h_ i in
  (e - 1) * ((h - 2%:R * e - 1) / (e * h) + 2%:R / (h * (h + 2%:R)))
     <= (#|G0|%:R - 1) / #|G|%:R.
Proof.
have [sLG solL frobL] := all_and3 frobeniusL_G.
have oddL i := oddSg (sLG i) oddG.
have /all_and2[nsHL ntH] i: H i <| L i /\ H i :!=: 1%g.
  by case/Frobenius_context: (frobL i) => /sdprod_context[].
have sHL i: H i \subset L i by case/andP: (nsHL i).
pose DH i := @Dade_signalizer gT G (L i) (A i).
have /fin_all_exists[ddA DH1] i: exists dd, {in A i, forall a, DH i dd a = 1%G}.
  have /Dade_normedTI_P[|ddAi _] := normedTI_A i; last by exists ddAi.
  by apply: normedTI_Dade => //; rewrite setSD // (subset_trans (sHL i)).
pose tau i := Dade (ddA i); pose rho i := invDade (ddA i).
pose Atau i := Dade_support (ddA i).
have defAtau i: Atau i = class_support (A i) G.
  rewrite class_supportEl; apply: eq_bigr => x Ax.
  by rewrite /Dade_support1 -/(DH i) DH1 // mul1g class_support_set1l.
have disjoint_Atau i j : i != j -> [disjoint Atau i & Atau j].
  move=> neq_ij; rewrite !defAtau !class_supportEr -setI_eq0 big_distrlr /=.
  rewrite pair_big big1 // => [[x y] _] /=; apply/eqP.
  by rewrite !conjD1g -setDIl setD_eq0 coprime_TIg // !cardJg card_coprime.
have{defAtau} defG0: G0 = G :\: \bigcup_i Atau i.
  by congr (_ :\: _); apply: eq_bigr => i; rewrite defAtau.
pose S i := seqIndD (H i) (L i) (H i) 1.
have irrS i: {subset S i <= irr (L i)}.
  move=> _ /seqIndC1P[t nz_t ->]; rewrite irr_induced_Frobenius_ker //.
  exact: FrobeniusWker (frobL i).
have /fin_all_exists[r lin_r] i: exists r, 'chi_r \in S i /\ 'chi_r 1%g = e_ i.
  have lt1Hi: [1] \proper H i by rewrite proper1G.
  have solHi := solvableS (sHL i) (solL i).
  have [xi Sxi lin_xi] := exists_linInd (nsHL i) solHi lt1Hi (normal1 _).
  by have /irrP[r def_xi] := irrS i xi Sxi; exists r; rewrite -def_xi.
have{lin_r} [Sr r1] := all_and2 lin_r.
have ntS i: (size (S i) > 1)%N by apply: seqInd_nontrivial (mem_irr _) (Sr i).
have /fin_all_exists[nu cohS] i: coherent (S i) (L i)^# 'Ind[G, L i].
  have [[[frobLi tiAiL] sLiG] oddLi] := (frobL i, normedTI_A i, sLG i, oddL i).
  have [defLi ntHi ntEi _ _] := Frobenius_context frobLi.
  have{ntEi} nilHi: nilpotent (H i) by apply: (Frobenius_sol_kernel_nil frobLi).
  exact: Sibley_coherence (or_introl _ frobLi).
have{cohS} [/all_and2[Inu Znu] nu_Ind] := all_and2 cohS.
have{DH DH1 nu_Ind} cohS i: coherent_with (S i) (L i)^# (tau i) (nu i).
  split=> // phi Sphi; rewrite /tau nu_Ind ?Dade_Ind //.
  by rewrite (@zchar_on _ _ (S i)) -?zcharD1_seqInd.
have n1S i xi: xi \in S i -> '[xi] = 1.
  by case/irrS/irrP=> t ->; rewrite cfnorm_irr.
have n1Snu i xi: xi \in S i -> '[nu i xi] = 1.
  by move=> Sxi; rewrite Inu ?n1S ?seqInd_zcharW.
have o_nu i j: i != j -> {in S i & S j, forall xi xj, '[nu i xi, nu j xj] = 0}.
  move/disjoint_Atau/disjoint_coherent_ortho=> o_ij xi xj Sxi Sxj.
  by rewrite o_ij ?irrS //; apply: cohS.
have /all_and2[nze nzh] i: e_ i != 0 /\ h_ i != 0 by rewrite neq0CiG neq0CG.
have h_gt1 i: 1 < h_ i by rewrite ltr1n cardG_gt1.
have eh i: e_ i * h_ i = #|L i|%:R by rewrite -natrM mulnC Lagrange.
have def_h1 i: h_ i - 1 = #|A i|%:R.
  by rewrite /h_ (cardsD1 1%g) group1 addnC natrD addrK.
have [i1 min_i1]: {i1 | forall i, i != i1 -> h_ i1 + 2%:R <= h_ i}.
  exists [arg min_(i < Ordinal k_ge2) #|H i|]; case: arg_minP => // i1 _ min_i1.
  have oddH i: #|H i| = #|H i|./2.*2.+1.
    by rewrite -{1}[#|H i|]odd_double_half (oddSg (sHL i)).
  move=> i neq_i; rewrite -natrD ler_nat (oddH i) oddH addn2 -doubleS ltnS.
  rewrite leq_double ltn_neqAle andbC half_leq ?min_i1 //=.
  apply: contraTneq (card_coprime neq_i) => eqHii1.
  by rewrite oddH -eqHii1 -oddH /coprime gcdnn -trivg_card1.
exists i1 => e h; set lhs := (e - 1) * _.
have nzh2: h + 2%:R != 0 by rewrite -natrD addnC pnatr_eq0.
have{lhs} ->: lhs = 1 - e / h - (h - 1) / (e * h) - (e - 1) / (h + 2%:R).
  rewrite {}/lhs -{2}(addrK h 2%:R) !invfM (mulrBl _ _ h) mulVKf ?nzh //.
  rewrite addrCA (addrC _ h) mulrCA mulrA addrA mulrBr; congr (_ - _).
  rewrite mulfK // mulrDr addrAC addrC mulrC mulrBl -mulrA mulVKf ?nze //.
  rewrite mulrC mulrBr mulrBl mul1r addrAC addrC addrA; congr (_ - _).
  rewrite mulrCA mulVKf ?nze // addrCA mulrCA mulr_natl opprD addNKr.
  by rewrite !mulrBl opprB addrA subrK divff ?nzh.
pose beta i := tau i ('Ind[L i, H i] 1 - 'chi_(r i)).
have betaP i := Dade_Ind1_sub_lin (cohS i) (ntS i) (mem_irr _) (Sr i) (r1 i).
pose chi i := nu i 'chi_(r i); pose c i j := '[beta i, chi j].
have:= betaP i1; rewrite -/(S _) -/(tau _) -/(beta _) -/(chi _) -/(e_ _) -/e.
move=> [[oSnu1 o_beta1 Zbeta1] [Gamma [oSnuGamma oGamma1] [a Za def_beta1]]].
have [_ lt_e_h2] := e_bounds i1; rewrite -/(rho _) -/(h_ _) -/h.
case/(_ lt_e_h2)=> min_rho1 maxGamma _ {lt_e_h2}.
pose calB := [set i | (i != i1) && (c i i1 == 0)].
pose sumB := \sum_(i in calB) (h_ i - 1) / (e_ i * h_ i).
suffices{min_rho1} sumB_max: sumB <= (e - 1) / (h + 2%:R).
  rewrite -subr_ge0 opprB addrCA -opprB subr_ge0; apply: ler_trans sumB_max.
  rewrite -subr_ge0 opprB addrCA -(opprB _ sumB) subr_ge0.
  have Zchi1: chi i1 \in 'Z[irr G] by rewrite Znu ?seqInd_zcharW ?Sr.
  have [eps [t def_chi1]] := vchar_norm1P Zchi1 (n1Snu i1 'chi_(r i1) (Sr i1)).
  pose sumG0 := \sum_(g in G0) `|'chi_t g| ^+ 2.
  apply: (@ler_trans _ ((#|G0|%:R - sumG0) / #|G|%:R)); last first.
    rewrite ler_pmul2r ?invr_gt0 ?gt0CG // ler_add2l ler_opp2.
    rewrite [sumG0](bigD1 1%g) /=; last first.
      rewrite !inE group1 andbT; apply/bigcupP=> [[i _]].
      by rewrite class_supportEr => /bigcupP[x _]; rewrite conjD1g !inE eqxx.
    rewrite -[1]addr0 ler_add ?sumr_ge0 // => [|x _]; last first.
      by rewrite -normrX normr_ge0.
    have Zchit1: 'chi_t 1%g \in Cint by rewrite CintE Cnat_irr1.
    by rewrite expr_ge1 ?normr_ge0 // norm_Cint_ge1 ?irr1_neq0.
  pose ea i : algC := #|(H i)^#|%:R / #|L i|%:R.
  apply: (@ler_trans _ (\sum_i ('[rho i 'chi_t] - ea i))); last first.
    rewrite -subr_ge0 -opprB oppr_ge0 -mulNr opprB addrC mulrC.
    by rewrite /sumG0 defG0 Dade_cover_inequality ?cfnorm_irr.
  rewrite (bigID (mem calB)) /= addrC ler_add //.
    rewrite -subr_ge0 opprK -big_split sumr_ge0 //= => i _.
    by rewrite def_h1 eh subrK cfnorm_ge0.
  rewrite (bigD1 i1) ?inE ?eqxx ?andbF //= -ler_subl_addl (@ler_trans _ 0) //.
    rewrite opprB /ea -def_h1 -eh -/h -/e addrA subrK subr_le0.
    by rewrite -(cfnorm_sign eps) -linearZ -def_chi1.
  rewrite sumr_ge0 // => i; rewrite inE /c andbC => /andP[neq_i].
  rewrite neq_i subr_ge0 def_chi1 cfdotZr mulf_eq0 => /norP[_ not_o_beta_chi].
  have [[_ _ Zbeta_i] _ /(_ _ (mem_irr t))[|_ ->]] := betaP i.
    apply/orthoPr=> _ /mapP[xi Sxi ->]; rewrite -['chi_t](signrZK eps).
    by rewrite -def_chi1 cfdotZr o_nu ?mulr0 ?Sr.
  rewrite -[ea i]mulr1 /ea ler_wpmul2l ?mulr_ge0 ?invr_ge0 ?ler0n //.
  by rewrite -/(tau i) -/(beta i) sqr_Cint_ge1 ?Cint_cfdot_vchar_irr.
rewrite -(mulfK nzh2 sumB) -{2 3}natrD ler_wpmul2r ?invr_ge0 ?ler0n //.
apply: ler_trans maxGamma; rewrite mulr_suml.
pose phi i : 'CF(G) := \sum_(xi <- S i) xi 1%g / e_ i / '[xi] *: nu i xi.
have o_phi_nu i j xi: i != j -> xi \in S j -> '[phi i, nu j xi] = 0.
  move/o_nu=> o_ij Sxi; rewrite cfdot_suml big1_seq //= => pi Spi.
  by rewrite cfdotZl o_ij ?mulr0.
have o_phi i j: i != j -> '[phi i, phi j] = 0.
  move/o_phi_nu=> o_ij; rewrite cfdot_sumr big1_seq // => xi Sxi.
  by rewrite cfdotZr o_ij ?mulr0.
pose X : 'CF(G) := \sum_(i in calB) c i1 i *: phi i; pose Gamma1 := Gamma - X.
have ->: Gamma = Gamma1 + X by rewrite subrK.
have{betaP def_beta1} /cfnormDd->: '[Gamma1, X] = 0.
  rewrite cfdot_sumr big1 // => i Bi; have [neq_i _] := setIdP Bi.
  rewrite cfdotZr cfdot_sumr big1_seq ?mulr0 //= => xi Sxi.
  apply/eqP; rewrite cfdotZr cfdotBl mulf_eq0; apply/pred2P; right.
  rewrite cfdot_suml (bigD1 i) ?big1 //= => [|j /andP[_ neq_j]]; last first.
    by rewrite cfdotZl o_phi_nu ?mulr0.
  rewrite cfdotZl cfproj_sum_orthogonal ?seqInd_orthogonal //; last exact: Inu.
  rewrite n1S // divr1 mulr1 addr0 mulrC -(canLR (addKr _) def_beta1).
  rewrite !(cfdotDl, cfdotNl) cfdotZl o_nu ?o_phi_nu ?Sr 1?eq_sym // mulr0.
  have[[/orthoPr oSnui_1 _ _] _ _] := betaP i; rewrite -/(S i) in oSnui_1.
  rewrite cfdotC oSnui_1 ?map_f // conjC0 !(add0r, oppr0).
  have Nxie: xi 1%g / e_ i \in Cnat by apply: dvd_index_seqInd1 _ Sxi.
  rewrite -(conj_Cnat Nxie) // -cfdotZr -raddfZ_Cnat // -!raddfB /=.
  have [_ Dnu] := cohS i.
  rewrite Dnu ?zcharD1_seqInd ?seqInd_sub_lin_vchar ?Sr ?r1 //.
  by rewrite disjoint_Dade_ortho ?disjoint_Atau 1?eq_sym.
rewrite -subr_ge0 cfdot_sumr -addrA -sumrB addr_ge0 ?cfnorm_ge0 //.
rewrite sumr_ge0 // => i Bi; have [neq_i ci1_0] := setIdP Bi.
have n_phi: '[phi i] = (h_ i - 1) / e_ i.
  rewrite cfnorm_sum_orthogonal ?seqInd_orthogonal //; last exact: Inu.
  rewrite -[_ - 1](mulKf (nze i)) -sum_seqIndC1_square // -/(S i) mulrAC.
  rewrite -invfM mulrC mulr_suml; apply: eq_big_seq => _ /irrS/irrP[t ->].
  rewrite cfnorm_irr !divr1 mulr1 -expr2 -exprVn -exprMn.
  by rewrite (normr_idP _) // mulr_ge0 ?invr_ge0 ?ler0n // ltrW ?irr1_gt0.
rewrite subr_ge0 cfdotZr cfdot_suml (bigD1 i) //=.
rewrite big1 ?addr0 => [|j /andP[_ ne_j]]; last by rewrite cfdotZl o_phi ?mulr0.
rewrite cfdotZl invfM 2!mulrA -n_phi -[_ * _]mulrA mulrC.
rewrite ler_wpmul2r ?cfnorm_ge0 // (@ler_trans _ 1) //.
  by rewrite -{2}(mulVf (nzh i)) ler_wpmul2l ?invr_ge0 ?ler0n ?min_i1.
rewrite mulrC -normCK expr_ge1 ?normr_ge0 // norm_Cint_ge1 //.
  rewrite Cint_cfdot_vchar ?Znu ?seqInd_zcharW ?Sr //.
suffices /orP: c i i1 != 0 \/ c i1 i != 0 by rewrite ci1_0.
apply: Dade_sub_lin_nonorthogonal; rewrite ?mem_irr ?Sr ?r1 //; try exact: cohS.
exact: disjoint_Atau.
Qed.

(* This is Peterfalvi (7.11). *)
Theorem no_coherent_Frobenius_partition : G0 != 1%G.
Proof.
have [i] := coherent_Frobenius_bound; apply: contraTneq => ->.
have [] := e_bounds i; set e := e_ i; set h := h_ i => e_gt1 le_e_h2.
rewrite cards1 subrr mul0r ltr_geF // pmulr_rgt0 ?subr_gt0 // ltr_paddl //.
  rewrite ?(mulr_ge0, invr_ge0) ?ler0n // addrAC subr_ge0.
  by rewrite -[_ - 1](@divfK _ 2%:R) ?pnatr_eq0 // mulrC ler_wpmul2r ?ler0n.
by rewrite -natrD addnC ?(pmulr_rgt0, invr_gt0) ?ltr0n.
Qed.

End CoherentFrobeniusPartition.

End Seven.

