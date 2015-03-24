(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div.
Require Import fintype bigop prime binomial finset ssralg fingroup finalg.
Require Import morphism perm automorphism quotient action commutator gproduct.
Require Import zmodp cyclic center pgroup gseries nilpotent sylow finalg.
Require Import finmodule abelian frobenius maximal extremal hall finmodule.
Require Import matrix mxalgebra mxrepresentation mxabelem BGsection1.

(******************************************************************************)
(*   This file provides the proof of the Wielandt fixpoint order formula,     *)
(* which is a prerequisite for B & G, Section 3 and Peterfalvi, Section 9.    *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GroupScope GRing.Theory.
Import FinRing.Theory.

Implicit Types (gT wT : finGroupType) (m n p q : nat).

Lemma coprime_act_abelian_pgroup_structure gT p (A X : {group gT}) :
    abelian A -> p.-group A -> p^'.-group X -> X \subset 'N(A) -> 
  exists2 s : {set {group gT}},
      \big[dprod/1]_(B in s) B = A
    & {in s, forall B : {group gT},
       [/\ homocyclic B, X \subset 'N(B)
         & acts_irreducibly X (B / 'Phi(B)) 'Q]}.
Proof.
move: {2}_.+1 (ltnSn #|A|) => m.
elim: m => // m IHm in gT A X *; rewrite ltnS => leAm cAA pA p'X nAX.
have [n1 eA]: {n | exponent A = p ^ n}%N by apply p_natP; rewrite pnat_exponent.
have [-> | ntA] := eqsVneq A 1.
  by exists set0 => [|B]; rewrite ?big_set0 ?inE.
have [p_pr _ _] := pgroup_pdiv pA ntA; have p_gt1 := prime_gt1 p_pr.
case: n1 => [|n] in eA; first by rewrite trivg_exponent eA in ntA.
have nA1X: X \subset 'N('Ohm_1(A)) := char_norm_trans (Ohm_char 1 A) nAX.
have sAnA1: 'Mho^n(A) \subset 'Ohm_1(A).
  rewrite (MhoE n pA) (OhmE 1 pA) genS //.
  apply/subsetP=> xpn; case/imsetP=> x Ax ->{xpn}; rewrite !inE groupX //.
  by rewrite -expgM -expnSr -eA -order_dvdn dvdn_exponent.
have nAnX: X \subset 'N('Mho^n(A)) := char_norm_trans (Mho_char n A) nAX.
have [B minB sBAn]: {B : {group gT} | minnormal B X & B \subset 'Mho^n(A)}.
  apply: mingroup_exists; rewrite nAnX andbT; apply/trivgPn.
  have [x Ax ox] := exponent_witness (abelian_nil cAA).
  exists (x ^+ (p ^ n)); first by rewrite Mho_p_elt ?(mem_p_elt pA).
  by rewrite -order_dvdn -ox eA dvdn_Pexp2l ?ltnn.
have abelA1: p.-abelem 'Ohm_1(A) by rewrite Ohm1_abelem.
have sBA1: B \subset 'Ohm_1(A) := subset_trans sBAn sAnA1.
case/mingroupP: minB; case/andP=> ntB nBX minB.
have{nBX sBA1} [U defA1 nUX] := Maschke_abelem abelA1 p'X sBA1 nA1X nBX.
have [_ mulBU _ tiBU] := dprodP defA1; have{mulBU} [_ sUA1] := mulG_sub mulBU.
have sUA: U \subset A := subset_trans sUA1 (Ohm_sub 1 _).
have [U1 | {defA1 minB}ntU] := eqsVneq U 1.
  rewrite U1 dprodg1 /= in defA1.
  have homoA: homocyclic A.
    apply/(Ohm1_homocyclicP pA cAA); rewrite eA pfactorK //=.
    by apply/eqP; rewrite eqEsubset sAnA1 -defA1 sBAn.
  exists [set A]; rewrite ?big_set1 // => G; move/set1P->; split=> //.
  have OhmMho: forall k, 'Ohm_k(A) = 'Mho^(n.+1 - k)(A).
    by move=> k; rewrite (homocyclic_Ohm_Mho k pA) // eA pfactorK.
  have fM: {in A &, {morph (fun x => x ^+ (p ^ n)) : x y / x * y >-> x * y}}.
    by move=> x y Ax Ay /=; rewrite expgMn // /commute -(centsP cAA).
  pose f := Morphism fM; have ker_f: 'ker f = 'Phi(A).
    apply/setP=> z; rewrite (Phi_Mho pA cAA) -(subSnn n) -OhmMho.
    by rewrite (OhmEabelian pA) ?(abelianS (Ohm_sub n A)) ?inE.
  have [g injg def_g] := first_isom f; rewrite /= {}ker_f in g injg def_g.
  have{f def_g} def_g: forall H, gval H \subset A -> g @* (H / _) = 'Mho^n(H).
    move=> H sHA; rewrite def_g morphimEsub //.
    by rewrite (MhoEabelian n (pgroupS sHA pA) (abelianS sHA cAA)).
  have im_g: g @* (A / 'Phi(A)) = B by rewrite def_g // defA1 OhmMho subn1.
  have defAb: A / 'Phi(A) = g @*^-1 B by rewrite -im_g injmK.
  have nsPhiA: 'Phi(A) <| A := Phi_normal A.
  have nPhiX: X \subset 'N('Phi(A)) := char_norm_trans (Phi_char A) nAX.
  rewrite defAb; apply/mingroupP; split=> [|Hb].
    by rewrite -(morphim_injm_eq1 injg) ?morphpreK /= -?defAb ?im_g ?ntB ?actsQ.
  case/andP=> ntHb actsXHb /= sgHbB; have [sHbA _] := subsetIP sgHbB.
  rewrite -sub_morphim_pre // in sgHbB; rewrite -(minB _ _ sgHbB) ?injmK //.
  rewrite morphim_injm_eq1 // {}ntHb {actsXHb}(subset_trans actsXHb) //=.
  have{sHbA} [H defHb sPhiH sHA] := inv_quotientS nsPhiA sHbA.
  rewrite defHb def_g // (char_norm_trans (Mho_char n H)) //.
  by rewrite astabsQ ?subsetIr ?(normalS sPhiH sHA).
have nsUA: U <| A by rewrite -sub_abelian_normal.
have nUA: A \subset 'N(U) by case/andP: nsUA.
have Au_lt_m: #|A / U| < m := leq_trans (ltn_quotient ntU sUA) leAm.
have cAuAu: abelian (A / U) := quotient_abelian _ cAA.
have pAu: p.-group (A / U) := quotient_pgroup _ pA.
have p'Xu: p^'.-group (X / U) := quotient_pgroup _ p'X.
have nXAu: X / U \subset 'N(A / U) := quotient_norms _ nAX.
have{Au_lt_m p'Xu nXAu} [S defAu simS] := IHm _ _ _ Au_lt_m cAuAu pAu p'Xu nXAu.
have sSAu: forall Ku, Ku \in S -> Ku \subset A / U.
  by move=> Ku S_Ku; rewrite -(bigdprodWY defAu) sub_gen // (bigcup_max Ku).
have{B ntB sBAn tiBU} [Ku S_Ku eKu]: exists2 Ku, Ku \in S & exponent Ku == (p ^ n.+1)%N.
  apply/exists_inP; apply: contraR ntB; rewrite negb_exists_in -subG1 -tiBU.
  move/forall_inP=> expSpn; apply/subsetP=> x Ux; rewrite inE Ux coset_idr //.
    by rewrite (subsetP nUA) // (subsetP (Mho_sub n A)) // (subsetP sBAn).
  have [y Ay ->]: exists2 y, y \in A & x = y ^+ (p ^ n).
    by apply/imsetP; rewrite -MhoEabelian ?(subsetP sBAn).
  rewrite morphX ?(subsetP nUA) // (exponentP _ _ (mem_quotient _ Ay)) //.
  rewrite -sub_Ldiv -OhmEabelian ?(abelianS (Ohm_sub n _)) //=.
  rewrite (OhmE n pAu) /= -(bigdprodWY defAu) genS // subsetI sub_gen //=. 
  apply/bigcupsP=> Ku S_Ku; rewrite sub_LdivT.
  have: exponent Ku %| p ^ n.+1.
    by rewrite (dvdn_trans (exponentS (sSAu _ S_Ku))) // -eA exponent_quotient.
  case/dvdn_pfactor=> // k le_k_n1 expKu; rewrite expKu dvdn_exp2l //.
  by rewrite -ltnS ltn_neqAle le_k_n1 -(eqn_exp2l _ _ p_gt1) -expKu expSpn.
have{sSAu} [sKuA [homoKu nKuX minKu]] := (sSAu Ku S_Ku, simS Ku S_Ku).
have [K defKu sUK sKA] := inv_quotientS nsUA sKuA.
have [cKK cKuKu] := (abelianS sKA cAA, abelianS sKuA cAuAu).
have [pK pKu] := (pgroupS sKA pA, pgroupS sKuA pAu).
have nsUK: U <| K := normalS sUK sKA nsUA; have [_ nUK] := andP nsUK.
have nKX: X \subset 'N(K).
  by rewrite -(quotientSGK nUX) ?normsG ?quotient_normG // -defKu.
pose K1 := 'Mho^1(K); have nsK1K: K1 <| K := Mho_normal 1 K.
have nXKb: X / K1 \subset 'N(K / K1) by exact: quotient_norms.
pose K'u := \big[dprod/1]_(Bu in S :\ Ku) Bu.
have{S_Ku} defAu_K: K / U \x K'u = A / U by rewrite -defKu -big_setD1.
have [[_ Pu _ defK'u]] := dprodP defAu_K; rewrite defK'u => mulKPu _ tiKPu.
have [_ sPuA] := mulG_sub mulKPu.
have [P defPu sUP sPA] := inv_quotientS nsUA sPuA.
have{simS defK'u} nPX: X \subset 'N(P).
  rewrite -(quotientSGK nUX) ?normsG // quotient_normG ?(normalS sUP sPA) //.
  rewrite -defPu -(bigdprodWY defK'u) norms_gen ?norms_bigcup //.
  by apply/bigcapsP=> Bu; case/setD1P=> _; case/simS.
have abelKb: p.-abelem (K / K1).
  by rewrite -[K1](Phi_Mho pK) ?Phi_quotient_abelem.
have p'Xb: p^'.-group (X / K1) := quotient_pgroup _ p'X.
have sUKb: U / K1 \subset K / K1 := quotientS _ sUK.
have nUXb: X / K1 \subset 'N(U / K1) := quotient_norms _ nUX.
have tiUK1: U :&: K1 = 1.
  apply/trivgP; apply/subsetP=> xp; case/setIP=> Uxp K1xp.
  have{K1xp} [x Kx def_xp]: exists2 x, x \in K & xp = x ^+ p.
    by apply/imsetP; rewrite -(MhoEabelian 1).
  suffices A1x: x \in 'Ohm_1(A).
    by rewrite def_xp inE; case/abelemP: abelA1 => // _ ->.
  have nUx: x \in 'N(U) := subsetP nUK x Kx.
  rewrite -sub1set -(quotientSGK _ sUA1) ?quotient_set1 ?sub1set //.
  apply: (subsetP (quotientS U (subset_trans (MhoS n sKA) sAnA1))).
  rewrite quotientE morphim_Mho //= -quotientE -defKu.
  have ->: 'Mho^n(Ku) = 'Ohm_1(Ku).
    by rewrite (homocyclic_Ohm_Mho 1 pKu) // (eqP eKu) pfactorK ?subn1.
  rewrite (OhmE 1 pKu) ?mem_gen // !inE defKu mem_quotient //=.
  by rewrite -morphX //= -def_xp coset_id.
have [Db defKb nDXb] := Maschke_abelem abelKb p'Xb sUKb nXKb nUXb.
have [_ mulUDb _ tiUDb] := dprodP defKb; have [_ sDKb] := mulG_sub mulUDb.
have [D defDb sK1D sDK] := inv_quotientS (Mho_normal 1 K) sDKb.
have nK1X: X \subset 'N(K1) := char_norm_trans (Mho_char 1 K) nKX.
have [cDU [sK1K nK1K]] := (centSS sUK sDK cKK, andP nsK1K).
have nDX: X \subset 'N(D).
  rewrite -(quotientSGK nK1X) ?normsG // quotient_normG ?(normalS _ sDK) //.
  by rewrite -defDb.
have{mulUDb} mulUD: U * D = K.
  rewrite (centC cDU) -(mulSGid sK1D) -mulgA -(centC cDU).
  rewrite -quotientK ?quotientMr ?(subset_trans _ nK1K) ?mul_subG // -defDb.
  by rewrite mulUDb quotientGK.
have cKP: P \subset 'C(K) := centSS sPA sKA cAA.
have mulKP: K * P = A.
  rewrite -(mulSGid sUK) -mulgA -(quotientGK nsUA) -mulKPu defPu.
  by rewrite -quotientK ?quotientMr ?mul_subG ?(subset_trans _ nUA).
have defKP: K :&: P = U.
  apply/eqP; rewrite eqEsubset subsetI sUK sUP !andbT.
  by rewrite -quotient_sub1 ?subIset ?nUK // -tiKPu defPu quotientI.
have tiUD: U :&: D = 1.
  apply/trivgP; rewrite -tiUK1 subsetI subsetIl.
  rewrite -quotient_sub1; last by rewrite subIset ?(subset_trans sUK).
  by rewrite -tiUDb defDb quotientI.
have tiDP: D :&: P = 1 by rewrite -(setIidPl sDK) -setIA defKP setIC.
have mulDP: D * P = A by rewrite -(mulSGid sUP) mulgA -(centC cDU) mulUD.
have sDA := subset_trans sDK sKA.
have defA: D \x P = A by rewrite dprodE // (centSS sPA sDA).
have ntD: D :!=: 1.
  apply: contraNneq ntA => D1; rewrite trivg_exponent eA -(eqP eKu).
  rewrite -trivg_exponent -subG1 -tiKPu defKu subsetIidl defPu quotientS //.
  by rewrite -(mul1g P) -D1 mulDP.
have ltPm: #|P| < m.
  by rewrite (leq_trans _ leAm) // -(dprod_card defA) ltn_Pmull ?cardG_gt1.
have [cPP pP] := (abelianS sPA cAA, pgroupS sPA pA).
have{S defAu K'u defAu_K} [S defP simS] := IHm _ _ _ ltPm cPP pP p'X nPX.
exists (D |: S) => [ | {defP}B].
  rewrite big_setU1 ?defP //=; apply: contra ntD => S_D.
  by rewrite -subG1 -tiDP subsetIidl -(bigdprodWY defP) sub_gen ?(bigcup_max D).
case/setU1P=> [-> {B S simS} | ]; last exact: simS.
have [[pD cDD] nUD] := (pgroupS sDA pA, abelianS sDA cAA, subset_trans sDA nUA).
have isoD: D \isog Ku by rewrite defKu -mulUD quotientMidl quotient_isog.
rewrite {isoD}(isog_homocyclic isoD); split=> //.
have nPhiDX: X \subset 'N('Phi(D)) := char_norm_trans (Phi_char D) nDX.
have [f [injf im_f act_f]]:
  exists f : {morphism D / 'Phi(D) >-> coset_of 'Phi(Ku)},
    [/\ 'injm f, f @* (D / 'Phi(D)) = Ku / 'Phi(Ku)
      &  {in D / 'Phi(D) & X, morph_act 'Q 'Q f (coset U)}].
- have [/= injf im_f] := isomP (quotient_isom nUD tiUD).
  set f := restrm nUD (coset U) in injf im_f.
  rewrite -quotientMidl mulUD -defKu in im_f.
  have fPhiD: f @* 'Phi(D) = 'Phi(Ku) by rewrite -im_f (morphim_Phi _ pD).
  rewrite -['Phi(Ku)]/(gval 'Phi(Ku)%G) -(group_inj fPhiD).
  exists (quotm_morphism [morphism of f] (Phi_normal _)).
  rewrite (injm_quotm _ injf) morphim_quotm /= -/f im_f.
  split=> // yb x; case/morphimP=> y Ny Dy ->{yb} Xx.
  have [nPhiDx nUx] := (subsetP nPhiDX x Xx, subsetP nUX x Xx).
  have Dyx: y ^ x \in D by rewrite memJ_norm // (subsetP nDX).
  rewrite quotmE // !qactE ?qact_domE ?subsetT ?astabsJ ?quotmE //=.
  - by congr (coset _ _); rewrite /f /restrm morphJ // (subsetP nUD).
  - by rewrite (subsetP (morphim_norm _ _)) ?mem_morphim.
  rewrite morphim_restrm  (setIidPr (Phi_sub _)).
  by rewrite (subsetP (morphim_norm _ _)) ?mem_quotient.
apply/mingroupP; split=> [|Y].
  rewrite -subG1 quotient_sub1 ?(normal_norm (Phi_normal _)) //.
  by rewrite proper_subn ?Phi_proper // actsQ.
case/andP=> ntY actsXY sYD; have{minKu} [_ minKu] := mingroupP minKu.
apply: (injm_morphim_inj injf); rewrite // im_f.
apply: minKu; last by rewrite /= -im_f morphimS.
rewrite morphim_injm_eq1 // ntY.
apply/subsetP=> xb; case/morphimP=> x Nx Xx ->{xb}.
rewrite 2!inE /= qact_domE ?subsetT // astabsJ.
rewrite (subsetP (char_norm_trans (Phi_char _) nKuX)) ?mem_quotient //=.
apply/subsetP=> fy; case/morphimP=> y Dy Yy ->{fy}.
by rewrite inE /= -act_f // morphimEsub // mem_imset // (acts_act actsXY).
Qed.

CoInductive is_iso_quotient_homocyclic_sdprod gT (V G : {group gT}) m : Prop := 
  IsoQuotientHomocyclicSdprod wT (W D G1 : {group wT}) (f : {morphism D >-> gT})
   of homocyclic W & #|W| = (#|V| ^ m)%N
    & 'ker f = 'Mho^1(W) & f @* W = V & f @* G1 = G & W ><| G1 = D.

Lemma iso_quotient_homocyclic_sdprod gT (V G : {group gT}) p m :
    minnormal V G -> coprime p #|G| -> p.-abelem V -> m > 0 ->
  is_iso_quotient_homocyclic_sdprod V G m.
Proof.
move=> minV copG abelV m_gt0; pose q := (p ^ m)%N.
have [ntV nVG] := andP (mingroupp minV).
have [p_pr pVdvdn [n Vpexpn]] := pgroup_pdiv (abelem_pgroup abelV) ntV.
move/(abelem_mx_irrP abelV ntV nVG): (minV) => mx_irrV.
have dim_lt0 : 'dim V > 0 by rewrite (dim_abelemE abelV) // Vpexpn pfactorK.
have q_gt1: q > 1 by rewrite (ltn_exp2l 0) // prime_gt1.
have p_q: p.-nat q by rewrite pnat_exp pnat_id.
have p_dv_q: p %| q := dvdn_exp2l p m_gt0.
pose rG := regular_repr [comUnitRingType of 'Z_q] G; pose MR_G := ('MR rG)%gact.
have [wT [fL injL [fX injX fJ]]]: exists wT : finGroupType,
    exists2 fL : {morphism setT >-> wT}, 'injm fL &
    exists2 fX : {morphism G >-> wT}, 'injm fX &
  {in setT & G, morph_act MR_G 'J fL fX}.
- exists (sdprod_groupType MR_G).
  exists (sdpair1_morphism MR_G); first exact: injm_sdpair1.
  by exists (sdpair2_morphism MR_G); [exact: injm_sdpair2 | exact: sdpair_act].
move imfL: (fL @* [set: _])%G => L; move imfX: (fX @* G)%G => X.
have cLL: abelian L by rewrite -imfL morphim_abelian // zmod_abelian.
have pL: p.-group L.
  by rewrite -imfL morphim_pgroup -?pnat_exponent ?exponent_mx_group.
have tiVG: V :&: G = 1 by rewrite coprime_TIg // Vpexpn coprime_pexpl.
have{copG} p'G: p^'.-group G by rewrite /pgroup p'natE // -prime_coprime.
have p'X: p^'.-group X by rewrite -imfX morphim_pgroup.
have nXL: X \subset 'N(L).
  rewrite -imfX -imfL; apply/subsetP=> _ /morphimP[x Gx _ ->]; rewrite inE.
  apply/subsetP=> _ /imsetP[_ /morphimP[v rVv _ ->] ->].
  by rewrite -fJ // mem_morphim ?in_setT.
have [/= S defL im_S] := coprime_act_abelian_pgroup_structure cLL pL p'X nXL.
pose gi (z : 'Z_q) := z%:R : 'F_p.
have giM: rmorphism gi.
  split=> [z1 z2|]; last split=> // z1 z2.
    apply: canRL (addrK _) _; apply: val_inj.
    by rewrite -{2}(subrK z2 z1) -natrD /= !val_Fp_nat ?modn_dvdm // Zp_cast.
  by apply: val_inj; rewrite -natrM /= !val_Fp_nat ?modn_dvdm // Zp_cast.
have [gL [DgL _ _ _]] := domP (invm_morphism injL) (congr_group imfL).
pose g u := map_mx (RMorphism giM) (gL u).
have gM: {in L &, {morph g : u v / u * v}}.
  by move=> u v Lu Lv /=; rewrite {1}/g morphM // map_mxD.
have kerg: 'ker (Morphism gM) = 'Phi(L).
  rewrite (Phi_Mho pL cLL) (MhoEabelian 1 pL cLL).
  apply/setP=> u; apply/idP/imsetP=> [ | [v Lv ->{u}]]; last first.
    rewrite !inE groupX //=; apply/eqP/rowP=> i; apply: val_inj.
    rewrite !mxE morphX // mulmxnE Zp_mulrn /= val_Fp_nat //=.
    by move: {i}(_ i); rewrite Zp_cast // => vi; rewrite modn_dvdm // modnMl.
  case/morphpreP; rewrite -{1}imfL => /morphimP[v rVv _ ->{u}] /set1P /=.
  rewrite /g DgL /= invmE // => /rowP vp0.
  pose x := fL (map_mx (fun t : 'Z_q => (t %/ p)%:R) v).
  exists x; first by rewrite -imfL mem_morphim ?inE.
  rewrite -morphX ?in_setT //; congr (fL _); apply/rowP=> i.
  rewrite mulmxnE -{1}(natr_Zp (v 0 i)) {1}(divn_eq (v 0 i) p) addnC.
  by have:= congr1 val (vp0 i); rewrite !mxE -mulrnA /= val_Fp_nat // => ->.
have [gX [DgX KgX _ imgX]] := domP (invm_morphism injX) (congr_group imfX).
pose aG := regular_repr [fieldType of 'F_p] G.
have GgX: {in X, forall x, gX x \in G}.
  by rewrite DgX -imfX => _ /morphimP[x Gx _ ->]; rewrite /= invmE.
have XfX: {in G, forall x, fX x \in X}.
  by move=> x Gx; rewrite -imfX mem_morphim.
have gJ: {in L & X, forall u x, g (u ^ x) = g u *m aG (gX x)}.
  rewrite -{1}imfL -{1}imfX => _ _ /morphimP[u rVu _ ->] /morphimP[x Gx _ ->].
  rewrite -fJ // /g DgL DgX /= !invmE // mx_repr_actE ?inE //.
  by rewrite (map_mxM (RMorphism giM)) map_regular_mx.
pose gMx U := rowg_mx (Morphism gM @* U).
have simS: forall U, U \in S -> mxsimple aG (gMx U).
  move=> U S_U; have [_ nUX irrU] := im_S U S_U.
  have{irrU} [modU irrU] := mingroupP irrU; have{modU} [ntU _] := andP modU.
  have sUL: U \subset L by rewrite -(bigdprodWY defL) sub_gen // (bigcup_max U).
  split=> [||U2 modU2].
  - rewrite (eqmx_module _ (genmxE _)); apply/mxmoduleP=> x Gx.
    apply/row_subP=> i; rewrite row_mul rowK.
    have [u Lu Uu def_u] := morphimP (enum_valP i).
    rewrite -(invmE injX Gx) -DgX def_u -gJ ?XfX //.
    set ux := u ^ _; apply: eq_row_sub (gring_index _ (g ux)) _.
    have Uux: ux \in U by rewrite memJ_norm // (subsetP nUX) ?XfX.
    by rewrite rowK gring_indexK //; apply: mem_morphim; rewrite ?(subsetP sUL).
  - apply: contra ntU; rewrite rowg_mx_eq0.
    rewrite -subG1 sub_morphim_pre // -kerE kerg => sU_Phi.
    rewrite /= quotientS1 //=; rewrite (big_setD1 U) //= in defL.
    have{defL} [[_ U' _ ->] defUU' cUU' tiUU'] := dprodP defL.
    have defL: U \* U' = L by rewrite cprodE.
    have:= cprod_modl (Phi_cprod pL defL) (Phi_sub U).
    rewrite -(setIidPl (Phi_sub U')) setIAC -setIA tiUU' setIg1 cprodg1 => ->.
    by rewrite subsetIidr.
  rewrite -!rowgS stable_rowg_mxK /= => [sU2gU nzU2|]; last first.
    apply/subsetP=> z _; rewrite !inE /=; apply/subsetP=> u gUu.
    by rewrite inE /= /scale_act -[val z]natr_Zp scaler_nat groupX.
  rewrite sub_morphim_pre // -subsetIidl.
  rewrite -(quotientSGK (normal_norm (Phi_normal U))) //=; last first.
    rewrite subsetI Phi_sub (subset_trans (PhiS pL sUL)) //.
    by rewrite -kerg ker_sub_pre.
  rewrite [(U :&: _) / _]irrU //; last by rewrite quotientS ?subsetIl.
  rewrite (contra _ nzU2) /=; last first.
    rewrite -subG1 quotient_sub1; last first.
      by rewrite subIset // normal_norm // Phi_normal.
    rewrite /= -(morphpre_restrm sUL).
    move/(morphimS (restrm_morphism sUL (Morphism gM))).
    rewrite morphpreK ?im_restrm // morphim_restrm => s_U2_1.
    rewrite -trivg_rowg -subG1 (subset_trans s_U2_1) //.
    rewrite -(morphim_ker (Morphism gM)) morphimS // kerg.
    by rewrite subIset ?(PhiS pL) ?orbT.
  rewrite actsQ //; first by rewrite (char_norm_trans (Phi_char U)).
  rewrite normsI //; apply/subsetP=> x Xx; rewrite inE.
  apply/subsetP=> _ /imsetP[u g'U2u ->].
  have [Lu U2gu] := morphpreP g'U2u; rewrite mem_rowg in U2gu.
  rewrite inE memJ_norm ?(subsetP nXL) // Lu /= inE gJ //.
  by rewrite mem_rowg (mxmodule_trans modU2) ?GgX.
have im_g: Morphism gM @* L = [set: 'rV_#|G|].
  apply/eqP; rewrite eqEcard subsetT cardsT card_matrix card_Fp //= mul1n.
  rewrite card_morphim kerg setIid (Phi_Mho pL cLL) -divgS ?Mho_sub //.
  rewrite -(mul_card_Ohm_Mho_abelian 1 cLL) mulnK ?cardG_gt0 //.
  rewrite (card_pgroup (pgroupS (Ohm_sub 1 L) pL)) -rank_abelian_pgroup //.
  by rewrite -imfL (injm_rank injL) //= rank_mx_group mul1n.
have sumS: (\sum_(U in S) gMx U :=: 1%:M)%MS.
  apply/eqmxP; rewrite submx1; apply/rV_subP=> v _.
  have: v \in Morphism gM @* L by rewrite im_g inE.
  case/morphimP=> u Lu _ ->{v}.
  rewrite -mem_rowg -sub1set -morphim_set1 // sub_morphim_pre ?sub1set //.
  have [c [Uc -> _]] := mem_bigdprod defL Lu; rewrite group_prod //= => U S_U.
  have sUL: U \subset L by rewrite -(bigdprodWY defL) sub_gen // (bigcup_max U).
  rewrite inE (subsetP sUL) ?Uc // inE mem_rowg (sumsmx_sup U) // -mem_rowg.
  by rewrite (subsetP (sub_rowg_mx _)) // mem_morphim ?(subsetP sUL) ?Uc.
have Fp'G: [char 'F_p]^'.-group G.
  by rewrite (eq_p'group _ (charf_eq (char_Fp p_pr))).
have [VK [modVK defVK]] := rsim_regular_submod mx_irrV Fp'G.
have [U S_U isoUV]: {U | U \in S & mx_iso (regular_repr _ G) (gMx U) VK}.
  apply: hom_mxsemisimple_iso (scalar_mx_hom _ 1 _) _ => [|U S_U _|]; auto.
    by apply/(submod_mx_irr modVK); exact: (mx_rsim_irr defVK).
  by rewrite mulmx1 sumS submx1.
have simU := simS U S_U; have [modU _ _] := simU.
pose rV := abelem_repr abelV ntV nVG.
have{VK modVK defVK isoUV} [h dimU h_free hJ]: mx_rsim (submod_repr modU) rV.
  by apply: mx_rsim_trans (mx_rsim_sym defVK); exact/mx_rsim_iso.
have sUL : U \subset L.
  by move: defL; rewrite (big_setD1 U) //= => /dprodP[[_ U1 _ ->] /mulG_sub[]].
pose W := [set: 'rV['Z_(p ^ m)](V)]%G.
have [homU nUX _] := im_S U S_U; have [cUU _] := andP homU.
have atypeU: abelian_type U == nseq ('dim V) (p ^ m)%N.
  rewrite (big_setD1 U) //= in defL.
  have [[_ U' _ defU'] defUU' _ tiUU'] := dprodP defL.
  rewrite defU' in defL defUU' tiUU'.
  have ->: 'dim V = 'r(U).
    apply/eqP; rewrite -dimU -(eqn_exp2l _ _ (prime_gt1 p_pr)).
    rewrite (rank_abelian_pgroup (pgroupS sUL pL) cUU).
    rewrite -(card_pgroup (pgroupS (Ohm_sub 1 U) (pgroupS sUL pL))).
    rewrite -{1}(card_Fp p_pr) -card_rowg stable_rowg_mxK; last first.
      apply/subsetP=> z _; rewrite !inE; apply/subsetP=> v gUv.
      by rewrite inE /= /scale_act -(natr_Zp (val z)) scaler_nat groupX.
    rewrite card_morphim kerg (Phi_Mho pL cLL) (setIidPr sUL) -divgI setIC.
    rewrite -(dprod_modl (Mho_dprod 1 defL) (Mho_sub 1 U)).
    rewrite [_ :&: _](trivgP _); last by rewrite -tiUU' setIC setSI ?Mho_sub.
    by rewrite dprodg1 -(mul_card_Ohm_Mho_abelian 1 cUU) mulnK ?cardG_gt0.
  have isoL: isog L [set: 'rV['Z_q]_#|G|] by rewrite -imfL isog_sym sub_isog.
  have homL: homocyclic L by rewrite (isog_homocyclic isoL) mx_group_homocyclic.
  have [-> _] := abelian_type_dprod_homocyclic defL pL homL.
  by rewrite (exponent_isog isoL) // exponent_mx_group.
have pU: p.-group U by rewrite (pgroupS sUL).
have isoWU: isog U W.
  by rewrite eq_abelian_type_isog ?zmod_abelian // abelian_type_mx_group ?mul1n.
have {cUU atypeU} cardU : #|U| = (#|V| ^ m)%N.
  rewrite card_homocyclic // (exponent_isog isoWU) exponent_mx_group //.
  rewrite -size_abelian_type // (eqP atypeU) size_nseq.
  by rewrite (dim_abelemE abelV) // Vpexpn pfactorK // expnAC.
pose f3 w := rVabelem abelV ntV (in_submod _ (g w) *m h).
have f3M: {in U &, {morph f3: w1 w2 / w1 * w2}}.
  move=> w1 w2 Uw1 Uw2 /=; rewrite {1}/f3.
  rewrite gM ?(subsetP sUL) // linearD mulmxDl.
  by rewrite morphM ?mem_im_abelem_rV.
have Ugw w : w \in U -> (g w <= gMx U)%MS.
  move=> Uw; rewrite -mem_rowg (subsetP (sub_rowg_mx _)) //.
  by rewrite (mem_morphim (Morphism gM)) ?(subsetP sUL).
have KgU: 'ker_U (Morphism gM) = 'Mho^1(U).
  rewrite kerg (Phi_Mho pL cLL); rewrite (big_setD1 U) //= in defL.
  have [[_ U' _ defU'] _ _ tiUU'] := dprodP defL; rewrite defU' in defL tiUU'.
  rewrite setIC -(dprod_modl (Mho_dprod 1 defL) (Mho_sub 1 U)).
  by rewrite [_ :&: _](trivgP _) ?dprodg1 // -tiUU' setIC setSI ?Mho_sub.
have{KgU} Kf3: 'ker (Morphism f3M) = 'Mho^1(U).
  apply/setP=> w; rewrite !inE /=.
  rewrite morph_injm_eq1 ?rVabelem_injm ?mem_im_abelem_rV //=.
  rewrite -[1](mul0mx _ h) (inj_eq (row_free_inj h_free)) in_submod_eq0.
  case Uw: (w \in U) => /=; last first.
    by apply/sym_eq; apply: contraFF Uw; apply: (subsetP (Mho_sub _ _)).
  rewrite -[(_ <= _)%MS]andTb -(Ugw _ Uw) -sub_capmx capmx_compl submx0.
  by rewrite -KgU !inE Uw (subsetP sUL).
have cUU: abelian U := abelianS sUL cLL.
have im_f3: Morphism f3M @* U = V.
  apply/eqP; rewrite eqEcard card_morphim setIid Kf3; apply/andP; split.
    by apply/subsetP=> _ /morphimP[w _ _ ->]; apply: mem_rVabelem.
  rewrite -divgS ?Mho_sub // -(mul_card_Ohm_Mho_abelian 1 cUU).
  rewrite mulnK ?cardG_gt0 // (card_pgroup (pgroupS (Ohm_sub 1 U) pU)).
  rewrite -rank_abelian_pgroup // (isog_rank isoWU) /W.
  by rewrite (dim_abelemE abelV) // rank_mx_group mul1n Vpexpn pfactorK.
have f3J: {in U & X, morph_act 'J 'J (Morphism f3M) gX}.
  move=> u x Uu Xx; rewrite /f3 /= gJ ?(subsetP sUL) // in_submodJ ?Ugw //.
  by rewrite -mulmxA hJ ?GgX // mulmxA rVabelemJ ?GgX.
have defUX: U ><| X = U <*> X.
  rewrite norm_joinEr; last by case: (im_S _ S_U).
  by rewrite sdprodE ?coprime_TIg ?(pnat_coprime pU).
pose f := sdprodm defUX f3J.
have{im_f3} fU_V: f @* U = V by rewrite morphim_sdprodml.
have fX_G: f @* X = G by rewrite morphim_sdprodmr // imgX -imfX im_invm.
suffices: 'ker f = 'Mho^1(U) by exists wT U (U <*> X)%G X [morphism of f].
rewrite -Kf3; apply/setP=> y; apply/idP/idP; last first.
  move=> /morphpreP[/= Uy /set1P f3y].
  by rewrite !inE /= sdprodmEl //= f3y (subsetP (joing_subl _ X)) /=.
rewrite ker_sdprodm => /imset2P[u t Uu /setIdP[Xt /eqP/= fu] ->{y}].
have: f3 u \in V :&: G.
  by rewrite inE -fU_V morphim_sdprodml //= mem_imset ?setIid // fu GgX.
rewrite tiVG in_set1 fu morph_injm_eq1 ?KgX ?injm_invm // => /eqP t1.
by rewrite t1 invg1 mulg1 !inE Uu /= fu t1 morph1.
Qed.

Theorem solvable_Wielandt_fixpoint (I : finType) gT (A : I -> {group gT})
                                   (n m : I -> nat) (G V : {group gT}) :
    (forall i, m i + n i > 0 -> A i \subset G) ->
    G \subset 'N(V) -> coprime #|V| #|G| -> solvable V ->
    {in G, forall a, \sum_(i | a \in A i) m i = \sum_(i | a \in A i) n i}%N ->
  (\prod_i #|'C_V(A i)| ^ (m i * #|A i|) 
     = \prod_i #|'C_V(A i)| ^ (n i * #|A i|))%N.
Proof.
move: {2}_.+1 (ltnSn #|V|) => c leVc sA_G nVG coVG solV partG; move: leVc.
pose nz_k i := (0 < m i + n i)%N; rewrite !(bigID nz_k xpredT) /= {2 4}/nz_k.
rewrite !(big1 _ (predC _)) /= => [|i|i]; try by case: (m i) (n i) => [[]|].
pose sum_k A_ a k := (\sum_(i | (a \in (A_ i : {set _})) && nz_k i) k i)%N.
have{partG} partG: {in G, forall a, sum_k _ A a m = sum_k _ A a n}.
  move=> a /partG; rewrite !(bigID nz_k (fun i => a \in _)) -!/(sum_k _ A a _).
  by rewrite /= !big1 ?addn0 /nz_k // => i /andP[_]; case: (m i) (n i) => [[]|].
rewrite !muln1; elim: c => // c IHc in gT G A V nVG coVG solV partG sA_G *.
rewrite ltnS => leVc; have [-> | ntV] := eqsVneq V 1.
  by rewrite !big1 // => i _; rewrite setI1g cards1 exp1n.
have nsVVG: V <| V <*> G by rewrite normalYl.
without loss{c leVc IHc} minV: / minnormal V (V <*> G).
  have [B minB sBV]: {B : {group gT} | minnormal B (V <*> G) & B \subset V}.
    by apply: mingroup_exists; rewrite ntV normal_norm.
  have [nBVG ntB abB] := minnormal_solvable minB sBV solV.
  have [nBV nBG] := joing_subP nBVG; have solB := solvableS sBV solV.
  have [{1}<- -> // | ltBV _] := eqVproper sBV.
  have ltBc: #|B| < c := leq_trans (proper_card ltBV) leVc.
  have coBG: coprime #|B| #|G| := coprimeSg sBV coVG.
  have factorCA_B k i: nz_k i ->  
    (#|'C_B(A i)| ^ (k i * #|A i|) * #|'C_(V / B)(A i / B)| ^ (k i * #|A i / B|)
      = #|'C_V(A i)| ^ (k i * #|A i|))%N.
  - move/sA_G => sAiG; have nBAi := subset_trans sAiG nBG.
    have [coVAi coBAi] := (coprimegS sAiG coVG, coprimegS sAiG coBG).
    rewrite -(card_isog (quotient_isog _ _)) ?(coprime_TIg coBAi) // -expnMn.
    rewrite -coprime_quotient_cent // -{1}(setIidPr sBV) setIAC.
    by rewrite card_quotient ?LagrangeI // subIset ?nBV.
  rewrite -!{1}(eq_bigr _ (factorCA_B _)) {factorCA_B} !big_split /=.
  pose A_B i := A i / B; congr (_ * _)%N; first exact: (IHc _ G).
  have: #|V / B| < c by apply: leq_trans leVc; rewrite ltn_quotient.
  have (i): nz_k i -> A i / B \subset G / B by move/sA_G/quotientS->.
  apply: IHc; rewrite ?morphim_sol ?coprime_morph ?quotient_norms //.
  move=> _ /morphimP[a Na Ga ->].
  suffices eqAB: sum_k _ A_B (coset B a) =1 sum_k _ A a by rewrite !eqAB partG.
  move=> k; apply: eq_bigl => i; apply: andb_id2r => /sA_G sAiG.
  rewrite -sub1set -quotient_set1 // quotientSK ?sub1set //.
  by rewrite -{2}(mul1g (A i)) -(coprime_TIg coBG) setIC group_modr // inE Ga.
have /is_abelemP[p p_pr abelV] := minnormal_solvable_abelem minV solV.
have [p_gt1 [pV cVV _]] := (prime_gt1 p_pr, and3P abelV).
have{minV} minV: minnormal V G.
  apply/mingroupP; split=> [|B nBG sBV]; first by rewrite ntV nVG.
  by case/mingroupP: minV => _ -> //; rewrite join_subG (sub_abelian_norm cVV).
have co_pG: coprime p #|G|.
  by have [_ _ [e oV]] := pgroup_pdiv pV ntV; rewrite oV coprime_pexpl in coVG.
have p'G: p^'.-group G by rewrite pgroupE p'natE -?prime_coprime.
pose rC i := logn p #|'C_V(A i)|.
have ErC k i: (#|'C_V(A i)| ^ (k i * #|A i|) = p ^ (rC i * k i * #|A i|))%N.
  suffices /card_pgroup->: p.-group 'C_V(A i) by rewrite -expnM mulnA.
  by rewrite (pgroupS (subsetIl _ _)).
rewrite !{1}(eq_bigr _ (fun i _ => ErC _ i)) {ErC} -!expn_sum; congr (_ ^ _)%N.
have eqmodX x y: (forall e, x = y %[mod p ^ e]) -> x = y.
  pose e := maxn x y; move/(_ e); have:= ltn_expl e p_gt1.
  by rewrite gtn_max /= => /andP[x_ltq y_ltq]; rewrite !modn_small.
apply: eqmodX => e; have [-> | e_gt0] := posnP e; first by rewrite !modn1.
set q := (p ^ e)%N; have q_gt1: q > 1 by rewrite -(exp1n e) ltn_exp2r.
have{e_gt0 co_pG} [wT W D G1 f homoW oW kerf imfW imfG1 defD] := 
  iso_quotient_homocyclic_sdprod minV co_pG abelV e_gt0.
have [[cWW _] [_ /mulG_sub[sWD sG1D] nWG1 tiWG1]] := (andP homoW, sdprodP defD).
have pW: p.-group W by rewrite /pgroup oW pnat_exp [p.-nat _]pV.
have rW_V: 'r(W) = 'dim V.
  rewrite (rank_abelian_pgroup pW cWW) -(mulnK #|_| (cardG_gt0 'Mho^1(W))).
  rewrite mul_card_Ohm_Mho_abelian // divg_normal ?Mho_normal //=.
  rewrite -(setIidPr (Mho_sub 1 W)) -kerf.
  by rewrite (card_isog (first_isog_loc _ _)) //= imfW (dim_abelemE abelV).
have expW: exponent W = q.
  apply/eqP; rewrite -(@eqn_exp2r _ _ ('dim V)) // -{1}rW_V -expnM mulnC expnM.
  by rewrite (dim_abelemE abelV) -?card_pgroup // -oW eq_sym max_card_abelian.
have{rW_V} /isogP[fW injfW im_fW]: [set: 'rV['Z_q](V)] \isog W.
  rewrite eq_abelian_type_isog ?zmod_abelian // abelian_type_mx_group ?mul1n //.
  by rewrite abelian_type_homocyclic // rW_V expW.
have WfW u: fW u \in W by rewrite -im_fW mem_morphim ?inE.
have [fW' [DfW' KfW' _ _]] := domP (invm_morphism injfW) im_fW.
have{KfW'} injfW': 'injm fW' by rewrite KfW' injm_invm.
have fW'K: {in W, cancel fW' fW} by move=> w Ww; rewrite DfW' invmK //= im_fW.
have toWlin a1: linear (fun u => fW' (fW u ^ val (subg G1 a1))).
  move=> z /= x y; rewrite (morphM fW) /= ?in_setT // conjMg /=.
  rewrite morphM ?memJ_norm ?(subsetP nWG1) ?subgP //=; congr (_ * _).
  rewrite -(natr_Zp z) !scaler_nat morphX ?in_setT // conjXg morphX //.
  by rewrite memJ_norm // (subsetP nWG1) ?subgP.
pose rW a1 := lin1_mx (Linear (toWlin a1)).
pose fG := restrm sG1D f; have im_fG : fG @* G1 = G by rewrite im_restrm.
have injfG: 'injm fG by rewrite -tiWG1 setIC ker_restrm kerf setIS ?Mho_sub.
pose fG' := invm injfG; have im_fG': fG' @* G = G1 by rewrite -im_fG im_invm.
pose gamma i := \sum_(a in A i) rW (fG' a).
suffices{sum_k partG} tr_rW_Ai i: nz_k i -> \tr (gamma i) = (rC i * #|A i|)%:R.
  have Dtr k i: nz_k i -> (rC i * k i * #|A i|)%:R = \tr (gamma i *+ k i).
    by rewrite mulnAC natrM raddfMn mulr_natr /= => /tr_rW_Ai->.
  rewrite -!val_Zp_nat // !natr_sum !{1}(eq_bigr _ (Dtr _)){Dtr}; congr (val _).
  rewrite -!raddf_sum -!(eq_bigr _ (fun i _ => sumrMnl _ _ _ _)); congr (\tr _).
  have sA_GP i a nz_i := subsetP (sA_G i nz_i) a.
  rewrite !(exchange_big_dep (mem G)) {sA_GP}//=; apply: eq_bigr => a Ga.
  by rewrite !sumrMnr !(big_andbC _ _ _ nz_k) -!/(sum_k _ A a _) partG.
move/sA_G=> {sA_G} sAiG; pose Ai1 := fG' @* A i; pose rR := 'r([~: W, Ai1]).
have sAiG1: Ai1 \subset G1 by rewrite -im_fG' morphimS.
have AfG' a: a \in A i -> fG' a \in Ai1.
  by move=> Aa; rewrite mem_morphim //= im_restrm imfG1 ?(subsetP sAiG).
have coWAi1: coprime #|W| #|Ai1|.
  by rewrite coprime_morphr ?(coprimegS sAiG) ?(pnat_coprime pW).
suffices [Pl [Pr [Pu [Pd [PlrudK ErC ErR]]]]]: 
  exists Pl, exists Pr, exists Pu, exists Pd,
    [/\ row_mx Pl Pr *m col_mx Pu Pd = 1%R,
        {in A i, forall a, Pd *m (rW (fG' a) *m Pr) = 1%:M :> 'M_(rC i)}
      & \sum_(a in A i) Pu *m (rW (fG' a) *m Pl) = 0 :> 'M_rR].
- rewrite -(mulmx1 (gamma i)) idmxE -PlrudK mulmxA mxtrace_mulC mul_mx_row.
  rewrite mul_col_row mxtrace_block !mulmx_suml !mulmx_sumr ErR mxtrace0 add0r.
  by rewrite (eq_bigr _ ErC) sumr_const raddfMn /= mxtrace1 natrM mulr_natr.
have defW: [~: W, Ai1] \x 'C_W(Ai1) = W.
  by rewrite coprime_abelian_cent_dprod ?(subset_trans sAiG1).
have [_ mulRCW _ tiRCW] := dprodP defW; have [sRW sCW] := mulG_sub mulRCW.
have [homoRW homoCW] := dprod_homocyclic defW pW homoW.
have [] := abelian_type_dprod_homocyclic defW pW homoW.
rewrite expW -/rR => atypeRW atypeCW.
have [[cRR _] [cCC _]] := (andP homoRW, andP homoCW).
have{cRR atypeRW} /isogP[hR injhR im_hR]: [~: W, Ai1] \isog [set: 'rV['Z_q]_rR].
  rewrite eq_abelian_type_isog ?zmod_abelian ?atypeRW //.
  by rewrite abelian_type_mx_group // mul1n eqxx.
have{tiRCW} rCW : 'r('C_W(Ai1)) = rC i.
  rewrite -['r(_)]rank_Ohm1; have /rank_abelem ->: p.-abelem 'Ohm_1('C_W(Ai1)).
    by rewrite Ohm1_abelem ?(pgroupS (subsetIl _ _)).
  congr (logn p _); transitivity #|'C_W(Ai1) : 'Mho^1('C_W(Ai1))|.
    by rewrite -divgS ?Mho_sub // -(mul_card_Ohm_Mho_abelian 1 cCC) mulnK.
  transitivity #|'C_W(Ai1) : 'Mho^1(W)|.
    symmetry; have /dprodP[_ /= defW1 _ _] := Mho_dprod 1 defW.
    rewrite -indexgI; congr #|_ : _|; rewrite /= -defW1 -group_modr ?Mho_sub //.
    by rewrite [_ :&: _](trivgP _) ?mul1g //= setIC -tiRCW setSI ?Mho_sub.
  suffices /card_isog ->: 'C_V(A i) \isog 'C_W(Ai1) / 'Mho^1(W).
    by rewrite card_quotient // subIset // normal_norm ?Mho_normal.
  rewrite coprime_quotient_cent ?Mho_sub ?abelian_sol //= -/Ai1; last first.
    by rewrite (subset_trans sAiG1) // (char_norm_trans _ nWG1) ?Mho_char.
  have ->: A i :=: fG @* Ai1.
    by rewrite /Ai1 morphim_invmE morphpreK // im_restrm imfG1.
  rewrite -imfW morphim_restrm (setIidPr sAiG1).
  have [f1 injf1 im_f1] := first_isom f.
  rewrite -!im_f1 -injm_subcent ?quotientS ?(subset_trans sAiG1) //.
  by rewrite -kerf isog_sym sub_isog // subIset ?quotientS.
have{atypeCW} /isogP[hC injhC im_hC]: 'C_W(Ai1) \isog [set: 'rV['Z_q]_(rC i)].
  rewrite eq_abelian_type_isog ?zmod_abelian // atypeCW rCW.
  by rewrite abelian_type_mx_group ?mul1n.
have mkMx m1 m2 (U : {group 'rV['Z_q]_m1}) (g : {morphism U >-> 'rV['Z_q]_m2}):
  setT \subset 'dom g -> {Mg | mulmx^~ Mg =1 g}.
- move/subsetP=> allU; suffices lin_g: linear g.
    by exists (lin1_mx (Linear lin_g)) => u; rewrite mul_rV_lin1.
  move=> z u v; rewrite morphM ?allU ?in_setT //.
  by rewrite -(natr_Zp z) !scaler_nat -zmodXgE morphX ?allU ?in_setT.
have /mkMx[Pu defPu]: setT \subset 'dom (invm injfW \o invm injhR).
  by rewrite -sub_morphim_pre -im_hR // im_invm //= im_fW.
have /mkMx[Pd defPd]: setT \subset 'dom (invm injfW \o invm injhC).
  by rewrite -sub_morphim_pre -im_hC //= im_fW im_invm subsetIl.
pose fUl := pairg1 [finGroupType of 'rV['Z_q]_(rC i)] \o hR.
pose fUr := @pair1g [finGroupType of 'rV['Z_q]_rR] _ \o hC.
have cRCW: fUr @* 'C_W(Ai1) \subset 'C(fUl @* [~: W, Ai1]).
  rewrite !morphim_comp morphim_pair1g morphim_pairg1.
  set UR := hR @* _; set UC := hC @* _.
  by have/dprodP[] : _ = setX UR UC := setX_dprod _ _.
have /domP[fUr' [DfUr' _ _ im_fUr']]: 'dom fUr = 'C_W(Ai1).
  by rewrite /dom -im_hC injmK.
have /domP[fUl' [DfUl' _ _ im_fUl']]: 'dom fUl = [~: W, Ai1].
  by rewrite /dom -im_hR injmK.
rewrite -{}im_fUr' -{}im_fUl' in cRCW; pose hW := dprodm defW cRCW.
pose fPl := @fst _ _ \o (hW \o fW); pose fPr := @snd _ _ \o (hW \o fW).
have /mkMx[/= Pl defPl]: setT \subset 'dom fPl.
  by rewrite -!sub_morphim_pre ?subsetT ?im_fW.
have /mkMx[/= Pr defPr]: setT \subset 'dom fPr.
  by rewrite -!sub_morphim_pre ?subsetT ?im_fW.
exists Pl, Pr, Pu, Pd; split.
- apply/row_matrixP=> j; rewrite rowE -row1 mul_row_col mulmxDr !mulmxA.
  apply: (injmP injfW); rewrite ?in_setT // morphM ?in_setT //.
  rewrite defPl defPr defPu defPd -/hW [hW]lock /= -lock.
  have /(mem_dprod defW)[jR [jC [RjR CjC -> _]]]:= WfW (row j 1).
  rewrite [hW _]dprodmE // DfUl' DfUr' /= mulg1 mul1g !invmE // -DfW'.
  by rewrite !fW'K ?(subsetP sRW jR) ?(subsetP sCW).
- move=> a Aa; apply/row_matrixP=> j; pose jC := invm injhC (row j 1%:M).
  rewrite rowE -row1 !mulmxA defPd defPr -/hW [hW]lock /= mul_rV_lin1 /= -lock.
  have CjC: jC \in 'C_W(Ai1).
    by rewrite -(im_invm injhC) mem_morphim /= ?im_hC ?inE.
  have [[/fW'K id_jC /centP cA1jC] A1a] := (setIP CjC, AfG' a Aa).
  rewrite -DfW' id_jC subgK ?(subsetP sAiG1) // /conjg cA1jC // mulKg id_jC.
  by rewrite [hW _]dprodmEr ?DfUr' //= invmK ?im_hC ?inE.
apply/row_matrixP=> j; pose jR := invm injhR (row j 1%:M).
have RjR: jR \in [~: W, Ai1].
  by rewrite -(im_invm injhR) mem_morphim /= ?im_hR ?inE.
rewrite rowE -row1 mulmx_sumr raddf0 -/jR.
have /subsetP nRA1: Ai1 \subset 'N([~: W, Ai1]) by rewrite commg_normr.
transitivity (\sum_(a1 in Ai1) hR (jR ^ a1)).
  rewrite {1}[Ai1 in rhs in _ = rhs]morphimEsub /= ?im_restrm ?imfG1 //.
  rewrite big_imset /=; last first.
    apply: sub_in2 (injmP (injm_invm injfG)); apply/subsetP.
    by rewrite /= im_restrm imfG1.
  apply: eq_bigr => a /AfG' A1a.
  have RjRa: jR ^ fG' a \in [~: W, Ai1] by rewrite memJ_norm ?nRA1.
  rewrite !mulmxA defPu defPl mul_rV_lin1 -/hW [hW]lock /= -lock.
  rewrite subgK ?(subsetP sAiG1) // -DfW' !fW'K ?(subsetP sRW) //.
  by rewrite [hW _]dprodmEl // DfUl'.
have [nf [fj Rfj ->]] := gen_prodgP RjR.
transitivity (\sum_(a1 in Ai1) (\prod_i1 hR (fj i1 ^ a1))%g).
  apply: eq_bigr => a1 Aa1; rewrite conjg_prod morph_prod // => i1 _.
  by rewrite memJ_norm ?mem_gen ?nRA1.
rewrite exchange_big big1 //= => i1 _; have /imset2P[w a1 Ww Aa1 ->] := Rfj i1.
apply: (addrI (\sum_(a2 in Ai1) hR [~ w, a2])).
rewrite addr0 {2}(reindex_inj (mulgI a1)) -big_split /=.
apply: eq_big => [a2 | a2 Aa2]; first by rewrite groupMl.
by rewrite commgMJ [rhs in _ = rhs]morphM ?memJ_norm ?nRA1 ?mem_commg ?groupM.
Qed.
