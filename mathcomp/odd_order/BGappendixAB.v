(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
Require Import fintype bigop prime finset ssralg fingroup morphism.
Require Import automorphism quotient gfunctor commutator zmodp center pgroup.
Require Import sylow gseries nilpotent abelian maximal.
Require Import matrix mxalgebra mxrepresentation mxabelem.
Require Import BGsection1 BGsection2.

(******************************************************************************)
(* This file contains the useful material in B & G, appendices A and B, i.e., *)
(* the proof of the p-stability properties and the ZL-Theorem (the Puig       *)
(* replacement for the Glaubermann ZJ-theorem). The relevant definitions are  *)
(* given in BGsection1.                                                       *)
(* Theorem A.4(a) has not been formalised: it is a result on external         *)
(* p-stability, which concerns faithful representations of group with a       *)
(* trivial p-core on a field of characteristic p. It's the historical concept *)
(* that was studied by Hall and Higman, but it's not used for FT. Note that   *)
(* the finite field case can be recovered from A.4(c) with a semi-direct      *)
(* product.                                                                   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Local Scope ring_scope.
Import GroupScope GRing.Theory.

Section AppendixA.

Implicit Type gT : finGroupType.
Implicit Type p : nat.

Import MatrixGenField.

(* This is B & G, Theorem A.4(c) (in Appendix A, not section 16!). We follow  *)
(* both B & G and Gorenstein in using the general form of the p-stable        *)
(* property. We could simplify the property because the conditions under      *)
(* which we prove p-stability are inherited by sections (morphic image in our *)
(* framework), and restrict to the case where P is normal in G. (Clearly the  *)
(* 'O_p^'(G) * P <| G premise plays no part in the proof.)                    *)
(* Theorems A.1-A.3 are essentially inlined in this proof.                    *)

Theorem odd_p_stable gT p (G : {group gT}) : odd #|G| -> p.-stable G.
Proof.
move: gT G.
pose p_xp gT (E : {group gT}) x := p.-elt x && (x \in 'C([~: E, [set x]])).
suffices IH gT (E : {group gT}) x y (G := <<[set x; y]>>) :
    [&& odd #|G|, p.-group E & G \subset 'N(E)] -> p_xp gT E x && p_xp gT E y ->
  p.-group (G / 'C(E)).
- move=> gT G oddG P A pP /andP[/mulGsubP[_ sPG] _] /andP[sANG pA] cRA.
  apply/subsetP=> _ /morphimP[x Nx Ax ->]; have NGx := subsetP sANG x Ax.
  apply: Baer_Suzuki => [|_ /morphimP[y Ny NGy ->]]; first exact: mem_quotient.
  rewrite -morphJ // -!morphim_set1 -?[<<_>>]morphimY ?sub1set ?groupJ //.
  set G1 := _ <*> _; rewrite /pgroup -(card_isog (second_isog _)); last first.
    by rewrite join_subG !sub1set Nx groupJ.
  have{Nx NGx Ny NGy} [[Gx Nx] [Gy Ny]] := (setIP NGx, setIP NGy).
  have sG1G: G1 \subset G by rewrite join_subG !sub1set groupJ ?andbT.
  have nPG1: G1 \subset 'N(P) by rewrite join_subG !sub1set groupJ ?andbT.
  rewrite -setIA setICA (setIidPr sG1G).
  rewrite (card_isog (second_isog _)) ?norms_cent //.
  apply: IH => //; first by rewrite pP nPG1 (oddSg sG1G).
  rewrite /p_xp -{2}(normP Ny) -conjg_set1 -conjsRg centJ memJ_conjg.
  rewrite p_eltJ andbb (mem_p_elt pA) // -sub1set centsC (sameP commG1P trivgP).
  by rewrite -cRA !commgSS ?sub1set.
move: {2}_.+1 (ltnSn #|E|) => n; elim: n => // n IHn in gT E x y G *.
rewrite ltnS => leEn /and3P[oddG pE nEG] /and3P[/andP[p_x cRx] p_y cRy].
have [Gx Gy]: x \in G /\ y \in G by apply/andP; rewrite -!sub1set -join_subG. 
apply: wlog_neg => p'Gc; apply/pgroupP=> q q_pr qGc; apply/idPn => p'q.
have [Q sylQ] := Sylow_exists q [group of G].
have [sQG qQ]: Q \subset G /\ q.-group Q by case/and3P: sylQ.
have{qQ p'q} p'Q: p^'.-group Q by apply: sub_in_pnat qQ => q' _ /eqnP->.
have{q q_pr sylQ qGc} ncEQ: ~~ (Q \subset 'C(E)).
  apply: contraL qGc => cEQ; rewrite -p'natE // -partn_eq1 //.
  have nCQ: Q \subset 'N('C(E)) by exact: subset_trans (normG _).
  have sylQc: q.-Sylow(G / 'C(E)) (Q / 'C(E)) by rewrite morphim_pSylow.
  by rewrite -(card_Hall sylQc) -trivg_card1 (sameP eqP trivgP) quotient_sub1.
have solE: solvable E := pgroup_sol pE.
have ntE: E :!=: 1 by apply: contra ncEQ; move/eqP->; rewrite cents1.
have{Q ncEQ p'Q sQG} minE_EG: minnormal E (E <*> G).
  apply/mingroupP; split=> [|D]; rewrite join_subG ?ntE ?normG //.
  case/and3P=> ntD nDE nDG sDE; have nDGi := subsetP nDG.
  apply/eqP; rewrite eqEcard sDE leqNgt; apply: contra ncEQ => ltDE.
  have nDQ: Q \subset 'N(D) by rewrite (subset_trans sQG).
  have cDQ: Q \subset 'C(D).
    rewrite -quotient_sub1 ?norms_cent // ?[_ / _]card1_trivg //.
    apply: pnat_1 (morphim_pgroup _ p'Q); apply: pgroupS (quotientS _ sQG) _.
    apply: IHn (leq_trans ltDE leEn) _ _; first by rewrite oddG (pgroupS sDE).
    rewrite /p_xp p_x p_y /=; apply/andP.
    by split; [move: cRx | move: cRy]; apply: subsetP; rewrite centS ?commSg.
  apply: (stable_factor_cent cDQ) solE; rewrite ?(pnat_coprime pE) //.
  apply/and3P; split; rewrite // -quotient_cents2 // centsC.
  rewrite -quotient_sub1 ?norms_cent ?quotient_norms ?(subset_trans sQG) //=.
  rewrite [(_ / _) / _]card1_trivg //=.
  apply: pnat_1 (morphim_pgroup _ (morphim_pgroup _ p'Q)).
  apply: pgroupS (quotientS _ (quotientS _ sQG)) _.
  have defGq: G / D = <<[set coset D x; coset D y]>>.
    by rewrite quotient_gen -1?gen_subG ?quotientU ?quotient_set1 ?nDGi.
  rewrite /= defGq IHn ?(leq_trans _ leEn) ?ltn_quotient // -?defGq.
    by rewrite quotient_odd // quotient_pgroup // quotient_norms.
  rewrite /p_xp -!sub1set !morph_p_elt -?quotient_set1 ?nDGi //=.
  by rewrite -!quotientR ?quotient_cents ?sub1set ?nDGi.
have abelE: p.-abelem E.
  by rewrite -is_abelem_pgroup //; case: (minnormal_solvable minE_EG _ solE).
have cEE: abelian E by case/and3P: abelE.
have{minE_EG} minE: minnormal E G.
  case/mingroupP: minE_EG => _ minE; apply/mingroupP; rewrite ntE.
  split=> // D ntD sDE; apply: minE => //; rewrite join_subG cents_norm //.
  by rewrite centsC (subset_trans sDE).
have nCG: G \subset 'N('C_G(E)) by rewrite normsI ?normG ?norms_cent.
suffices{p'Gc} pG'c: p.-group (G / 'C_G(E))^`(1).
  have [Pc sylPc sGc'Pc]:= Sylow_superset (der_subS _ _) pG'c.
  have nsPc: Pc <| G / 'C_G(E) by rewrite sub_der1_normal ?(pHall_sub sylPc).
  case/negP: p'Gc; rewrite /pgroup -(card_isog (second_isog _)) ?norms_cent //.
  rewrite setIC; apply: pgroupS (pHall_pgroup sylPc) => /=.
  rewrite sub_quotient_pre // join_subG !sub1set !(subsetP nCG, inE) //=.
  by rewrite !(mem_normal_Hall sylPc) ?mem_quotient ?morph_p_elt ?(subsetP nCG).
have defC := rker_abelem abelE ntE nEG; rewrite /= -/G in defC.
set rG := abelem_repr _ _ _ in defC.
case ncxy: (rG x *m rG y == rG y *m rG x).
  have Cxy: [~ x, y] \in 'C_G(E).
    rewrite -defC inE groupR //= !repr_mxM ?groupM ?groupV // mul1mx -/rG.
    by rewrite (eqP ncxy) -!repr_mxM ?groupM ?groupV // mulKg mulVg repr_mx1.
  rewrite [_^`(1)](commG1P _) ?pgroup1 //= quotient_gen -gen_subG //= -/G.
  rewrite !gen_subG centsC gen_subG quotient_cents2r ?gen_subG //= -/G. 
  rewrite /commg_set imset2Ul !imset2_set1l !imsetU !imset_set1.
  by rewrite !subUset andbC !sub1set !commgg group1 /= -invg_comm groupV Cxy.
pose Ax : 'M(E) := rG x - 1; pose Ay : 'M(E) := rG y - 1.
have Ax2: Ax *m Ax = 0.
  apply/row_matrixP=> i; apply/eqP; rewrite row_mul mulmxBr mulmx1.
  rewrite row0 subr_eq0 -(inj_eq (@rVabelem_inj _ _ _ abelE ntE)).
  rewrite rVabelemJ // conjgE -(centP cRx) ?mulKg //.
  rewrite linearB /= addrC row1 rowE rVabelemD rVabelemN rVabelemJ //=.
  by rewrite mem_commg ?set11 ?mem_rVabelem.
have Ay2: Ay *m Ay = 0.
  apply/row_matrixP=> i; apply/eqP; rewrite row_mul mulmxBr mulmx1.
  rewrite row0 subr_eq0 -(inj_eq (@rVabelem_inj _ _ _ abelE ntE)).
  rewrite rVabelemJ // conjgE -(centP cRy) ?mulKg //.
  rewrite linearB /= addrC row1 rowE rVabelemD rVabelemN rVabelemJ //=.
  by rewrite mem_commg ?set11 ?mem_rVabelem.
pose A := Ax *m Ay + Ay *m Ax.
have cAG: centgmx rG A.
  rewrite /centgmx gen_subG subUset !sub1set !inE Gx Gy /=; apply/andP.
  rewrite -[rG x](subrK 1%R) -[rG y](subrK 1%R) -/Ax -/Ay.
  rewrite 2!(mulmxDl _ 1 A) 2!(mulmxDr A _ 1) !mulmx1 !mul1mx.
  rewrite !(inj_eq (addIr A)) ![_ *m A]mulmxDr ![A *m _]mulmxDl.
  by rewrite -!mulmxA Ax2 Ay2 !mulmx0 !mulmxA Ax2 Ay2 !mul0mx !addr0 !add0r.
have irrG: mx_irreducible rG by exact/abelem_mx_irrP.
pose rAG := gen_repr irrG cAG; pose inFA := in_gen irrG cAG.
pose valFA := @val_gen _ _ _ _ _ _ irrG cAG.
set dA := gen_dim A in rAG inFA valFA.
rewrite -(rker_abelem abelE ntE nEG) -/rG -(rker_gen irrG cAG) -/rAG.
have dA_gt0: dA > 0 by rewrite (gen_dim_gt0 irrG cAG).
have irrAG: mx_irreducible rAG by exact: gen_mx_irr.
have: dA <= 2.
  case Ax0: (Ax == 0).
    by rewrite subr_eq0 in Ax0; case/eqP: ncxy; rewrite (eqP Ax0) mulmx1 mul1mx.
  case/rowV0Pn: Ax0 => v; case/submxP => u def_v nzv.
  pose U := col_mx v (v *m Ay); pose UA := <<inFA _ U>>%MS.
  pose rvalFA := @rowval_gen _ _ _ _ _ _ irrG cAG.
  have Umod: mxmodule rAG UA.
    rewrite /mxmodule gen_subG subUset !sub1set !inE Gx Gy /= andbC.
    apply/andP; split; rewrite (eqmxMr _ (genmxE _)) -in_genJ // genmxE.
      rewrite submx_in_gen // -[rG y](subrK 1%R) -/Ay mulmxDr mulmx1.
      rewrite addmx_sub // mul_col_mx -mulmxA Ay2 mulmx0.
      by rewrite -!addsmxE addsmx0 addsmxSr.
    rewrite -[rG x](subrK 1%R) -/Ax mulmxDr mulmx1 in_genD mul_col_mx.
    rewrite -mulmxA -[Ay *m Ax](addKr (Ax *m Ay)) (mulmxDr v _ A) -mulmxN.
    rewrite mulmxA {1 2}def_v -(mulmxA u) Ax2 mulmx0 mul0mx add0r.
    pose B := A; rewrite -(mul0mx _ B) -mul_col_mx -[B](mxval_groot irrG cAG).
    rewrite {B} -[_ 0 v](in_genK irrG cAG) -val_genZ val_genK.
    rewrite addmx_sub ?scalemx_sub ?submx_in_gen //.
    by rewrite -!addsmxE adds0mx addsmxSl.
  have nzU: UA != 0.
    rewrite -mxrank_eq0 genmxE mxrank_eq0; apply/eqP.
    move/(canRL ((in_genK _ _) _)); rewrite val_gen0; apply/eqP.
    by rewrite -submx0 -addsmxE addsmx_sub submx0 negb_and nzv.
  case/mx_irrP: irrAG => _ /(_ UA Umod nzU)/eqnP <-.
  by rewrite genmxE rank_leq_row.
rewrite leq_eqVlt ltnS leq_eqVlt ltnNge dA_gt0 orbF orbC; case/pred2P=> def_dA.
  rewrite [_^`(1)](commG1P _) ?pgroup1 // quotient_cents2r // gen_subG.
  apply/subsetP=> zt; case/imset2P=> z t Gz Gt ->{zt}.
  rewrite !inE groupR //= mul1mx; have Gtz := groupM Gt Gz.
  rewrite -(inj_eq (can_inj (mulKmx (repr_mx_unit rAG Gtz)))) mulmx1.
  rewrite [eq_op]lock -repr_mxM ?groupR ?groupM // -commgC !repr_mxM // -lock.
  apply/eqP; move: (rAG z) (rAG t); rewrite /= -/dA def_dA => Az At.
  by rewrite [Az]mx11_scalar scalar_mxC.
move: (kquo_repr _) (kquo_mx_faithful rAG) => /=; set K := rker _.
rewrite def_dA => r2G; move/der1_odd_GL2_charf; move/implyP.
rewrite quotient_odd //= -/G; apply: etrans; apply: eq_pgroup => p'.
have [p_pr _ _] := pgroup_pdiv pE ntE.
by rewrite (fmorph_char (gen_rmorphism _ _)) (charf_eq (char_Fp _)).
Qed.

Section A5.

Variables (gT : finGroupType) (p : nat) (G P X : {group gT}).

Hypotheses (oddG : odd #|G|) (solG : solvable G) (pP : p.-group P).
Hypotheses (nsPG : P <| G) (sXG : X \subset G).
Hypotheses (genX : generated_by (p_norm_abelian p P) X).

Let C := 'C_G(P).
Let defN : 'N_G(P) = G. Proof. by rewrite (setIidPl _) ?normal_norm. Qed.
Let nsCG : C <| G. Proof. by rewrite -defN subcent_normal. Qed.
Let nCG := normal_norm nsCG.
Let nCX := subset_trans sXG nCG.

(* This is B & G, Theorem A.5.1; it does not depend on the solG assumption. *)
Theorem odd_abelian_gen_stable : X / C \subset 'O_p(G / C).
Proof.
case/exists_eqP: genX => gX defX.
rewrite -defN sub_quotient_pre // -defX gen_subG.
apply/bigcupsP=> A gX_A; have [_ pA nAP cAA] := and4P gX_A.
have{gX_A} sAX: A \subset X by rewrite -defX sub_gen ?bigcup_sup.
rewrite -sub_quotient_pre ?(subset_trans sAX nCX) //=.
rewrite odd_p_stable ?normalM ?pcore_normal //.
  by rewrite /psubgroup pA defN (subset_trans sAX sXG).
by apply/commG1P; rewrite (subset_trans _ cAA) // commg_subr.
Qed.

(* This is B & G, Theorem A.5.2. *)
Theorem odd_abelian_gen_constrained :
  'O_p^'(G) = 1 -> 'C_('O_p(G))(P) \subset P -> X \subset 'O_p(G).
Proof.
set Q := 'O_p(G) => p'G1 sCQ_P. 
have sPQ: P \subset Q by rewrite pcore_max.
have defQ: 'O_{p^', p}(G) = Q by rewrite pseries_pop2.
have pQ: p.-group Q by exact: pcore_pgroup.
have sCQ: 'C_G(Q) \subset Q.
  by rewrite -{2}defQ solvable_p_constrained //= defQ /pHall pQ indexgg subxx.
have pC: p.-group C.
  apply/pgroupP=> q q_pr; case/Cauchy=> // u Cu q_u; apply/idPn=> p'q.
  suff cQu: u \in 'C_G(Q).
    case/negP: p'q; have{q_u}: q %| #[u] by rewrite q_u.
    by apply: pnatP q q_pr => //; apply: mem_p_elt pQ _; exact: (subsetP sCQ).
  have [Gu cPu] := setIP Cu; rewrite inE Gu /= -cycle_subG.
  rewrite coprime_nil_faithful_cent_stab ?(pgroup_nil pQ) //= -/C -/Q.
  - by rewrite cycle_subG; apply: subsetP Gu; rewrite normal_norm ?pcore_normal.
  - by rewrite (pnat_coprime pQ) // [#|_|]q_u pnatE.
  have sPcQu: P \subset 'C_Q(<[u]>) by rewrite subsetI sPQ centsC cycle_subG.
  by apply: subset_trans (subset_trans sCQ_P sPcQu); rewrite setIS // centS.
rewrite -(quotientSGK nCX) ?pcore_max // -pquotient_pcore //.
exact: odd_abelian_gen_stable.
Qed.

End A5.

End AppendixA.

Section AppendixB.

Local Notation "X --> Y" := (generated_by (norm_abelian X) Y)
  (at level 70, no associativity) : group_scope.

Variable gT : finGroupType.
Implicit Types G H A : {group gT}.
Implicit Types D E : {set gT}.
Implicit Type p : nat.

Lemma Puig_char G : 'L(G) \char G.
Proof. exact: gFchar. Qed.

Lemma center_Puig_char G : 'Z('L(G)) \char G.
Proof. exact: char_trans (center_char _) (Puig_char _). Qed.

(* This is B & G, Lemma B.1(a). *)
Lemma Puig_succS G D E : D \subset E -> 'L_[G](E) \subset 'L_[G](D).
Proof.
move=> sDE; apply: Puig_max (Puig_succ_sub _ _).
exact: norm_abgenS sDE (Puig_gen _ _).
Qed.

(* This is part of B & G, Lemma B.1(b) (see also BGsection1.Puig1). *)
Lemma Puig_sub_even m n G : m <= n -> 'L_{m.*2}(G) \subset 'L_{n.*2}(G).
Proof.
move/subnKC <-; move: {n}(n - m)%N => n.
by elim: m => [|m IHm] /=; rewrite ?sub1G ?Puig_succS.
Qed.

(* This is part of B & G, Lemma B.1(b). *)
Lemma Puig_sub_odd m n G : m <= n -> 'L_{n.*2.+1}(G) \subset 'L_{m.*2.+1}(G).
Proof. by move=> le_mn; rewrite Puig_succS ?Puig_sub_even. Qed.

(* This is part of B & G, Lemma B.1(b). *)
Lemma Puig_sub_even_odd m n G : 'L_{m.*2}(G) \subset 'L_{n.*2.+1}(G).
Proof.
elim: n m => [|n IHn] m; first by rewrite Puig1 Puig_at_sub.
by case: m => [|m]; rewrite ?sub1G ?Puig_succS ?IHn.
Qed.

(* This is B & G, Lemma B.1(c). *)
Lemma Puig_limit G :
  exists m, forall k, m <= k ->
    'L_{k.*2}(G) = 'L_*(G) /\ 'L_{k.*2.+1}(G) = 'L(G).
Proof.
pose L2G m := 'L_{m.*2}(G); pose n := #|G|.
have []: #|L2G n| <= n /\ n <= n by rewrite subset_leq_card ?Puig_at_sub.
elim: {1 2 3}n => [| m IHm leLm1 /ltnW]; first by rewrite leqNgt cardG_gt0.
have [eqLm le_mn|] := eqVneq (L2G m.+1) (L2G m); last first.
  rewrite eq_sym eqEcard Puig_sub_even ?leqnSn // -ltnNge => lt_m1_m.
  exact: IHm (leq_trans lt_m1_m leLm1).
have{eqLm} eqLm k: m <= k -> 'L_{k.*2}(G) = L2G m.
  rewrite leq_eqVlt => /predU1P[-> // |]; elim: k => // k IHk.
  by rewrite leq_eqVlt => /predU1P[<- //| ltmk]; rewrite -eqLm !PuigS IHk.
by exists m => k le_mk; rewrite Puig_def PuigS /Puig_inf /= !eqLm.
Qed.

(* This is B & G, Lemma B.1(d), second part; the first part is covered by     *)
(* BGsection1.Puig_inf_sub.                                                   *)
Lemma Puig_inf_sub_Puig G : 'L_*(G) \subset 'L(G).
Proof. exact: Puig_sub_even_odd. Qed.

(* This is B & G, Lemma B.1(e). *)
Lemma abelian_norm_Puig n G A :
  n > 0 -> abelian A -> A <| G -> A \subset 'L_{n}(G).
Proof.
case: n => // n _ cAA /andP[sAG nAG].
rewrite PuigS sub_gen // bigcup_sup // inE sAG /norm_abelian cAA andbT.
exact: subset_trans (Puig_at_sub n G) nAG.
Qed.

(* This is B & G, Lemma B.1(f), first inclusion. *)
Lemma sub_cent_Puig_at n p G :
  n > 0 -> p.-group G -> 'C_G('L_{n}(G)) \subset 'L_{n}(G).
Proof.
move=> n_gt0 pG.
have /ex_maxgroup[M /(max_SCN pG)SCN_M]: exists M, (gval M <| G) && abelian M.
  by exists 1%G; rewrite normal1 abelian1.
have{SCN_M} [cMM [nsMG defCM]] := (SCN_abelian SCN_M, SCN_P SCN_M).
have sML: M \subset 'L_{n}(G) by apply: abelian_norm_Puig.
by apply: subset_trans (sML); rewrite -defCM setIS // centS.
Qed.

(* This is B & G, Lemma B.1(f), second inclusion. *)
Lemma sub_center_cent_Puig_at n G : 'Z(G) \subset 'C_G('L_{n}(G)).
Proof. by rewrite setIS ?centS ?Puig_at_sub. Qed.

(* This is B & G, Lemma B.1(f), third inclusion (the fourth is trivial). *)
Lemma sub_cent_Puig_inf p G : p.-group G -> 'C_G('L_*(G)) \subset 'L_*(G).
Proof. by apply: sub_cent_Puig_at; rewrite double_gt0. Qed.

(* This is B & G, Lemma B.1(f), fifth inclusion (the sixth is trivial). *)
Lemma sub_cent_Puig p G : p.-group G -> 'C_G('L(G)) \subset 'L(G).
Proof. exact: sub_cent_Puig_at. Qed.

(* This is B & G, Lemma B.1(f), final remark (we prove the contrapositive). *)
Lemma trivg_center_Puig_pgroup p G : p.-group G -> 'Z('L(G)) = 1 -> G :=: 1.
Proof.
move=> pG LG1; apply/(trivg_center_pgroup pG)/trivgP.
rewrite -(trivg_center_pgroup (pgroupS (Puig_sub _) pG) LG1).
by apply: subset_trans (sub_cent_Puig pG); apply: sub_center_cent_Puig_at.
Qed.

(* This is B & G, Lemma B.1(g), second part; the first part is simply the     *)
(* definition of 'L(G) in terms of 'L_*(G).                                   *)
Lemma Puig_inf_def G : 'L_*(G) = 'L_[G]('L(G)).
Proof.
have [k defL] := Puig_limit G.
by case: (defL k) => // _ <-; case: (defL k.+1) => [|<- //]; apply: leqnSn.
Qed.

(* This is B & G, Lemma B.2. *)
Lemma sub_Puig_eq G H : H \subset G -> 'L(G) \subset H -> 'L(H) = 'L(G).
Proof.
move=> sHG sLG_H; apply/setP/subset_eqP/andP.
have sLH_G := subset_trans (Puig_succ_sub _ _) sHG.
have gPuig := norm_abgenS _ (Puig_gen _ _).
have [[kG defLG] [kH defLH]] := (Puig_limit G, Puig_limit H).
have [/defLG[_ {1}<-] /defLH[_ <-]] := (leq_maxl kG kH, leq_maxr kG kH).
split; do [elim: (maxn _ _) => [|k IHk /=]; first by rewrite !Puig1].
  rewrite doubleS !(PuigS _.+1) Puig_max ?gPuig // Puig_max ?gPuig //.
  exact: subset_trans (Puig_sub_even_odd _.+1 _ _) sLG_H.
rewrite doubleS Puig_max // -!PuigS Puig_def gPuig //.
by rewrite Puig_inf_def Puig_max ?gPuig ?sLH_G.
Qed.

Lemma norm_abgen_pgroup p X G :
  p.-group G -> X --> G -> generated_by (p_norm_abelian p X) G.
Proof.
move=> pG /exists_eqP[gG defG].
have:= subxx G; rewrite -{1 3}defG gen_subG /= => /bigcupsP-sGG.
apply/exists_eqP; exists gG; congr <<_>>; apply: eq_bigl => A.
by rewrite andbA andbAC andb_idr // => /sGG/pgroupS->.
Qed.

Variables (p : nat) (G S : {group gT}).
Hypotheses (oddG : odd #|G|) (solG : solvable G) (sylS : p.-Sylow(G) S).
Hypothesis p'G1 : 'O_p^'(G) = 1.

Let T := 'O_p(G).
Let nsTG : T <| G := pcore_normal _ _.
Let pT : p.-group T := pcore_pgroup _ _.
Let pS : p.-group S := pHall_pgroup sylS.
Let sSG := pHall_sub sylS.

(* This is B & G, Lemma B.3. *)
Lemma pcore_Sylow_Puig_sub : 'L_*(S) \subset 'L_*(T) /\ 'L(T) \subset 'L(S).
Proof.
have [[kS defLS] [kT defLT]] := (Puig_limit S, Puig_limit [group of T]).
have [/defLS[<- <-] /defLT[<- <-]] := (leq_maxl kS kT, leq_maxr kS kT).
have sL_ := subset_trans (Puig_succ_sub _ _).
elim: (maxn kS kT) => [|k [_ sL1]]; first by rewrite !Puig1 pcore_sub_Hall.
have{sL1} gL: 'L_{k.*2.+1}(T) --> 'L_{k.*2.+2}(S).
  exact: norm_abgenS sL1 (Puig_gen _ _).
have sCT_L: 'C_T('L_{k.*2.+1}(T)) \subset 'L_{k.*2.+1}(T).
  exact: sub_cent_Puig_at pT.
have{sCT_L} sLT: 'L_{k.*2.+2}(S) \subset T.
  apply: odd_abelian_gen_constrained sCT_L => //.
  - exact: pgroupS (Puig_at_sub _ _) pT.
  - by apply: char_normal_trans nsTG; apply: gFchar.
  - exact: sL_ sSG.
  by rewrite norm_abgen_pgroup // (pgroupS _ pS) ?Puig_at_sub.
have sL2: 'L_{k.*2.+2}(S) \subset 'L_{k.*2.+2}(T) by apply: Puig_max.
split; [exact: sL2 | rewrite doubleS; apply: subset_trans (Puig_succS _ sL2) _].
by rewrite Puig_max -?PuigS ?Puig_gen // sL_ // pcore_sub_Hall.
Qed.

Let Y := 'Z('L(T)).
Let L := 'L(S).

(* This is B & G, Theorem B.4(b). *)
Theorem Puig_center_normal : 'Z(L) <| G.
Proof.
have [sLiST sLTS] := pcore_Sylow_Puig_sub.
have sLiLT: 'L_*(T) \subset 'L(T) by exact: Puig_sub_even_odd.
have sZY: 'Z(L) \subset Y.
  rewrite subsetI andbC subIset ?centS ?orbT //=.
  suffices: 'C_S('L_*(S)) \subset 'L(T).
    by apply: subset_trans; rewrite setISS ?Puig_sub ?centS ?Puig_sub_even_odd.
  apply: subset_trans (subset_trans sLiST sLiLT).
  by apply: sub_cent_Puig_at pS; rewrite double_gt0.
have chY: Y \char G := char_trans (center_Puig_char _) (pcore_char _ _).
have nsCY_G: 'C_G(Y) <| G by rewrite char_normal 1?subcent_char ?char_refl.
have [C defC sCY_C nsCG] := inv_quotientN nsCY_G (pcore_normal p _).
have sLG: L \subset G by rewrite (subset_trans _ (pHall_sub sylS)) ?Puig_sub.
have nsL_nCS: L <| 'N_G(C :&: S).
  have sYLiS: Y \subset 'L_*(S).
    rewrite abelian_norm_Puig ?double_gt0 ?center_abelian //.
    apply: normalS (pHall_sub sylS) (char_normal chY).
    by rewrite subIset // (subset_trans sLTS) ?Puig_sub.
  have gYL: Y --> L := norm_abgenS sYLiS (Puig_gen _ _).
  have sLCS: L \subset C :&: S.
    rewrite subsetI Puig_sub andbT.
    rewrite -(quotientSGK _ sCY_C) ?(subset_trans sLG) ?normal_norm // -defC.
    rewrite odd_abelian_gen_stable ?char_normal ?norm_abgen_pgroup //.
      by rewrite (pgroupS _ pT) ?subIset // Puig_sub.
    by rewrite (pgroupS _ pS) ?Puig_sub.
  rewrite -[L](sub_Puig_eq _ sLCS) ?subsetIr //.
  by rewrite (char_normal_trans (Puig_char _)) ?normalSG // subIset // sSG orbT.
have sylCS: p.-Sylow(C) (C :&: S) := Sylow_setI_normal nsCG sylS.
have{defC} defC: 'C_G(Y) * (C :&: S) = C.
  apply/eqP; rewrite eqEsubset mulG_subG sCY_C subsetIl /=.
  have nCY_C: C \subset 'N('C_G(Y)).
    exact: subset_trans (normal_sub nsCG) (normal_norm nsCY_G). 
  rewrite -quotientSK // -defC /= -pseries1.
  rewrite -(pseries_catr_id [:: p : nat_pred]) (pseries_rcons_id [::]) /=.
  rewrite pseries1 /= pseries1 defC pcore_sub_Hall // morphim_pHall //.
  by rewrite subIset ?nCY_C.
have defG: 'C_G(Y) * 'N_G(C :&: S) = G.
  have sCS_N: C :&: S \subset 'N_G(C :&: S).
    by rewrite subsetI normG subIset // sSG orbT.
  by rewrite -(mulSGid sCS_N) mulgA defC (Frattini_arg _ sylCS).
have nsZ_N: 'Z(L) <| 'N_G(C :&: S) := char_normal_trans (center_char _) nsL_nCS.
rewrite /normal subIset ?sLG //= -{1}defG mulG_subG /=.
rewrite cents_norm ?normal_norm // centsC.
by rewrite (subset_trans sZY) // centsC subsetIr.
Qed.

End AppendixB.

Section Puig_factorization.

Variables (gT : finGroupType) (p : nat) (G S : {group gT}).
Hypotheses (oddG : odd #|G|) (solG : solvable G) (sylS : p.-Sylow(G) S).

(* This is B & G, Theorem B.4(a). *)
Theorem Puig_factorization : 'O_p^'(G) * 'N_G('Z('L(S))) = G.
Proof.
set D := 'O_p^'(G); set Z := 'Z(_); have [sSG pS _] := and3P sylS.
have sSN: S \subset 'N(D) by rewrite (subset_trans sSG) ?gFnorm.
have p'D: p^'.-group D := pcore_pgroup _ _.
have tiSD: S :&: D = 1 := coprime_TIg (pnat_coprime pS p'D).
have def_Zq: Z / D = 'Z('L(S / D)).
  rewrite !quotientE -(setIid S) -(morphim_restrm sSN); set f := restrm _ _.
  have injf: 'injm f by rewrite ker_restrm ker_coset tiSD.
  rewrite -!(injmF _ injf) ?Puig_sub //= morphim_restrm.
  by rewrite (setIidPr _) // subIset ?Puig_sub.
have{def_Zq} nZq: Z / D <| G / D.
  have sylSq: p.-Sylow(G / D) (S / D) by exact: morphim_pHall.
  rewrite def_Zq (Puig_center_normal _ _ sylSq) ?quotient_odd ?quotient_sol //.
  exact: trivg_pcore_quotient.
have sZS: Z \subset S by rewrite subIset ?Puig_sub.
have sZN: Z \subset 'N_G(Z) by rewrite subsetI normG (subset_trans sZS).
have nDZ: Z \subset 'N(D) by rewrite (subset_trans sZS).
rewrite -(mulSGid sZN) mulgA -(norm_joinEr nDZ) (@Frattini_arg p) //= -/D -/Z.
  rewrite -cosetpre_normal quotientK ?quotientGK ?pcore_normal // in nZq.
  by rewrite norm_joinEr.
rewrite /pHall -divgS joing_subr ?(pgroupS sZS) /= ?norm_joinEr //= -/Z.
by rewrite TI_cardMg ?mulnK //; apply/trivgP; rewrite /= setIC -tiSD setSI.
Qed.

End Puig_factorization.





