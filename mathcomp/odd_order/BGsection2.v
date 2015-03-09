(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div fintype.
Require Import bigop prime binomial finset fingroup morphism perm automorphism.
Require Import quotient action gfunctor commutator gproduct.
Require Import ssralg finalg zmodp cyclic center pgroup gseries nilpotent.
Require Import sylow abelian maximal hall.
Require poly ssrint.
Require Import matrix mxalgebra mxrepresentation mxabelem.
Require Import BGsection1.

(******************************************************************************)
(* This file covers the useful material in B & G, Section 2. This excludes    *)
(* part (c) of Proposition 2.1 and part (b) of Proposition 2.2, which are not *)
(* actually used in the rest of the proof; also the rest of Proposition 2.1   *)
(* is already covered by material in file mxrepresentation.v.                 *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section BGsection2.

Import GroupScope GRing.Theory FinRing.Theory poly.UnityRootTheory ssrint.IntDist.
Local Open Scope ring_scope.

Implicit Types (F : fieldType) (gT : finGroupType) (p : nat).

(* File mxrepresentation.v covers B & G, Proposition 2.1 as follows:          *)
(* - Proposition 2.1 (a) is covered by Lemmas mx_abs_irr_cent_scalar and      *)
(*     cent_mx_scalar_abs_irr.                                                *)
(* - Proposition 2.2 (b) is our definition of "absolutely irreducible", and   *)
(*   is thus covered by cent_mx_scalar_abs_irr and mx_abs_irrP.               *)
(* - Proposition 2.2 (c) is partly covered by the construction in submodule   *)
(*   MatrixGenField, which extends the base field with a single element a of  *)
(*   K = Hom_FG(M, M), rather than all of K, thus avoiding the use of the     *)
(*   Wedderburn theorem on finite division rings (by the primitive element    *)
(*   theorem this is actually equivalent). The corresponding representation   *)
(*   is built by MatrixGenField.gen_repr. In B & G, Proposition 2.1(c) is     *)
(*   only used in case II of the proof of Theorem 3.10, which we greatly      *)
(*   simplify by making use of the Wielandt fixpoint formula, following       *)
(*   Peterfalvi (Theorem 9.1). In this formalization the limited form of      *)
(*   2.1(c) is used to streamline the proof that groups of odd order are      *)
(*   p-stable (B & G, Appendix A.5(c)).                                       *)

(* This is B & G, Proposition 2.2(a), using internal isomorphims (mx_iso).    *)
Proposition mx_irr_prime_index F gT (G H : {group gT}) n M (nsHG : H <| G)
    (rG : mx_representation F G n) (rH := subg_repr rG (normal_sub nsHG)) :
    group_closure_field F gT -> mx_irreducible rG -> cyclic (G / H)%g ->
    mxsimple rH M -> {in G, forall x, mx_iso rH M (M *m rG x)} ->
  mx_irreducible rH.
Proof.
move=> closedF irrG /cyclicP[Hx defGH] simM isoM; have [sHG nHG] := andP nsHG.
have [modM nzM _] := simM; pose E_H := enveloping_algebra_mx rH.
have absM f: (M *m f <= M)%MS -> {a | (a \in E_H)%MS & M *m a = M *m f}.
  move=> sMf; set rM := submod_repr modM; set E_M := enveloping_algebra_mx rM.
  pose u := mxvec (in_submod M (val_submod 1%:M *m f)) *m pinvmx E_M.
  have EHu: (gring_mx rH u \in E_H)%MS := gring_mxP rH u.
  exists (gring_mx rH u) => //; rewrite -(in_submodK sMf).
  rewrite -(in_submodK (mxmodule_envelop modM EHu _)) //; congr (val_submod _).
  transitivity (in_submod M M *m gring_mx rM u).
    rewrite /gring_mx /= !mulmx_sum_row !linear_sum; apply: eq_bigr => i /= _.
    by rewrite !linearZ /= !rowK !mxvecK -in_submodJ.
  rewrite /gring_mx /= mulmxKpV ?submx_full ?mxvecK //; last first.
    suffices: mx_absolutely_irreducible rM by case/andP.
    by apply: closedF; exact/submod_mx_irr.
  rewrite {1}[in_submod]lock in_submodE -mulmxA mulmxA -val_submodE -lock.
  by rewrite mulmxA -in_submodE in_submodK.
have /morphimP[x nHx Gx defHx]: Hx \in (G / H)%g by rewrite defGH cycle_id.
have{Hx defGH defHx} defG : G :=: <[x]> <*> H.
  rewrite -(quotientGK nsHG) defGH defHx -quotient_cycle //.
  by rewrite joingC quotientK ?norm_joinEr // cycle_subG.
have [e def1]: exists e, 1%:M = \sum_(z in G) e z *m (M *m rG z).
  apply/sub_sumsmxP; have [X sXG [<- _]] := Clifford_basis irrG simM.
  by apply/sumsmx_subP=> z Xz; rewrite (sumsmx_sup z) ?(subsetP sXG).
have [phi inj_phi hom_phi defMx] := isoM x Gx.
have Mtau: (M *m (phi *m rG x^-1%g) <= M)%MS.
  by rewrite mulmxA (eqmxMr _ defMx) repr_mxK.
have Mtau': (M *m (rG x *m invmx phi) <= M)%MS.
  by rewrite mulmxA -(eqmxMr _ defMx) mulmxK.
have [[tau Htau defMtau] [tau' Htau' defMtau']] := (absM _ Mtau, absM _ Mtau').
have tau'K: tau' *m tau = 1%:M.
  rewrite -[tau']mul1mx def1 !mulmx_suml; apply: eq_bigr => z Gz.
  have [f _ hom_f] := isoM z Gz; move/eqmxP; case/andP=> _; case/submxP=> v ->.
  rewrite (mulmxA _ v) -2!mulmxA; congr (_ *m _).
  rewrite -(hom_envelop_mxC hom_f) ?envelop_mxM //; congr (_ *m _).
  rewrite mulmxA defMtau' -(mulmxKpV Mtau') -mulmxA defMtau (mulmxA _ M).
  by rewrite mulmxKpV // !mulmxA mulmxKV // repr_mxK.
have cHtau_x: centgmx rH (tau *m rG x).
  apply/centgmxP=> y Hy; have [u defMy] := submxP (mxmoduleP modM y Hy).
  have Gy := subsetP sHG y Hy.
  rewrite mulmxA; apply: (canRL (repr_mxKV rG Gx)).
  rewrite -!mulmxA /= -!repr_mxM ?groupM ?groupV // (conjgC y) mulKVg.
  rewrite -[rG y]mul1mx -{1}[tau]mul1mx def1 !mulmx_suml.
  apply: eq_bigr => z Gz; have [f _ hom_f] := isoM z Gz.
  move/eqmxP; case/andP=> _; case/submxP=> v ->; rewrite -!mulmxA.
  congr (_ *m (_ *m _)); rewrite {v} !(mulmxA M).
  rewrite -!(hom_envelop_mxC hom_f) ?envelop_mxM ?(envelop_mx_id rH) //.
    congr (_ *m f); rewrite !mulmxA defMy -(mulmxA u) defMtau (mulmxA u) -defMy.
    rewrite !mulmxA (hom_mxP hom_phi) // -!mulmxA; congr (M *m (_ *m _)).
    by rewrite /= -!repr_mxM ?groupM ?groupV // -conjgC.
  by rewrite -mem_conjg (normsP nHG).
have{cHtau_x} cGtau_x: centgmx rG (tau *m rG x).
  rewrite /centgmx {1}defG join_subG cycle_subG !inE Gx /= andbC.
  rewrite (subset_trans cHtau_x); last by rewrite rcent_subg subsetIr.
  apply/eqP; rewrite -{2 3}[rG x]mul1mx -tau'K !mulmxA; congr (_ *m _ *m _).
  case/envelop_mxP: Htau' => u ->.
  rewrite !(mulmx_suml, mulmx_sumr); apply: eq_bigr => y Hy.
  by rewrite -!(scalemxAl, scalemxAr) (centgmxP cHtau_x) ?mulmxA.
have{cGtau_x} [a def_tau_x]: exists a, tau *m rG x = a%:M.
  by apply/is_scalar_mxP; apply: mx_abs_irr_cent_scalar cGtau_x; exact: closedF.
apply: mx_iso_simple (eqmx_iso _ _) simM; apply/eqmxP; rewrite submx1 sub1mx.
case/mx_irrP: (irrG) => _ -> //; rewrite /mxmodule {1}defG join_subG /=.
rewrite cycle_subG inE Gx andbC (subset_trans modM) ?rstabs_subg ?subsetIr //=.
rewrite -{1}[M]mulmx1 -tau'K mulmxA -mulmxA def_tau_x mul_mx_scalar.
by rewrite scalemx_sub ?(mxmodule_envelop modM Htau').
Qed.

(* This is B & G, Lemma 2.3. Note that this is not used in the FT proof.      *)
Lemma rank_abs_irr_dvd_solvable F gT (G : {group gT}) n rG :
  @mx_absolutely_irreducible F _ G n rG -> solvable G -> n %| #|G|.
Proof.
move=> absG solG.
without loss closF: F rG absG / group_closure_field F gT.
  move=> IH; apply: (@group_closure_field_exists gT F) => [[F' f closF']].
  by apply: IH (map_repr f rG) _ closF'; rewrite map_mx_abs_irr.
elim: {G}_.+1 {-2}G (ltnSn #|G|) => // m IHm G leGm in n rG absG solG *.
have [G1 | ntG] := eqsVneq G 1%g. 
  by rewrite abelian_abs_irr ?G1 ?abelian1 // in absG; rewrite (eqP absG) dvd1n.
have [H nsHG p_pr] := sol_prime_factor_exists solG ntG.
set p := #|G : H| in p_pr.
pose sHG := normal_sub nsHG; pose rH := subg_repr rG sHG.
have irrG := mx_abs_irrW absG.
wlog [L simL _]: / exists2 L, mxsimple rH L & (L <= 1%:M)%MS.
  by apply: mxsimple_exists; rewrite ?mxmodule1 //; case: irrG.
have ltHG: H \proper G.
  by rewrite properEcard sHG -(Lagrange sHG) ltn_Pmulr // prime_gt1.
have dvLH: \rank L %| #|H|.
  have absL: mx_absolutely_irreducible (submod_repr (mxsimple_module simL)).
    by apply: closF; exact/submod_mx_irr.
  apply: IHm absL (solvableS (normal_sub nsHG) solG).
  by rewrite (leq_trans (proper_card ltHG)).
have [_ [x Gx H'x]] := properP ltHG.
have prGH: prime #|G / H|%g by rewrite card_quotient ?normal_norm.
wlog sH: / socleType rH by exact: socle_exists.
pose W := PackSocle (component_socle sH simL).
have card_sH: #|sH| = #|G : 'C_G[W | 'Cl]|.
  rewrite -cardsT; have ->: setT = orbit 'Cl G W.
    apply/eqP; rewrite eqEsubset subsetT.
    have /imsetP[W' _ defW'] := Clifford_atrans irrG sH.
    have WW': W' \in orbit 'Cl G W by rewrite orbit_in_sym // -defW' inE.
    by rewrite defW' andbT; apply/subsetP=> W''; exact: orbit_in_trans.
  rewrite orbit_stabilizer // card_in_imset //. 
  exact: can_in_inj (act_reprK _).
have sHcW: H \subset 'C_G[W | 'Cl].
  apply: subset_trans (subset_trans (joing_subl _ _) (Clifford_astab sH)) _.
  apply/subsetP=> z; rewrite !inE => /andP[->]; apply: subset_trans.
  exact: subsetT.
have [|] := prime_subgroupVti ('C_G[W | 'Cl] / H)%G prGH.
  rewrite quotientSGK ?normal_norm // => cClG.
  have def_sH: setT = [set W].
    apply/eqP; rewrite eq_sym eqEcard subsetT cards1 cardsT card_sH.
    by rewrite -indexgI (setIidPl cClG) indexgg.
  suffices L1: (L :=: 1%:M)%MS.
    by rewrite L1 mxrank1 in dvLH; exact: dvdn_trans (cardSg sHG).
  apply/eqmxP; rewrite submx1.
  have cycH: cyclic (G / H)%g by rewrite prime_cyclic.
  have [y Gy|_ _] := mx_irr_prime_index closF irrG cycH simL; last first.
    by apply; rewrite ?submx1 //; case simL.
  have simLy: mxsimple rH (L *m rG y) by exact: Clifford_simple.
  pose Wy := PackSocle (component_socle sH simLy).
  have: (L *m rG y <= Wy)%MS by rewrite PackSocleK component_mx_id.
  have ->: Wy = W by apply/set1P; rewrite -def_sH inE.
  by rewrite PackSocleK; exact: component_mx_iso.
rewrite (setIidPl _) ?quotientS ?subsetIl // => /trivgP.
rewrite quotient_sub1 //; last by rewrite subIset // normal_norm.
move/setIidPl; rewrite (setIidPr sHcW) /= => defH.
rewrite -(Lagrange sHG) -(Clifford_rank_components irrG W) card_sH -defH.
rewrite mulnC dvdn_pmul2r // (_ : W :=: L)%MS //; apply/eqmxP.
have sLW: (L <= W)%MS by rewrite PackSocleK component_mx_id.
rewrite andbC sLW; have [modL nzL _] := simL.
have [_ _] := (Clifford_rstabs_simple irrG W); apply=> //.
rewrite /mxmodule rstabs_subg /= -Clifford_astab1 -astabIdom -defH.
by rewrite -(rstabs_subg rG sHG).
Qed.

(* This section covers the many parts B & G, Proposition 2.4; only the last   *)
(* part (k) in used in the rest of the proof, and then only for Theorem 2.5.  *)
Section QuasiRegularCyclic.

Variables (F : fieldType) (q' h : nat).

Local Notation q := q'.+1.
Local Notation V := 'rV[F]_q.
Local Notation E := 'M[F]_q.

Variables (g : E) (eps : F).

Hypothesis gh1 : g ^+ h = 1.
Hypothesis prim_eps : h.-primitive_root eps.

Let h_gt0 := prim_order_gt0 prim_eps.
Let eps_h := prim_expr_order prim_eps.
Let eps_mod_h m := expr_mod m eps_h.
Let inj_eps : injective (fun i : 'I_h => eps ^+ i).
Proof.
move=> i j eq_ij; apply/eqP; move/eqP: eq_ij.
by rewrite (eq_prim_root_expr prim_eps) !modn_small.
Qed.

Let inhP m : m %% h < h. Proof. by rewrite ltn_mod. Qed.
Let inh m := Ordinal (inhP m).

Let V_ i := eigenspace g (eps ^+ i).
Let n_ i := \rank (V_ i).
Let E_ i := eigenspace (lin_mx (mulmx g^-1 \o mulmxr g)) (eps ^+ i).
Let E2_ i t :=
  (kermx (lin_mx (mulmxr (cokermx (V_ t)) \o mulmx (V_ i)))
   :&: kermx (lin_mx (mulmx (\sum_(j < h | j != i %[mod h]) V_ j)%MS)))%MS.

Local Notation "''V_' i" := (V_ i) (at level 8, i at level 2, format "''V_' i").
Local Notation "''n_' i" := (n_ i) (at level 8, i at level 2, format "''n_' i").
Local Notation "''E_' i" := (E_ i) (at level 8, i at level 2, format "''E_' i").
Local Notation "'E_ ( i )" := (E_ i) (at level 8, only parsing).
Local Notation "e ^g" := (g^-1 *m (e *m g))
  (at level 8, format "e ^g") : ring_scope.
Local Notation "'E_ ( i , t )" := (E2_ i t)
  (at level 8, format "''E_' ( i ,  t )").

Let inj_g : g \in GRing.unit.
Proof. by rewrite -(unitrX_pos _ h_gt0) gh1 unitr1. Qed.

Let Vi_mod i : 'V_(i %% h) = 'V_i.
Proof. by rewrite /V_ eps_mod_h. Qed.

Let g_mod i := expr_mod i gh1.

Let EiP i e : reflect (e^g = eps ^+ i *: e) (e \in 'E_i)%MS.
Proof.
rewrite (sameP eigenspaceP eqP) mul_vec_lin -linearZ /=.
by rewrite (can_eq mxvecK); exact: eqP.
Qed.

Let E2iP i t e :
  reflect ('V_i *m e <= 'V_t /\ forall j, j != i %[mod h] -> 'V_j *m e = 0)%MS
          (e \in 'E_(i, t))%MS.
Proof.
rewrite sub_capmx submxE !(sameP sub_kermxP eqP) /=.
rewrite !mul_vec_lin !mxvec_eq0 /= -submxE -submx0 sumsmxMr.
apply: (iffP andP) => [[->] | [-> Ve0]]; last first.
  by split=> //; apply/sumsmx_subP=> j ne_ji; rewrite Ve0.
move/sumsmx_subP=> Ve0; split=> // j ne_ji; apply/eqP.
by rewrite -submx0 -Vi_mod (Ve0 (inh j)) //= modn_mod.
Qed.

Let sumV := (\sum_(i < h) 'V_i)%MS.

(* This is B & G, Proposition 2.4(a). *)
Proposition mxdirect_sum_eigenspace_cycle : (sumV :=: 1%:M)%MS /\ mxdirect sumV.
Proof.
have splitF: group_splitting_field F (Zp_group h).
  move: prim_eps (abelianS (subsetT (Zp h)) (Zp_abelian _)).
  by rewrite -{1}(card_Zp h_gt0); exact: primitive_root_splitting_abelian.
have F'Zh: [char F]^'.-group (Zp h).
  apply/pgroupP=> p p_pr; rewrite card_Zp // => /dvdnP[d def_h].
  apply/negP=> /= charFp.
  have d_gt0: d > 0 by move: h_gt0; rewrite def_h; case d.
  have: eps ^+ d == 1.
    rewrite -(inj_eq (fmorph_inj [rmorphism of Frobenius_aut charFp])).
    by rewrite rmorph1 /= Frobenius_autE -exprM -def_h eps_h.
  by rewrite -(prim_order_dvd prim_eps) gtnNdvd // def_h ltn_Pmulr // prime_gt1.
case: (ltngtP h 1) => [|h_gt1|h1]; last first; last by rewrite ltnNge h_gt0.
  rewrite /sumV mxdirectE /= h1 !big_ord1; split=> //.
  apply/eqmxP; rewrite submx1; apply/eigenspaceP.
  by rewrite mul1mx scale1r idmxE -gh1 h1.
pose mxZ (i : 'Z_h) := g ^+ i.
have mxZ_repr: mx_repr (Zp h) mxZ.
  by split=> // i j _ _; rewrite /mxZ /= {3}Zp_cast // expr_mod // exprD.
pose rZ := MxRepresentation mxZ_repr.
have ZhT: Zp h = setT by rewrite /Zp h_gt1.
have memZh: _ \in Zp h by move=> i; rewrite ZhT inE.
have def_g: g = rZ Zp1 by [].
have lin_rZ m (U : 'M_(m, q)) a:
  U *m g = a *: U -> forall i, U *m rZ i%:R = (a ^+ i) *: U.
- move=> defUg i; rewrite repr_mxX //.
  elim: i => [|i IHi]; first by rewrite mulmx1 scale1r.
  by rewrite !exprS -scalerA mulmxA defUg -IHi scalemxAl.
rewrite mxdirect_sum_eigenspace => [|j k _ _]; last exact: inj_eps.
split=> //; apply/eqmxP; rewrite submx1.
wlog [I M /= simM <- _]: / mxsemisimple rZ 1.
  exact: mx_reducible_semisimple (mxmodule1 _) (mx_Maschke rZ F'Zh) _.
apply/sumsmx_subP=> i _; have simMi := simM i; have [modMi _ _] := simMi.
set v := nz_row (M i); have nz_v: v != 0 by exact: nz_row_mxsimple simMi.
have rankMi: \rank (M i) = 1%N.
  by rewrite (mxsimple_abelian_linear splitF _ simMi) //= ZhT Zp_abelian.
have defMi: (M i :=: v)%MS.
  apply/eqmxP; rewrite andbC -(geq_leqif (mxrank_leqif_eq _)) ?nz_row_sub //.
  by rewrite rankMi lt0n mxrank_eq0.
have [a defvg]: exists a, v *m rZ 1%R = a *: v.
  by apply/sub_rVP; rewrite -defMi mxmodule_trans ?socle_module ?defMi.
have: a ^+ h - 1 == 0.
  apply: contraR nz_v => nz_pZa; rewrite -(eqmx_eq0 (eqmx_scale _ nz_pZa)).
  by rewrite scalerBl scale1r -lin_rZ // subr_eq0 char_Zp ?mulmx1.
rewrite subr_eq0; move/eqP; case/(prim_rootP prim_eps) => k def_a.
by rewrite defMi (sumsmx_sup k) // /V_ -def_a; exact/eigenspaceP.
Qed.

(* This is B & G, Proposition 2.4(b). *)
Proposition rank_step_eigenspace_cycle i : 'n_ (i + h) = 'n_ i.
Proof. by rewrite /n_ -Vi_mod modnDr Vi_mod. Qed.

Let sumE := (\sum_(it : 'I_h * 'I_h) 'E_(it.1, it.2))%MS.

(* This is B & G, Proposition 2.4(c). *)
Proposition mxdirect_sum_proj_eigenspace_cycle :
  (sumE :=: 1%:M)%MS /\ mxdirect sumE.
Proof.
have [def1V] := mxdirect_sum_eigenspace_cycle; move/mxdirect_sumsP=> dxV.
pose p (i : 'I_h) := proj_mx 'V_i (\sum_(j | j != i) 'V_j)%MS.
have def1p: 1%:M = \sum_i p i.
  rewrite -[\sum_i _]mul1mx; move/eqmxP: def1V; rewrite submx1.
  case/sub_sumsmxP=> u ->; rewrite mulmx_sumr; apply: eq_bigr => i _.
  rewrite (bigD1 i) //= mulmxDl proj_mx_id ?submxMl ?dxV //.
  rewrite proj_mx_0 ?dxV ?addr0 ?summx_sub // => j ne_ji.
  by rewrite (sumsmx_sup j) ?submxMl.
split; first do [apply/eqmxP; rewrite submx1].
  apply/(@memmx_subP F _ _ q)=> A _; apply/memmx_sumsP.
  pose B i t := p i *m A *m p t.
  exists (fun it => B it.1 it.2) => [|[i t] /=].
    rewrite -(pair_bigA _ B) /= -[A]mul1mx def1p mulmx_suml.
    by apply: eq_bigr => i _; rewrite -mulmx_sumr -def1p mulmx1.
  apply/E2iP; split=> [|j ne_ji]; first by rewrite mulmxA proj_mx_sub.
  rewrite 2!mulmxA -mulmxA proj_mx_0 ?dxV ?mul0mx //.
  rewrite (sumsmx_sup (inh j)) ?Vi_mod //.
  by rewrite (modn_small (valP i)) in ne_ji.
apply/mxdirect_sumsP=> [[i t] _] /=.
apply/eqP; rewrite -submx0; apply/(@memmx_subP F _ _ q)=> A.
rewrite sub_capmx submx0 mxvec_eq0 -submx0.
case/andP=> /E2iP[ViA Vi'A] /memmx_sumsP[B /= defA sBE].
rewrite -[A]mul1mx -(eqmxMr A def1V) sumsmxMr (bigD1 i) //=.
rewrite big1 ?addsmx0 => [|j ne_ij]; last by rewrite Vi'A ?modn_small.
rewrite -[_ *m A]mulmx1 def1p mulmx_sumr (bigD1 t) //=.
rewrite big1 ?addr0 => [|u ne_ut]; last first.
  by rewrite proj_mx_0 ?dxV ?(sumsmx_sup t) // eq_sym.
rewrite {A ViA Vi'A}defA mulmx_sumr mulmx_suml summx_sub // => [[j u]].
case/E2iP: (sBE (j, u)); rewrite eqE /=; case: eqP => [-> sBu _ ne_ut|].
  by rewrite proj_mx_0 ?dxV ?(sumsmx_sup u).
by move/eqP=> ne_ji _ ->; rewrite ?mul0mx // eq_sym !modn_small.
Qed.

(* This is B & G, Proposition 2.4(d). *)
Proposition rank_proj_eigenspace_cycle i t : \rank 'E_(i, t) = ('n_i * 'n_t)%N.
Proof.
have [def1V] := mxdirect_sum_eigenspace_cycle; move/mxdirect_sumsP=> dxV.
pose p (i : 'I_h) := proj_mx 'V_i (\sum_(j | j != i) 'V_j)%MS.
have def1p: 1%:M = \sum_i p i.
  rewrite -[\sum_i _]mul1mx; move/eqmxP: def1V; rewrite submx1.
  case/sub_sumsmxP=> u ->; rewrite mulmx_sumr; apply: eq_bigr => j _.
  rewrite (bigD1 j) //= mulmxDl proj_mx_id ?submxMl ?dxV //.
  rewrite proj_mx_0 ?dxV ?addr0 ?summx_sub // => k ne_kj.
  by rewrite (sumsmx_sup k) ?submxMl.
move: i t => i0 t0; pose i := inh i0; pose t := inh t0.
transitivity (\rank 'E_(i, t)); first by rewrite /E2_ !Vi_mod modn_mod.
transitivity ('n_i * 'n_t)%N; last by rewrite /n_ !Vi_mod.
move: {i0 t0}i t => i t; pose Bi := row_base 'V_i; pose Bt := row_base 'V_t.
pose B := lin_mx (mulmx (p i *m pinvmx Bi) \o mulmxr Bt).
pose B' := lin_mx (mulmx Bi \o mulmxr (pinvmx Bt)).
have Bk : B *m B' = 1%:M.
  have frVpK m (C : 'M[F]_(m, q)) : row_free C -> C *m pinvmx C = 1%:M.
    by move/row_free_inj; apply; rewrite mul1mx mulmxKpV.
  apply/row_matrixP=> k; rewrite row_mul mul_rV_lin /= rowE mx_rV_lin /= -row1.
  rewrite (mulmxA _ _ Bt) -(mulmxA _ Bt) [Bt *m _]frVpK ?row_base_free //.
  rewrite mulmx1 2!mulmxA proj_mx_id ?dxV ?eq_row_base //.
  by rewrite frVpK ?row_base_free // mul1mx vec_mxK.
have <-: \rank B = ('n_i * 'n_t)%N by apply/eqP; apply/row_freeP; exists B'.
apply/eqP; rewrite eqn_leq !mxrankS //.
  apply/row_subP=> k; rewrite rowE mul_rV_lin /=.
  apply/E2iP; split=> [|j ne_ji].
    rewrite 3!mulmxA mulmx_sub ?eq_row_base //.
  rewrite 2!(mulmxA 'V_j) proj_mx_0 ?dxV ?mul0mx //.
  rewrite (sumsmx_sup (inh j)) ?Vi_mod //.
  by rewrite (modn_small (valP i)) in ne_ji.
apply/(@memmx_subP F _ _ q) => A /E2iP[ViA Vi'A].
apply/submxP; exists (mxvec (Bi *m A *m pinvmx Bt)); rewrite mul_vec_lin /=.
rewrite mulmxKpV; last by rewrite eq_row_base (eqmxMr _ (eq_row_base _)).
rewrite mulmxA -[p i]mul1mx mulmxKpV ?eq_row_base ?proj_mx_sub // mul1mx.
rewrite -{1}[A]mul1mx def1p mulmx_suml (bigD1 i) //= big1 ?addr0 // => j neji.
rewrite -[p j]mul1mx -(mulmxKpV (proj_mx_sub _ _ _)) -mulmxA Vi'A ?mulmx0 //.
by rewrite !modn_small.
Qed.

(* This is B & G, Proposition 2.4(e). *)
Proposition proj_eigenspace_cycle_sub_quasi_cent i j :
  ('E_(i, i + j) <= 'E_j)%MS.
Proof.
apply/(@memmx_subP F _ _ q)=> A /E2iP[ViA Vi'A].
apply/EiP; apply: canLR (mulKmx inj_g) _; rewrite -{1}[A]mul1mx -{2}[g]mul1mx.
have: (1%:M <= sumV)%MS by have [->] := mxdirect_sum_eigenspace_cycle.
case/sub_sumsmxP=> p ->; rewrite -!mulmxA !mulmx_suml.
apply: eq_bigr=> k _; have [-> | ne_ki] := eqVneq (k : nat) (i %% h)%N.
  rewrite Vi_mod -mulmxA (mulmxA _ A) (eigenspaceP ViA).
  rewrite (mulmxA _ g) (eigenspaceP (submxMl _ _)).
  by rewrite -!(scalemxAl, scalemxAr) scalerA mulmxA exprD.
rewrite 2!mulmxA (eigenspaceP (submxMl _ _)) -!(scalemxAr, scalemxAl).
by rewrite -(mulmxA _ 'V_k A) Vi'A ?linear0 ?mul0mx ?scaler0 // modn_small.
Qed.

Let diagE m :=
  (\sum_(it : 'I_h * 'I_h | it.1 + m == it.2 %[mod h]) 'E_(it.1, it.2))%MS.

(* This is B & G, Proposition 2.4(f). *)
Proposition diag_sum_proj_eigenspace_cycle m :
  (diagE m :=: 'E_m)%MS /\ mxdirect (diagE m).
Proof.
have sub_diagE n: (diagE n <= 'E_n)%MS.
  apply/sumsmx_subP=> [[i t] /= def_t].
  apply: submx_trans (proj_eigenspace_cycle_sub_quasi_cent i n).
  by rewrite /E2_ -(Vi_mod (i + n)) (eqP def_t) Vi_mod.
pose sum_diagE := (\sum_(n < h) diagE n)%MS.
pose p (it : 'I_h * 'I_h) := inh (h - it.1 + it.2).
have def_diag: sum_diagE = sumE.
  rewrite /sumE (partition_big p xpredT) //.
  apply: eq_bigr => n _; apply: eq_bigl => [[i t]] /=.
  rewrite /p -val_eqE /= -(eqn_modDl (h - i)).
  by rewrite addnA subnK 1?ltnW // modnDl modn_small.
have [Efull dxE] := mxdirect_sum_proj_eigenspace_cycle.
have /mxdirect_sumsE[/= dx_diag rank_diag]: mxdirect sum_diagE.
  apply/mxdirectP; rewrite /= -/sum_diagE def_diag (mxdirectP dxE) /=.
  rewrite (partition_big p xpredT) //.
  apply: eq_bigr => n _; apply: eq_bigl => [[i t]] /=.
  symmetry; rewrite /p -val_eqE /= -(eqn_modDl (h - i)).
  by rewrite addnA subnK 1?ltnW // modnDl modn_small.
have dx_sumE1: mxdirect (\sum_(i < h) 'E_i).
  by apply: mxdirect_sum_eigenspace => i j _ _; exact: inj_eps.
have diag_mod n: diagE (n %% h) = diagE n.
  by apply: eq_bigl=> it; rewrite modnDmr.
split; last first.
  apply/mxdirectP; rewrite /= -/(diagE m) -diag_mod.
  rewrite (mxdirectP (dx_diag (inh m) _)) //=.
  by apply: eq_bigl=> it; rewrite modnDmr.
apply/eqmxP; rewrite sub_diagE /=.
rewrite -(capmx_idPl (_ : _ <= sumE))%MS ?Efull ?submx1 //.
rewrite -def_diag /sum_diagE (bigD1 (inh m)) //= addsmxC.
rewrite diag_mod -matrix_modr ?sub_diagE //.
rewrite ((_ :&: _ =P 0)%MS _) ?adds0mx // -submx0.
rewrite -{2}(mxdirect_sumsP dx_sumE1 (inh m)) ?capmxS //.
  by rewrite /E_ eps_mod_h.
by apply/sumsmx_subP=> i ne_i_m; rewrite (sumsmx_sup i) ?sub_diagE.
Qed.

(* This is B & G, Proposition 2.4(g). *)
Proposition rank_quasi_cent_cycle m :
  \rank 'E_m = (\sum_(i < h) 'n_i * 'n_(i + m))%N.
Proof.
have [<- dx_diag] := diag_sum_proj_eigenspace_cycle m.
rewrite (mxdirectP dx_diag) /= (reindex (fun i : 'I_h => (i, inh (i + m)))) /=.
  apply: eq_big => [i | i _]; first by rewrite modn_mod eqxx.
  by rewrite rank_proj_eigenspace_cycle /n_ Vi_mod.
exists (@fst _ _) => // [] [i t] /=.
by rewrite !inE /= (modn_small (valP t)) => def_t; exact/eqP/andP.
Qed.

(* This is B & G, Proposition 2.4(h). *)
Proposition diff_rank_quasi_cent_cycle m :
  (2 * \rank 'E_0 = 2 * \rank 'E_m + \sum_(i < h) `|'n_i - 'n_(i + m)| ^ 2)%N.
Proof.
rewrite !rank_quasi_cent_cycle !{1}mul2n -addnn.
rewrite {1}(reindex (fun i : 'I_h => inh (i + m))) /=; last first.
  exists (fun i : 'I_h => inh (i + (h - m %% h))%N) => i _.
    apply: val_inj; rewrite /= modnDml -addnA addnCA -modnDml addnCA.
    by rewrite subnKC 1?ltnW ?ltn_mod // modnDr modn_small.
  apply: val_inj; rewrite /= modnDml -modnDmr -addnA.
  by rewrite subnK 1?ltnW ?ltn_mod // modnDr modn_small.
rewrite -mul2n big_distrr -!big_split /=; apply: eq_bigr => i _.
by rewrite !addn0 (addnC (2 * _)%N) sqrn_dist addnC /n_ Vi_mod.
Qed.

Hypothesis rankEm : forall m, m != 0 %[mod h] -> \rank 'E_0 = (\rank 'E_m).+1.

(* This is B & G, Proposition 2.4(j). *)
Proposition rank_eigenspaces_quasi_homocyclic :
  exists2 n, `|q - h * n| = 1%N &
  exists i : 'I_h, [/\ `|'n_i - n| = 1%N, (q < h * n) = ('n_i < n)
                     & forall j, j != i -> 'n_j = n].
Proof.
have [defV dxV] := mxdirect_sum_eigenspace_cycle.
have sum_n: (\sum_(i < h) 'n_i)%N = q by rewrite -(mxdirectP dxV) defV mxrank1.
suffices [n [i]]: exists n : nat, exists2 i : 'I_h, 
  `|'n_i - n| == 1%N & forall i', i' != i -> 'n_i' = n.
- move/eqP=> n_i n_i'; rewrite -{1 5}(prednK h_gt0).
  rewrite -sum_n (bigD1 i) //= (eq_bigr _ n_i') sum_nat_const cardC1 card_ord.
  by exists n; last exists i; rewrite ?distnDr ?ltn_add2r.
case: (leqP h 1) sum_n {defV dxV} => [|h_gt1 _].
  rewrite leq_eqVlt ltnNge h_gt0 orbF; move/eqP->; rewrite big_ord1 => n_0.
  by exists q', 0 => [|i']; rewrite ?(ord1 i') // n_0 distSn.
pose dn1 i := `|'n_i - 'n_(i + 1)|.
have sum_dn1: (\sum_(0 <= i < h) dn1 i ^ 2 == 2)%N.
  rewrite big_mkord -(eqn_add2l (2 * \rank 'E_1)) -diff_rank_quasi_cent_cycle.
  by rewrite -mulnSr -rankEm ?modn_small.
pose diff_n := [seq i <- index_iota 0 h | dn1 i != 0%N].
have diff_n_1: all (fun i => dn1 i == 1%N) diff_n.
  apply: contraLR sum_dn1; case/allPn=> i; rewrite mem_filter.
  case def_i: (dn1 i) => [|[|ni]] //=; case/splitPr=> e e' _.
  by rewrite big_cat big_cons /= addnCA def_i -add2n sqrnD.
have: sorted ltn diff_n.
  by rewrite (sorted_filter ltn_trans) // /index_iota subn0 iota_ltn_sorted.
have: all (ltn^~ h) diff_n.
  by apply/allP=> i; rewrite mem_filter mem_index_iota; case/andP.
have: size diff_n = 2%N.
  move: diff_n_1; rewrite size_filter -(eqnP sum_dn1) /diff_n.
  elim: (index_iota 0 h) => [|i e IHe]; rewrite (big_nil, big_cons) //=.
  by case def_i: (dn1 i) => [|[]] //=; rewrite def_i //; move/IHe->.
case def_jk: diff_n diff_n_1 => [|j [|k []]] //=; case/and3P=> dn1j dn1k _ _.
case/and3P=> lt_jh lt_kh _ /andP[lt_jk _].
have def_n i:
  i <= h -> 'n_i = if i <= j then 'n_0 else if i <= k then 'n_j.+1 else 'n_k.+1.
- elim: i => // i IHi lt_ik; have:= IHi (ltnW lt_ik); rewrite !(leq_eqVlt i).
  have:= erefl (i \in diff_n); rewrite {2}def_jk !inE mem_filter mem_index_iota.
  case: (i =P j) => [-> _ _ | _]; first by rewrite ltnn lt_jk.
  case: (i =P k) => [-> _ _ | _]; first by rewrite ltnNge ltnW // ltnn.
  by rewrite distn_eq0 lt_ik addn1; case: eqP => [->|].
have n_j1: 'n_j.+1 = 'n_k by rewrite (def_n k (ltnW lt_kh)) leqnn leqNgt lt_jk.
have n_k1: 'n_k.+1 = 'n_0.
  rewrite -(rank_step_eigenspace_cycle 0) (def_n h (leqnn h)).
  by rewrite leqNgt lt_jh leqNgt lt_kh; split.
case: (leqP k j.+1) => [ | lt_j1_k].
  rewrite leq_eqVlt ltnNge lt_jk orbF; move/eqP=> def_k.
  exists 'n_(k + 1); exists (Ordinal lt_kh) => [|i' ne_i'k]; first exact: dn1k.
  rewrite addn1 {1}(def_n _ (ltnW (valP i'))) n_k1.
  by rewrite -ltnS -def_k ltn_neqAle ne_i'k /=; case: leqP; split.
case: (leqP h.-1 (k - j)) => [le_h1_kj | lt_kj_h1].
  have k_h1: k = h.-1.
    apply/eqP; rewrite eqn_leq -ltnS (prednK h_gt0) lt_kh.
    exact: leq_trans (leq_subr j k).
  have j0: j = 0%N.
    apply/eqP; rewrite -leqn0 -(leq_add2l k) -{2}(subnK (ltnW lt_jk)).
    by rewrite addn0 leq_add2r {1}k_h1.
  exists 'n_(j + 1); exists (Ordinal lt_jh) => [|i' ne_i'j]; first exact: dn1j.
  rewrite addn1 {1}(def_n _ (ltnW (valP i'))) j0 leqNgt lt0n -j0.
  by rewrite ne_i'j -ltnS k_h1 (prednK h_gt0) (valP i'); split.
suffices: \sum_(i < h) `|'n_i - 'n_(i + 2)| ^ 2 > 2.
  rewrite -(ltn_add2l (2 * \rank 'E_2)) -diff_rank_quasi_cent_cycle.
  rewrite -mulnSr -rankEm ?ltnn ?modn_small //.
  by rewrite -(prednK h_gt0) ltnS (leq_trans _ lt_kj_h1) // ltnS subn_gt0.
have lt_k1h: k.-1 < h by rewrite ltnW // (ltn_predK lt_jk).
rewrite (bigD1 (Ordinal lt_jh)) // (bigD1 (Ordinal lt_k1h)) /=; last first.
  by rewrite -val_eqE neq_ltn /= orbC -subn1 ltn_subRL lt_j1_k.
rewrite (bigD1 (Ordinal lt_kh)) /=; last first.
  by rewrite -!val_eqE !neq_ltn /= lt_jk (ltn_predK lt_jk) leqnn !orbT.
rewrite !addnA ltn_addr // !addn2 (ltn_predK lt_jk) n_k1.
rewrite (def_n j (ltnW lt_jh)) leqnn (def_n _ (ltn_trans lt_j1_k lt_kh)).
rewrite lt_j1_k -if_neg -leqNgt leqnSn n_j1.
rewrite (def_n _ (ltnW lt_k1h)) leq_pred -if_neg -ltnNge.
rewrite -subn1 ltn_subRL lt_j1_k n_j1.
suffices ->: 'n_k.+2 = 'n_k.+1.
  by rewrite distnC -n_k1 -(addn1 k) -/(dn1 k) (eqP dn1k).
case: (leqP k.+2 h) => [le_k2h | ].
  by rewrite (def_n _ le_k2h) (leqNgt _ k) leqnSn n_k1 if_same.
rewrite ltnS leq_eqVlt ltnNge lt_kh orbF; move/eqP=> def_h.
rewrite -{1}def_h -add1n rank_step_eigenspace_cycle (def_n _ h_gt0).
rewrite -(subSn (ltnW lt_jk)) def_h leq_subLR in lt_kj_h1.
by rewrite -(leq_add2r k) lt_kj_h1 n_k1.
Qed.

(* This is B & G, Proposition 2.4(k). *)
Proposition rank_eigenspaces_free_quasi_homocyclic :
  q > 1 -> 'n_0 = 0%N -> h = q.+1 /\ (forall j, j != 0 %[mod h] -> 'n_j = 1%N).
Proof.
move=> q_gt1 n_0; rewrite mod0n.
have [n d_q_hn [i [n_i lt_q_hn n_i']]] := rank_eigenspaces_quasi_homocyclic.
move/eqP: d_q_hn; rewrite distn_eq1 {}lt_q_hn.
case: (eqVneq (Ordinal h_gt0) i) n_i n_i' => [<- | ne0i _ n_i']; last first.
  by rewrite -(n_i' _ ne0i) n_0 /= muln0 -(subnKC q_gt1).
rewrite n_0 dist0n => -> n_i'; rewrite muln1 => /eqP->; split=> // i'.
by move/(n_i' (inh i')); rewrite /n_ Vi_mod.
Qed.

End QuasiRegularCyclic.

(* This is B & G, Theorem 2.5, used for Theorems 3.4 and 15.7. *)
Theorem repr_extraspecial_prime_sdprod_cycle p n gT (G P H : {group gT}) :
    p.-group P -> extraspecial P -> P ><| H = G -> cyclic H ->
    let h := #|H| in #|P| = (p ^ n.*2.+1)%N -> coprime p h ->
    {in H^#, forall x, 'C_P[x] = 'Z(P)} ->
  (h %| p ^ n + 1) || (h %| p ^ n - 1)
  /\ ((h != p ^ n + 1)%N -> forall F q (rG : mx_representation F G q),
      [char F]^'.-group G -> mx_faithful rG -> rfix_mx rG H != 0).
Proof.
move=> pP esP sdPH_G cycH h oPpn co_p_h primeHP.
set dvd_h_pn := _ || _; set neq_h_pn := h != _.
suffices IH F q (rG : mx_representation F G q):
    [char F]^'.-group G -> mx_faithful rG ->
  dvd_h_pn && (neq_h_pn ==> (rfix_mx rG H != 0)).
- split=> [|ne_h F q rG F'G ffulG]; last first.
    by case/andP: (IH F q rG F'G ffulG) => _; rewrite ne_h.
  pose r := pdiv #|G|.+1.
  have r_pr: prime r by rewrite pdiv_prime // ltnS cardG_gt0.
  have F'G: [char 'F_r]^'.-group G.
    rewrite /pgroup (eq_pnat _ (eq_negn (charf_eq (char_Fp r_pr)))).
    rewrite p'natE // -prime_coprime // (coprime_dvdl (pdiv_dvd _)) //.
    by rewrite /coprime -addn1 gcdnC gcdnDl gcdn1.
  by case/andP: (IH _ _ _ F'G (regular_mx_faithful _ _)).
move=> F'G ffulG.
without loss closF: F rG F'G ffulG / group_closure_field F gT.
  move=> IH; apply: (@group_closure_field_exists gT F) => [[Fs f clFs]].
  rewrite -(map_mx_eq0 f) map_rfix_mx {}IH ?map_mx_faithful //.
  by rewrite (eq_p'group _ (fmorph_char f)).
have p_pr := extraspecial_prime pP esP; have p_gt1 := prime_gt1 p_pr.
have oZp := card_center_extraspecial pP esP; have[_ prZ] := esP.
have{sdPH_G} [nsPG sHG defG nPH tiPH] := sdprod_context sdPH_G.
have sPG := normal_sub nsPG.
have coPH: coprime #|P| #|H| by rewrite oPpn coprime_pexpl.
have nsZG: 'Z(P) <| G := char_normal_trans (center_char _) nsPG.
have defCP: 'C_G(P) = 'Z(P).
  apply/eqP; rewrite eqEsubset andbC setSI //=.
  rewrite -(coprime_mulG_setI_norm defG) ?norms_cent ?normal_norm //=.
  rewrite mul_subG // -(setD1K (group1 H)).
  apply/subsetP=> x; case/setIP; case/setU1P=> [-> // | H'x].
  rewrite -sub_cent1; move/setIidPl; rewrite primeHP // => defP.
  by have:= min_card_extraspecial pP esP; rewrite -defP oZp (leq_exp2l 3 1).
have F'P: [char F]^'.-group P by exact: pgroupS sPG F'G.
have F'H: [char F]^'.-group H by exact: pgroupS sHG F'G.
wlog{ffulG F'G} [irrG regZ]: q rG / mx_irreducible rG /\ rfix_mx rG 'Z(P) = 0.
  move=> IH; wlog [I W /= simW defV _]: / mxsemisimple rG 1%:M.
    exact: (mx_reducible_semisimple (mxmodule1 _) (mx_Maschke rG F'G)).
  have [z Zz ntz]: exists2 z, z \in 'Z(P) & z != 1%g.
    by apply/trivgPn; rewrite -cardG_gt1 oZp prime_gt1.
  have Gz := subsetP sPG z (subsetP (center_sub P) z Zz).
  case: (pickP (fun i => z \notin rstab rG (W i))) => [i ffZ | z1]; last first.
    case/negP: ntz; rewrite -in_set1 (subsetP ffulG) // inE Gz /=.
    apply/eqP; move/eqmxP: defV; case/andP=> _; case/sub_sumsmxP=> w ->.
    rewrite mulmx_suml; apply: eq_bigr => i _.
    by move/negbFE: (z1 i) => /rstab_act-> //; rewrite submxMl.
  have [modW _ _] := simW i; pose rW := submod_repr modW.
  rewrite -(eqmx_rstab _ (val_submod1 (W i))) -(rstab_submod modW) in ffZ.
  have irrW: mx_irreducible rW by exact/submod_mx_irr.
  have regZ: rfix_mx rW 'Z(P)%g = 0.
    apply/eqP; apply: contraR ffZ; case/mx_irrP: irrW => _ minW /minW.
    by rewrite normal_rfix_mx_module // -sub1mx inE Gz /= => /implyP/rfix_mxP->.
  have ffulP: P :&: rker rW = 1%g.
    apply: (TI_center_nil (pgroup_nil pP)).
      by rewrite /normal subsetIl normsI ?normG ?(subset_trans _ (rker_norm _)).
    rewrite /= setIC setIA (setIidPl (center_sub _)); apply: prime_TIg=> //.
    by apply: contra ffZ => /subsetP->.
  have cPker: rker rW \subset 'C_G(P).
    rewrite subsetI rstab_sub (sameP commG1P trivgP) /= -ffulP subsetI.
    rewrite commg_subl commg_subr (subset_trans sPG) ?rker_norm //.
    by rewrite (subset_trans (rstab_sub _ _)) ?normal_norm.
  have [->] := andP (IH _ _ (conj irrW regZ)); case: (neq_h_pn) => //.
  apply: contra; rewrite (eqmx_eq0 (rfix_submod modW sHG)) => /eqP->.
  by rewrite capmx0 linear0.
pose rP := subg_repr rG sPG; pose rH := subg_repr rG sHG.
wlog [M simM _]: / exists2 M, mxsimple rP M & (M <= 1%:M)%MS.
  by apply: (mxsimple_exists (mxmodule1 _)); last case irrG.
have{M simM irrG regZ F'P} [irrP def_q]: mx_irreducible rP /\ q = (p ^ n)%N.
  have [modM nzM _]:= simM.
  have [] := faithful_repr_extraspecial _ _ oPpn _ _ simM => // [|<- isoM].
    apply/eqP; apply: (TI_center_nil (pgroup_nil pP)).
      rewrite /= -(eqmx_rstab _ (val_submod1 M)) -(rstab_submod modM).
      exact: rker_normal.
    rewrite setIC prime_TIg //=; apply: contra nzM => cMZ.
    rewrite -submx0 -regZ; apply/rfix_mxP=> z; move/(subsetP cMZ)=> cMz.
    by rewrite (rstab_act cMz).
  suffices irrP: mx_irreducible rP.
    by split=> //; apply/eqP; rewrite eq_sym; case/mx_irrP: irrP => _; exact.
  apply: (@mx_irr_prime_index F _ G P _ M nsPG) => // [|x Gx].
    by rewrite -defG quotientMidl quotient_cyclic.
  rewrite (bool_irrelevance (normal_sub nsPG) sPG).
  apply: isoM; first exact: (@Clifford_simple _ _ _ _ nsPG).
  have cZx: x \in 'C_G('Z(P)).
    rewrite (setIidPl _) // -defG mulG_subG centsC subsetIr.
    rewrite -(setD1K (group1 H)) subUset sub1G /=.
    by apply/subsetP=> y H'y; rewrite -sub_cent1 -(primeHP y H'y) subsetIr.
  by have [f] := Clifford_iso nsZG rG M cZx; exists f.
pose E_P := enveloping_algebra_mx rP; have{irrP} absP := closF P _ _ irrP.
have [q_gt0 EPfull]: q > 0 /\ (1%:M <= E_P)%MS by apply/andP; rewrite sub1mx.
pose Z := 'Z(P); have [sZP nZP] := andP (center_normal P : Z <| P).
have nHZ: H \subset 'N(Z) := subset_trans sHG (normal_norm nsZG).
pose clPqH := [set Zx ^: (H / Z) | Zx in P / Z]%g.
pose b (ZxH : {set coset_of Z}) := repr (repr ZxH).
have Pb ZxH: ZxH \in clPqH -> b ZxH \in P.
  case/imsetP=> Zx P_Zx ->{ZxH}.
  rewrite -(quotientGK (center_normal P)) /= -/Z inE repr_coset_norm /=.
  rewrite inE coset_reprK; apply: subsetP (mem_repr _ (class_refl _ _)).
  rewrite -class_support_set1l class_support_sub_norm ?sub1set //.
  by rewrite quotient_norms.
have{primeHP coPH} card_clPqH ZxH: ZxH \in clPqH^# -> #|ZxH| = #|H|.
  case/setD1P=> ntZxH P_ZxH.
  case/imsetP: P_ZxH ntZxH => Zx P_Zx ->{ZxH}; rewrite classG_eq1 => ntZx.
  rewrite -index_cent1 ['C__[_]](trivgP _).
    rewrite indexg1 card_quotient // -indexgI setICA setIA tiPH.
    by rewrite (setIidPl (sub1G _)) indexg1.
  apply/subsetP=> Zy => /setIP[/morphimP[y Ny]]; rewrite -(setD1K (group1 H)).
  case/setU1P=> [-> | Hy] ->{Zy} cZxy; first by rewrite morph1 set11.
  have: Zx \in 'C_(P / Z)(<[y]> / Z).
    by rewrite inE P_Zx quotient_cycle // cent_cycle cent1C.
  case/idPn; rewrite -coprime_quotient_cent ?cycle_subG ?(pgroup_sol pP) //.
    by rewrite /= cent_cycle primeHP // trivg_quotient inE.
  by apply: coprimegS coPH; rewrite cycle_subG; case/setD1P: Hy.
pose B x := \matrix_(i < #|H|) mxvec (rP (x ^ enum_val i)%g).
have{E_P EPfull absP} sumB: (\sum_(ZxH in clPqH) <<B (b ZxH)>> :=: 1%:M)%MS.
  apply/eqmxP; rewrite submx1 (submx_trans EPfull) //.
  apply/row_subP=> ix; set x := enum_val ix; pose ZxH := coset Z x ^: (H / Z)%g.
  have Px: x \in P by [rewrite enum_valP]; have nZx := subsetP nZP _ Px.
  have P_ZxH: ZxH \in clPqH by apply: mem_imset; rewrite mem_quotient.
  have Pbx := Pb _ P_ZxH; have nZbx := subsetP nZP _ Pbx.
  rewrite rowK (sumsmx_sup ZxH) {P_ZxH}// genmxE -/x.
  have: coset Z x \in coset Z (b ZxH) ^: (H / Z)%g.
    by rewrite class_sym coset_reprK (mem_repr _ (class_refl _ _)).
  case/imsetP=> _ /morphimP[y Ny Hy ->].
  rewrite -morphJ //; case/kercoset_rcoset; rewrite ?groupJ // => z Zz ->.
  have [Pz cPz] := setIP Zz; rewrite repr_mxM ?memJ_norm ?(subsetP nPH) //.
  have [a ->]: exists a, rP z = a%:M.
    apply/is_scalar_mxP; apply: (mx_abs_irr_cent_scalar absP).
    by apply/centgmxP=> t Pt; rewrite -!repr_mxM ?(centP cPz).
  rewrite mul_scalar_mx linearZ scalemx_sub //.
  by rewrite (eq_row_sub (gring_index H y)) // rowK gring_indexK.
have{card_clPqH} Bfree_if ZxH:
  ZxH \in clPqH^# -> \rank <<B (b ZxH)>> <= #|ZxH| ?= iff row_free (B (b ZxH)).
- by move=> P_ZxH; rewrite genmxE card_clPqH // /leqif rank_leq_row.
have B1_if: \rank <<B (b 1%g)>> <= 1 ?= iff (<<B (b 1%g)>> == mxvec 1%:M)%MS.
  have r1: \rank (mxvec 1%:M : 'rV[F]_(q ^ 2)) = 1%N.
    by rewrite rank_rV mxvec_eq0 -mxrank_eq0 mxrank1 -lt0n q_gt0.
  rewrite -{1}r1; apply: mxrank_leqif_eq; rewrite genmxE.
  have ->: b 1%g = 1%g by rewrite /b repr_set1 repr_coset1.
  by apply/row_subP=> i; rewrite rowK conj1g repr_mx1.
have rankEP: \rank (1%:M : 'A[F]_q) = (\sum_(ZxH in clPqH) #|ZxH|)%N.
  rewrite acts_sum_card_orbit ?astabsJ ?quotient_norms // card_quotient //.
  rewrite mxrank1 -divgS // -mulnn oPpn oZp expnS -muln2 expnM -def_q.
  by rewrite mulKn // ltnW.
have cl1: 1%g \in clPqH by apply/imsetP; exists 1%g; rewrite ?group1 ?class1G.
have{B1_if Bfree_if}:= leqif_add B1_if (leqif_sum Bfree_if).
case/(leqif_trans (mxrank_sum_leqif _)) => _ /=.
rewrite -{1}(big_setD1 _ cl1) sumB {}rankEP (big_setD1 1%g) // cards1 eqxx.
case/esym/and3P=> dxB /eqmxP defB1 /forall_inP/= Bfree.
have [yg defH] := cyclicP cycH; pose g := rG yg.
have Hxg: yg \in H by [rewrite defH cycle_id]; have Gyg := subsetP sHG _ Hxg.
pose gE : 'A_q := lin_mx (mulmx (invmx g) \o mulmxr g).
pose yr := regular_repr F H yg.
have mulBg x: x \in P -> B x *m gE = yr *m B x.
  move/(subsetP sPG)=> Gx.
  apply/row_matrixP=> i; have Hi := enum_valP i; have Gi := subsetP sHG _ Hi.
  rewrite 2!row_mul !rowK mul_vec_lin /= -rowE rowK gring_indexK ?groupM //.
  by rewrite conjgM -repr_mxV // -!repr_mxM // ?(groupJ, groupM, groupV).
wlog sH: / irrType F H by exact: socle_exists.
have{cycH} linH: irr_degree (_ : sH) = 1%N.
  exact: irr_degree_abelian (cyclic_abelian cycH).
have baseH := linear_irr_comp F'H (closF H) (linH _).
have{linH} linH (W : sH): \rank W = 1%N by rewrite baseH; exact: linH.
have [w] := cycle_repr_structure sH defH F'H (closF H).
rewrite -/h => prim_w [Wi [bijWi _ _ Wi_yg]].
have{Wi_yg baseH} Wi_yr i: Wi i *m yr = w ^+ i *: (Wi i : 'M_h).
  have /submxP[u ->]: (Wi i <= val_submod (irr_repr (Wi i) 1%g))%MS.
    by rewrite repr_mx1 val_submod1 -baseH.
  rewrite repr_mx1 -mulmxA -2!linearZ; congr (u *m _).
  by rewrite -mul_mx_scalar -Wi_yg /= val_submodJ.
pose E_ m := eigenspace gE (w ^+ m).
have dxE: mxdirect (\sum_(m < h) E_ m)%MS.
  apply: mxdirect_sum_eigenspace => m1 m2 _ _ eq_m12; apply/eqP.
  by move/eqP: eq_m12; rewrite (eq_prim_root_expr prim_w) !modn_small.
pose B2 ZxH i : 'A_q := <<Wi i *m B (b ZxH)>>%MS.
pose B1 i : 'A_q := (\sum_(ZxH in clPqH^#) B2 ZxH i)%MS.
pose SB := (<<B (b 1%g)>> + \sum_i B1 i)%MS.
have{yr Wi_yr Pb mulBg} sB1E i: (B1 i <= E_ i)%MS.
  apply/sumsmx_subP=> ZxH /setIdP[_]; rewrite genmxE => P_ZxH.
  by apply/eigenspaceP; rewrite -mulmxA mulBg ?Pb // mulmxA Wi_yr scalemxAl.
have{bijWi sumB cl1 F'H} defSB: (SB :=: 1%:M)%MS.
  apply/eqmxP; rewrite submx1 -sumB (big_setD1 _ cl1) addsmxS //=.
  rewrite exchange_big sumsmxS // => ZxH _; rewrite genmxE /= -sumsmxMr_gen.
  rewrite -((reindex Wi) xpredT val) /=; last by exact: onW_bij.
  by rewrite -/(Socle _) (reducible_Socle1 sH (mx_Maschke _ F'H)) mul1mx.
rewrite mxdirect_addsE /= in dxB; case/and3P: dxB => _ dxB dxB1.
have{linH Bfree dxB} rankB1 i: \rank (B1 i) = #|clPqH^#|.
  rewrite -sum1_card (mxdirectP _) /=.
    by apply: eq_bigr => ZxH P_ZxH; rewrite genmxE mxrankMfree ?Bfree.
  apply/mxdirect_sumsP=> ZxH P_ZxH.
  apply/eqP; rewrite -submx0 -{2}(mxdirect_sumsP dxB _ P_ZxH) capmxS //.
    by rewrite !genmxE submxMl.
  by rewrite sumsmxS // => ZyH _; rewrite !genmxE submxMl.
have rankEi (i : 'I_h) : i != 0%N :> nat -> \rank (E_ i) = #|clPqH^#|.
  move=> i_gt0; apply/eqP; rewrite -(rankB1 i) (mxrank_leqif_sup _) ?sB1E //.
  rewrite -[E_ i]cap1mx -(cap_eqmx defSB (eqmx_refl _)) /SB.
  rewrite (bigD1 i) //= (addsmxC (B1 i)) addsmxA addsmxC -matrix_modl //.
  rewrite -(addsmx0 (q ^ 2) (B1 i)) addsmxS //.
  rewrite capmxC -{2}(mxdirect_sumsP dxE i) // capmxS // addsmx_sub // .
  rewrite (sumsmx_sup (Ordinal (cardG_gt0 H))) ?sumsmxS 1?eq_sym //.
  rewrite defB1; apply/eigenspaceP; rewrite mul_vec_lin scale1r /=.
  by rewrite mul1mx mulVmx ?repr_mx_unit.
have{b B defB1 rP rH sH Wi rankB1 dxB1 defSB sB1E B1 B2 dxE SB} rankE0 i:
  (i : 'I_h) == 0%N :> nat -> \rank (E_ i) = #|clPqH^#|.+1.
- move=> i_eq0; rewrite -[E_ i]cap1mx -(cap_eqmx defSB (eqmx_refl _)) /SB.
  rewrite (bigD1 i) // addsmxA -matrix_modl; last first.
    rewrite addsmx_sub // sB1E andbT defB1; apply/eigenspaceP.
    by rewrite mul_vec_lin (eqP i_eq0) scale1r /= mul1mx mulVmx ?repr_mx_unit.
  rewrite (((_ :&: _)%MS =P 0) _).
    rewrite addsmx0 mxrank_disjoint_sum /=.
      by rewrite defB1 rank_rV rankB1 mxvec_eq0 -mxrank_eq0 mxrank1 -lt0n q_gt0.
    apply/eqP; rewrite -submx0 -(eqP dxB1) capmxS // sumsmxS // => ZxH _.
    by rewrite !genmxE ?submxMl.
  by rewrite -submx0 capmxC /= -{2}(mxdirect_sumsP dxE i) // capmxS ?sumsmxS.
have{clPqH rankE0 rankEi} (m):
  m != 0 %[mod h] -> \rank (E_ 0%N) = (\rank (E_ m)).+1.
- move=> nz_m; rewrite (rankE0 (Ordinal (cardG_gt0 H))) //.
  rewrite /E_ -(prim_expr_mod prim_w); rewrite mod0n in nz_m.
  have lt_m: m %% h < h by rewrite ltn_mod ?cardG_gt0.
  by rewrite (rankEi (Ordinal lt_m)).
have: q > 1.
  rewrite def_q (ltn_exp2l 0) // lt0n.
  apply: contraL (min_card_extraspecial pP esP).
  by rewrite oPpn; move/eqP->; rewrite leq_exp2l.
rewrite {}/E_ {}/gE {}/dvd_h_pn {}/neq_h_pn -{n oPpn}def_q subn1 addn1 /=.
case: q q_gt0 => // q' _ in rG g * => q_gt1 rankE.
have gh1: g ^+ h = 1 by rewrite -repr_mxX // /h defH expg_order repr_mx1.
apply/andP; split.
  have [n' def_q _]:= rank_eigenspaces_quasi_homocyclic gh1 prim_w rankE.
  move/eqP: def_q; rewrite distn_eq1 eqSS.
  by case: ifP => _ /eqP->; rewrite dvdn_mulr ?orbT.
apply/implyP; apply: contra => regH.
have [|-> //]:= rank_eigenspaces_free_quasi_homocyclic gh1 prim_w rankE q_gt1.
apply/eqP; rewrite mxrank_eq0 -submx0 -(eqP regH).
apply/rV_subP=> v /eigenspaceP; rewrite scale1r => cvg.
apply/rfix_mxP=> y Hy; apply: rstab_act (submx_refl v); apply: subsetP y Hy.
by rewrite defH cycle_subG !inE Gyg /= cvg.
Qed.

(* This is the main part of B & G, Theorem 2.6; it implies 2.6(a) and most of *)
(* 2.6(b).                                                                    *)
Theorem der1_odd_GL2_charf F gT (G : {group gT})
                           (rG : mx_representation F G 2) :
 odd #|G| -> mx_faithful rG -> [char F].-group G^`(1)%g.
Proof.
move=> oddG ffulG.
without loss closF: F rG ffulG / group_closure_field F gT.
  move=> IH; apply: (@group_closure_field_exists gT F) => [[Fc f closFc]].
  rewrite -(eq_pgroup _ (fmorph_char f)).
  by rewrite -(map_mx_faithful f) in ffulG; exact: IH ffulG closFc.
elim: {G}_.+1 {-2}G (ltnSn #|G|) => // m IHm G le_g_m in rG oddG ffulG *.
apply/pgroupP=> p p_pr pG'; rewrite !inE p_pr /=; apply: wlog_neg => p_nz.
have [P sylP] := Sylow_exists p G.
have nPG: G \subset 'N(P).
  apply/idPn=> ltNG; pose N := 'N_G(P); have sNG: N \subset G := subsetIl _ _.
  have{IHm ltNG} p'N': [char F].-group N^`(1)%g.
    apply: IHm (subg_mx_faithful sNG ffulG); last exact: oddSg oddG.
    rewrite -ltnS (leq_trans _ le_g_m) // ltnS proper_card //.
    by rewrite /proper sNG subsetI subxx.
  have{p'N'} tiPN': P :&: N^`(1)%g = 1%g.
    rewrite coprime_TIg ?(pnat_coprime (pHall_pgroup sylP)) //= -/N.
    apply: sub_in_pnat p'N' => q _; apply: contraL; move/eqnP->.
    by rewrite !inE p_pr.
  have sPN: P \subset N by rewrite subsetI normG (pHall_sub sylP).
  have{tiPN'} cPN: N \subset 'C(P).
    rewrite (sameP commG1P trivgP) -tiPN' subsetI commgS //.
    by rewrite commg_subr subsetIr.
  have /sdprodP[_ /= defG nKP _] := Burnside_normal_complement sylP cPN.
  set K := 'O_p^'(G) in defG nKP; have nKG: G \subset 'N(K) by exact: gFnorm.
  suffices p'G': p^'.-group G^`(1)%g by case/eqnP: (pgroupP p'G' p p_pr pG').
  apply: pgroupS (pcore_pgroup p^' G); rewrite -quotient_cents2 //= -/K.
  by rewrite -defG quotientMidl /= -/K quotient_cents ?(subset_trans sPN).
pose Q := G^`(1)%g :&: P; have sQG: Q \subset G by rewrite subIset ?der_subS.
have nQG: G \subset 'N(Q) by rewrite normsI // normal_norm ?der_normalS.
have pQ: (p %| #|Q|)%N.
  have sylQ: p.-Sylow(G^`(1)%g) Q.
    by apply: Sylow_setI_normal (der_normalS _ _) _.
  apply: contraLR pG'; rewrite -!p'natE // (card_Hall sylQ) -!partn_eq1 //.
  by rewrite part_pnat_id ?part_pnat.
have{IHm} abelQ: abelian Q.
  apply/commG1P/eqP/idPn => ntQ'.
  have{IHm} p'Q': [char F].-group Q^`(1)%g.
    apply: IHm (subg_mx_faithful sQG ffulG); last exact: oddSg oddG.
    rewrite -ltnS (leq_trans _ le_g_m) // ltnS proper_card //.
    rewrite /proper sQG subsetI //= andbC subEproper.
    case: eqP => [-> /= | _]; last by rewrite /proper (pHall_sub sylP) andbF.
    have: nilpotent P by rewrite (pgroup_nil (pHall_pgroup sylP)).
    move/forallP/(_ P); apply: contraL; rewrite subsetI subxx => -> /=.
    apply: contra ntQ'; rewrite /Q => /eqP->.
    by rewrite (setIidPr _) ?sub1G // commG1.
  case/eqP: ntQ';  have{p'Q'}: P :&: Q^`(1)%g = 1%g.
    rewrite coprime_TIg ?(pnat_coprime (pHall_pgroup sylP)) //= -/Q.
    by rewrite (pi_p'nat p'Q') // !inE p_pr.
  by rewrite (setIidPr _) // comm_subG ?subsetIr.
pose rQ := subg_repr rG sQG.
wlog [U simU sU1]: / exists2 U, mxsimple rQ U & (U <= 1%:M)%MS.
  by apply: mxsimple_exists; rewrite ?mxmodule1 ?oner_eq0.
have Uscal: \rank U = 1%N by exact: (mxsimple_abelian_linear (closF _)) simU.
have{simU} [Umod _ _] := simU.
have{sU1} [|V Vmod sumUV dxUV] := mx_Maschke _ _ Umod sU1.
  have: p.-group Q by apply: pgroupS (pHall_pgroup sylP); rewrite subsetIr.
  by apply: sub_in_pnat=> q _; move/eqnP->; rewrite !inE p_pr.
have [u defU]: exists u : 'rV_2, (u :=: U)%MS.
  by move: (row_base U) (eq_row_base U); rewrite Uscal => u; exists u.
have{dxUV Uscal} [v defV]: exists v : 'rV_2, (v :=: V)%MS.
  move/mxdirectP: dxUV; rewrite /= Uscal sumUV mxrank1 => [[Vscal]].
  by move: (row_base V) (eq_row_base V); rewrite -Vscal => v; exists v.
pose B : 'M_(1 + 1) := col_mx u v; have{sumUV} uB: B \in unitmx.
  rewrite -row_full_unit /row_full eqn_leq rank_leq_row {1}addn1.
  by rewrite -addsmxE -(mxrank1 F 2) -sumUV mxrankS // addsmxS ?defU ?defV.
pose Qfix (w : 'rV_2) := {in Q, forall y, w *m rG y <= w}%MS.
have{U defU Umod} u_fix: Qfix u.
  by move=> y Qy; rewrite /= (eqmxMr _ defU) defU (mxmoduleP Umod).
have{V defV Vmod} v_fix: Qfix v.
  by move=> y Qy; rewrite /= (eqmxMr _ defV) defV (mxmoduleP Vmod).
case/Cauchy: pQ => // x Qx oxp; have Gx := subsetP sQG x Qx.
case/submxP: (u_fix x Qx) => a def_ux.
case/submxP: (v_fix x Qx) => b def_vx.
have def_x: rG x = B^-1 *m block_mx a 0 0 b *m B.
  rewrite -mulmxA -[2]/(1 + 1)%N mul_block_col !mul0mx addr0 add0r.
  by rewrite -def_ux -def_vx -mul_col_mx mulKmx.
have ap1: a ^+ p = 1.
  suff: B^-1 *m block_mx (a ^+ p) 0 0 (b ^+ p) *m B = 1.
    move/(canRL (mulmxK uB))/(canRL (mulKVmx uB)); rewrite mul1mx.
    by rewrite mulmxV // scalar_mx_block; case/eq_block_mx.
  transitivity (rG x ^+ p); last first.
    by rewrite -(repr_mxX (subg_repr rG sQG)) // -oxp expg_order repr_mx1.
  elim: (p) => [|k IHk]; first by rewrite -scalar_mx_block mulmx1 mulVmx.
  rewrite !exprS -IHk def_x -!mulmxE !mulmxA mulmxK // -2!(mulmxA B^-1).
  by rewrite -[2]/(1 + 1)%N mulmx_block !mulmx0 !mul0mx !addr0 mulmxA add0r.
have ab1: a * b = 1.
  have: Q \subset <<[set y in G | \det (rG y) == 1]>>.
  rewrite subIset // genS //; apply/subsetP=> yz; case/imset2P=> y z Gy Gz ->.
    rewrite inE !repr_mxM ?groupM ?groupV //= !detM (mulrCA _ (\det (rG y))). 
    rewrite -!det_mulmx -!repr_mxM ?groupM ?groupV //.
    by rewrite mulKg mulVg repr_mx1 det1.
  rewrite gen_set_id; last first.
    apply/group_setP; split=> [|y z /setIdP[Gy /eqP y1] /setIdP[Gz /eqP z1]].
      by rewrite inE group1 /= repr_mx1 det1.
    by rewrite inE groupM ?repr_mxM //= detM y1 z1 mulr1.
  case/subsetP/(_ x Qx)/setIdP=> _.
  rewrite def_x !detM mulrAC -!detM -mulrA mulKr // -!mulmxE.
  rewrite -[2]/(1 + 1)%N det_lblock // [a]mx11_scalar [b]mx11_scalar.
  by rewrite !det_scalar1 -scalar_mxM => /eqP->.
have{ab1 ap1 def_x} ne_ab: a != b.
  apply/eqP=> defa; have defb: b = 1.
    rewrite -ap1 (divn_eq p 2) modn2.
    have ->: odd p by rewrite -oxp (oddSg _ oddG) // cycle_subG.
    by rewrite addn1 exprS mulnC exprM exprS {1 3}defa ab1 expr1n mulr1.
  suff x1: x \in [1] by rewrite -oxp (set1P x1) order1 in p_pr.
  rewrite (subsetP ffulG) // inE Gx def_x defa defb -scalar_mx_block mulmx1.
  by rewrite mul1mx mulVmx ?eqxx.
have{a b ne_ab def_ux def_vx} nx_uv (w : 'rV_2):
  (w *m rG x <= w -> w <= u \/ w <= v)%MS.
- case/submxP=> c; have:= mulmxKV uB w.
  rewrite -[_ *m invmx B]hsubmxK [lsubmx _]mx11_scalar [rsubmx _]mx11_scalar.
  move: (_ 0) (_ 0) => dv du; rewrite mul_row_col !mul_scalar_mx => <-{w}.
  rewrite mulmxDl -!scalemxAl def_ux def_vx mulmxDr -!scalemxAr.
  rewrite !scalemxAl -!mul_row_col; move/(can_inj (mulmxK uB)).
  case/eq_row_mx => eqac eqbc; apply/orP.
  have [-> | nz_dv] := eqVneq dv 0; first by rewrite scale0r addr0 scalemx_sub.
  have [-> | nz_du] := eqVneq du 0.
    by rewrite orbC scale0r add0r scalemx_sub.
  case/eqP: ne_ab; rewrite -[b]scale1r -(mulVf nz_dv) -[a]scale1r.
  by rewrite -(mulVf nz_du) -!scalerA eqac eqbc !scalerA !mulVf.
have{x Gx Qx oxp nx_uv} redG y (A := rG y):
  y \in G -> (u *m A <= u /\ v *m A <= v)%MS.
- move=> Gy; have uA: row_free A by rewrite row_free_unit repr_mx_unit.
  have Ainj (w t : 'rV_2): (w *m A <= w -> t *m A <= w -> t *m A <= t)%MS.
    case/sub_rVP=> [c ryww] /sub_rVP[d rytw].
    rewrite -(submxMfree _ _ uA) rytw -scalemxAl ryww scalerA mulrC.
    by rewrite -scalerA scalemx_sub.
  have{Qx nx_uv} nAx w: Qfix w -> (w *m A <= u \/ w *m A <= v)%MS.
    move=> nwQ; apply: nx_uv; rewrite -mulmxA -repr_mxM // conjgCV.
    rewrite repr_mxM ?groupJ ?groupV // mulmxA submxMr // nwQ // -mem_conjg.
    by rewrite (normsP nQG).
  have [uAu | uAv] := nAx _ u_fix; have [vAu | vAv] := nAx _ v_fix; eauto.
  have [k ->]: exists k, A = A ^+ k.*2.
    exists #[y].+1./2; rewrite -mul2n -divn2 mulnC divnK.
      by rewrite -repr_mxX // expgS expg_order mulg1.
    by rewrite dvdn2 negbK; apply: oddSg oddG; rewrite cycle_subG.
  elim: k => [|k [IHu IHv]]; first by rewrite !mulmx1.
  case/sub_rVP: uAv => c uAc; case/sub_rVP: vAu => d vAd.
  rewrite doubleS !exprS !mulmxA; do 2!rewrite uAc vAd -!scalemxAl.
  by rewrite !scalemx_sub.
suffices trivG': G^`(1)%g = 1%g.
  by rewrite /= trivG' cards1 gtnNdvd ?prime_gt1 in pG'.
apply/trivgP; apply: subset_trans ffulG; rewrite gen_subG.
apply/subsetP=> _ /imset2P[y z Gy Gz ->]; rewrite inE groupR //=.
rewrite -(inj_eq (can_inj (mulKmx (repr_mx_unit rG (groupM Gz Gy))))).
rewrite mul1mx mulmx1 -repr_mxM ?(groupR, groupM) // -commgC !repr_mxM //.
rewrite -(inj_eq (can_inj (mulKmx uB))) !mulmxA !mul_col_mx.
case/redG: Gy => /sub_rVP[a uya] /sub_rVP[b vyb].
case/redG: Gz => /sub_rVP[c uzc] /sub_rVP[d vzd].
by do 2!rewrite uya vyb uzc vzd -?scalemxAl; rewrite !scalerA mulrC (mulrC d).
Qed.

(* This is B & G, Theorem 2.6(a) *)
Theorem charf'_GL2_abelian F gT (G : {group gT})
                           (rG : mx_representation F G 2) :
  odd #|G| -> mx_faithful rG -> [char F]^'.-group G -> abelian G.
Proof.
move=> oddG ffG char'G; apply/commG1P/eqP.
rewrite trivg_card1 (pnat_1 _ (pgroupS _ char'G)) ?comm_subG //=.
exact: der1_odd_GL2_charf ffG.
Qed.

(* This is B & G, Theorem 2.6(b) *)
Theorem charf_GL2_der_subS_abelian_Sylow p F gT (G : {group gT})
                                         (rG : mx_representation F G 2) :
    odd #|G| -> mx_faithful rG -> p \in [char F] ->
  exists P : {group gT}, [/\ p.-Sylow(G) P, abelian P & G^`(1)%g \subset P].
Proof.
move=> oddG ffG charFp.
have{oddG} pG': p.-group G^`(1)%g.
  rewrite /pgroup -(eq_pnat _ (charf_eq charFp)).
  exact: der1_odd_GL2_charf ffG.
have{pG'} [P SylP sG'P]:= Sylow_superset (der_sub _ _) pG'.
exists P; split=> {sG'P}//; case/and3P: SylP => sPG pP _.
apply/commG1P/trivgP; apply: subset_trans ffG; rewrite gen_subG.
apply/subsetP=> _ /imset2P[y z Py Pz ->]; rewrite inE (subsetP sPG) ?groupR //=.
pose rP := subg_repr rG sPG; pose U := rfix_mx rP P.
rewrite -(inj_eq (can_inj (mulKmx (repr_mx_unit rP (groupM Pz Py))))).
rewrite mul1mx mulmx1 -repr_mxM ?(groupR, groupM) // -commgC !repr_mxM //.
have: U != 0 by apply: (rfix_pgroup_char charFp).
rewrite -mxrank_eq0 -lt0n 2!leq_eqVlt ltnNge rank_leq_row orbF orbC eq_sym.
case/orP=> [Ufull | Uscal].
  suffices{y z Py Pz} rP1 y: y \in P -> rP y = 1%:M by rewrite !rP1 ?mulmx1.
  move=> Py; apply/row_matrixP=> i.
  by rewrite rowE -row1 (rfix_mxP P _) ?submx_full.
have [u defU]: exists u : 'rV_2, (u :=: U)%MS.
  by move: (row_base U) (eq_row_base U); rewrite -(eqP Uscal) => u; exists u.
have fix_u: {in P, forall x, u *m rP x = u}.
  by move/eqmxP: defU; case/andP; move/rfix_mxP.
have [v defUc]: exists u : 'rV_2, (u :=: U^C)%MS.
  have UCscal: \rank U^C = 1%N by rewrite mxrank_compl -(eqP Uscal).
  by move: (row_base _)%MS (eq_row_base U^C)%MS; rewrite UCscal => v; exists v.
pose B := col_mx u v; have uB: B \in unitmx.
  rewrite -row_full_unit -sub1mx -(eqmxMfull _ (addsmx_compl_full U)).
  by rewrite mulmx1 -addsmxE addsmxS ?defU ?defUc.
have Umod: mxmodule rP U by exact: rfix_mx_module.
pose W := rfix_mx (factmod_repr Umod) P.
have ntW: W != 0. 
  apply: (rfix_pgroup_char charFp) => //.
  rewrite eqmxMfull ?row_full_unit ?unitmx_inv ?row_ebase_unit //.
  by rewrite rank_copid_mx -(eqP Uscal).
have{ntW} Wfull: row_full W.
  by rewrite -col_leq_rank {1}mxrank_coker -(eqP Uscal) lt0n mxrank_eq0.
have svW: (in_factmod U v <= W)%MS by rewrite submx_full.
have fix_v: {in P, forall x, v *m rG x - v <= u}%MS.
  move=> x Px /=; rewrite -[v *m _](add_sub_fact_mod U) (in_factmodJ Umod) //.
  move/rfix_mxP: svW => -> //; rewrite in_factmodK ?defUc // addrK.
  by rewrite defU val_submodP.
have fixB: {in P, forall x, exists2 a, u *m rG x = u & v *m rG x = v + a *: u}.
  move=> x Px; case/submxP: (fix_v x Px) => a def_vx.
  exists (a 0 0); first exact: fix_u.
  by rewrite addrC -mul_scalar_mx -mx11_scalar -def_vx subrK.
rewrite -(inj_eq (can_inj (mulKmx uB))) // !mulmxA !mul_col_mx.
case/fixB: Py => a uy vy; case/fixB: Pz => b uz vz.
by rewrite uy uz vy vz !mulmxDl -!scalemxAl uy uz vy vz addrAC.
Qed.

(* This is B & G, Lemma 2.7. *)
Lemma regular_abelem2_on_abelem2 p q gT (P Q : {group gT}) :
    p.-abelem P -> q.-abelem Q -> 'r_p(P) = 2 ->'r_q(Q) = 2 ->
    Q \subset 'N(P) -> 'C_Q(P) = 1%g ->
  (q %| p.-1)%N
  /\ (exists2 a, a \in Q^# & exists r,
      [/\ {in P, forall x, x ^ a = x ^+ r}%g,
          r ^ q = 1 %[mod p] & r != 1 %[mod p]]).
Proof.
move=> abelP abelQ; rewrite !p_rank_abelem // => logP logQ nPQ regQ.
have ntP: P :!=: 1%g by case: eqP logP => // ->; rewrite cards1 logn1.
have [p_pr _ _]:= pgroup_pdiv (abelem_pgroup abelP) ntP.
have ntQ: Q :!=: 1%g by case: eqP logQ => // ->; rewrite cards1 logn1.
have [q_pr _ _]:= pgroup_pdiv (abelem_pgroup abelQ) ntQ.
pose rQ := abelem_repr abelP ntP nPQ.
have [|P1 simP1 _] := dec_mxsimple_exists (mxmodule1 rQ).
  by rewrite oner_eq0.
have [modP1 nzP1 _] := simP1.
have ffulQ: mx_faithful rQ by exact: abelem_mx_faithful.
have linP1: \rank P1 = 1%N.
  apply/eqP; have:= abelem_cyclic abelQ; rewrite logQ; apply: contraFT.
  rewrite neq_ltn ltnNge lt0n mxrank_eq0 nzP1 => P1full.
  have irrQ: mx_irreducible rQ.
    apply: mx_iso_simple simP1; apply: eqmx_iso; apply/eqmxP.
    by rewrite submx1 sub1mx -col_leq_rank {1}(dim_abelemE abelP ntP) logP.
  exact: mx_faithful_irr_abelian_cyclic irrQ (abelem_abelian abelQ).
have ne_qp: q != p.
  move/implyP: (logn_quotient_cent_abelem nPQ abelP).
  by rewrite logP regQ indexg1 /=; case: eqP => // <-; rewrite logQ.
have redQ: mx_completely_reducible rQ 1%:M.
  apply: mx_Maschke; apply: pi_pnat (abelem_pgroup abelQ) _.
  by rewrite inE /= (charf_eq (char_Fp p_pr)).
have [P2 modP2 sumP12 dxP12] := redQ _ modP1 (submx1 _).
have{dxP12} linP2: \rank P2 = 1%N.
  apply: (@addnI 1%N); rewrite -{1}linP1 -(mxdirectP dxP12) /= sumP12.
  by rewrite mxrank1 (dim_abelemE abelP ntP) logP.
have{sumP12} [u def1]: exists u, 1%:M = u.1 *m P1 + u.2 *m P2.
  by apply/sub_addsmxP; rewrite sumP12.
pose lam (Pi : 'M(P)) b := (nz_row Pi *m rQ b *m pinvmx (nz_row Pi)) 0 0.
have rQ_lam Pi b:
  mxmodule rQ Pi -> \rank Pi = 1%N -> b \in Q -> Pi *m rQ b = lam Pi b *: Pi.
- rewrite /lam => modPi linPi Qb; set v := nz_row Pi; set a := _ 0.
  have nz_v: v != 0 by rewrite nz_row_eq0 -mxrank_eq0 linPi.
  have sPi_v: (Pi <= v)%MS.
    by rewrite -mxrank_leqif_sup ?nz_row_sub // rank_rV nz_v linPi.
  have [v' defPi] := submxP sPi_v; rewrite {2}defPi scalemxAr -mul_scalar_mx.
  rewrite -mx11_scalar !(mulmxA v') -defPi mulmxKpV ?(submx_trans _ sPi_v) //.
  exact: (mxmoduleP modPi).
have lam_q Pi b:
  mxmodule rQ Pi -> \rank Pi = 1%N -> b \in Q -> lam Pi b ^+ q = 1.
- move=> modPi linPi Qb; apply/eqP; rewrite eq_sym -subr_eq0.
  have: \rank Pi != 0%N by rewrite linPi.
  apply: contraR; move/eqmx_scale=> <-.
  rewrite mxrank_eq0 scalerBl subr_eq0 -mul_mx_scalar -(repr_mx1 rQ).
  have <-: (b ^+ q = 1)%g by case/and3P: abelQ => _ _; move/exponentP->.
  apply/eqP; rewrite repr_mxX //.
  elim: (q) => [|k IHk]; first by rewrite scale1r mulmx1.
  by rewrite !exprS mulmxA rQ_lam // -scalemxAl IHk scalerA.
pose f b := (lam P1 b, lam P2 b).
have inj_f: {in Q &, injective f}.
  move=> b c Qb Qc /= [eq_bc1 eq_bc2]; apply: (mx_faithful_inj ffulQ) => //.
  rewrite -[rQ b]mul1mx -[rQ c]mul1mx {}def1 !mulmxDl -!mulmxA.
  by rewrite !{1}rQ_lam ?eq_bc1 ?eq_bc2.
pose rs := [set x : 'F_p | x ^+ q == 1].
have s_fQ_rs: f @: Q \subset setX rs rs.
  apply/subsetP=> _ /imsetP[b Qb ->].
  by rewrite !{1}inE /= !{1}lam_q ?eqxx.
have le_rs_q: #|rs| <= q ?= iff (#|rs| == q).
  split; rewrite // cardE max_unity_roots ?enum_uniq ?prime_gt0 //.
  by apply/allP=> x; rewrite mem_enum inE unity_rootE.
have:= subset_leqif_card s_fQ_rs.
rewrite card_in_imset // (card_pgroup (abelem_pgroup abelQ)) logQ.
case/(leqif_trans (leqif_mul le_rs_q le_rs_q))=> _; move/esym.
rewrite cardsX eqxx andbb muln_eq0 orbb eqn0Ngt prime_gt0 //= => /andP[rs_q].
rewrite subEproper /proper {}s_fQ_rs andbF orbF => /eqP rs2_Q.
have: ~~ (rs \subset [set 1 : 'F_p]).
  apply: contraL (prime_gt1 q_pr); move/subset_leq_card.
  by rewrite cards1 (eqnP rs_q) leqNgt.
case/subsetPn => r rs_r; rewrite inE => ne_r_1.
have rq1: r ^+ q = 1 by apply/eqP; rewrite inE in rs_r.
split.
  have Ur: r \in GRing.unit.
    by rewrite -(unitrX_pos _ (prime_gt0 q_pr)) rq1 unitr1.
  pose u_r : {unit 'F_p} := Sub r Ur; have:= order_dvdG (in_setT u_r).
  rewrite card_units_Zp ?pdiv_gt0 // {2}/pdiv primes_prime //=.
  rewrite (@totient_pfactor p 1) // muln1; apply: dvdn_trans.
  have: (u_r ^+ q == 1)%g.
    by rewrite -val_eqE unit_Zp_expg -Zp_nat natrX natr_Zp rq1.
  case/primeP: q_pr => _ q_min; rewrite -order_dvdn; move/q_min.
  by rewrite order_eq1 -val_eqE (negPf ne_r_1) /=; move/eqnP->.
have /imsetP[a Qa [def_a1 def_a2]]: (r, r) \in f @: Q.
  by rewrite -rs2_Q inE andbb.
have rQa: rQ a = r%:M.
  rewrite -[rQ a]mul1mx def1 mulmxDl -!mulmxA !rQ_lam //.
  by rewrite -def_a1 -def_a2 !linearZ -scalerDr -def1 /= scalemx1.
exists a.
  rewrite !inE Qa andbT; apply: contra ne_r_1 => a1.
  by rewrite (eqP a1) repr_mx1 in rQa; rewrite (fmorph_inj _ rQa).
exists r; rewrite -!val_Fp_nat // natrX natr_Zp rq1.
split=> // x Px; apply: (@abelem_rV_inj _ _ _ abelP ntP); rewrite ?groupX //.
  by rewrite memJ_norm ?(subsetP nPQ).
by rewrite abelem_rV_X // -mul_mx_scalar natr_Zp -rQa -abelem_rV_J.
Qed.

End BGsection2.
