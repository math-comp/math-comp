(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From mathcomp Require Import div choice fintype tuple finfun bigop prime.
From mathcomp Require Import ssralg poly finset fingroup action finalg zmodp.
From mathcomp Require Import cyclic ssrnum ssrint archimedean polydiv intdiv.
From mathcomp Require Import mxpoly rat vector falgebra fieldext separable.
From mathcomp Require Import galois algC nilpotent.

(******************************************************************************)
(* This file provides few basic properties of cyclotomic polynomials.         *)
(* We define:                                                                 *)
(*   cyclotomic z n == the factorization of the nth cyclotomic polynomial in  *)
(*                     a ring R in which z is an nth primitive root of unity. *)
(*           'Phi_n == the nth cyclotomic polynomial in int.                  *)
(* This library is quite limited, and should be extended in the future. In    *)
(* particular the irreducibity of 'Phi_n is only stated indirectly, as the    *)
(* fact that its embedding in the algebraics (algC) is the minimal polynomial *)
(* of an nth primitive root of unity.                                         *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section CyclotomicPoly.

Section Ring.

Variable R : ringType.

Definition cyclotomic (z : R) n :=
  \prod_(k < n | coprime k n) ('X - (z ^+ k)%:P).

Lemma cyclotomic_monic z n : cyclotomic z n \is monic.
Proof. exact: monic_prod_XsubC. Qed.

Lemma size_cyclotomic z n : size (cyclotomic z n) = (totient n).+1.
Proof.
rewrite /cyclotomic -big_filter size_prod_XsubC; congr _.+1.
case: big_enumP => _ _ _ [_ ->].
rewrite totient_count_coprime -big_mkcond big_mkord -sum1_card.
by apply: eq_bigl => k; rewrite coprime_sym.
Qed.

End Ring.

Lemma separable_Xn_sub_1 (R : idomainType) n :
  n%:R != 0 :> R -> @separable_poly R ('X^n - 1).
Proof.
case: n => [/eqP// | n nz_n]; rewrite unlock linearB /= derivC subr0.
rewrite derivXn -scaler_nat coprimepZr //= exprS -scaleN1r coprimep_sym.
by rewrite coprimep_addl_mul coprimepZr ?coprimep1 // (signr_eq0 _ 1).
Qed.

Section Field.

Variables (F : fieldType) (n : nat) (z : F).
Hypothesis prim_z : n.-primitive_root z.
Let n_gt0 := prim_order_gt0 prim_z.

Lemma root_cyclotomic x : root (cyclotomic z n) x = n.-primitive_root x.
Proof.
transitivity (x \in [seq z ^+ i | i : 'I_n in [pred i : 'I_n | coprime i n]]).
  by rewrite -root_prod_XsubC big_image.
apply/imageP/idP=> [[k co_k_n ->] | prim_x].
  by rewrite prim_root_exp_coprime.
have [k Dx] := prim_rootP prim_z (prim_expr_order prim_x).
exists (Ordinal (ltn_pmod k n_gt0)) => /=; last by rewrite prim_expr_mod.
by rewrite inE coprime_modl -(prim_root_exp_coprime k prim_z) -Dx.
Qed.

Lemma prod_cyclotomic :
  'X^n - 1 = \prod_(d <- divisors n) cyclotomic (z ^+ (n %/ d)) d.
Proof.
have in_d d: (d %| n)%N -> val (@inord n d) = d by move/dvdn_leq/inordK=> /= ->.
have dv_n k: (n %/ gcdn k n %| n)%N.
  by rewrite -{3}(divnK (dvdn_gcdr k n)) dvdn_mulr.
have [uDn _ inDn] := divisors_correct n_gt0.
have defDn: divisors n = map val (map (@inord n) (divisors n)).
  by rewrite -map_comp map_id_in // => d; rewrite inDn => /in_d.
rewrite defDn big_map big_uniq /=; last first.
  by rewrite -(map_inj_uniq val_inj) -defDn.
pose h (k : 'I_n) : 'I_n.+1 := inord (n %/ gcdn k n).
rewrite -(factor_Xn_sub_1 prim_z) big_mkord.
rewrite (partition_big h (dvdn^~ n)) /= => [|k _]; last by rewrite in_d ?dv_n.
apply: eq_big => d; first by rewrite -(mem_map val_inj) -defDn inDn.
set q := (n %/ d)%N => d_dv_n.
have [q_gt0 d_gt0]: (0 < q /\ 0 < d)%N by apply/andP; rewrite -muln_gt0 divnK.
have fP (k : 'I_d): (q * k < n)%N by rewrite divn_mulAC ?ltn_divLR ?ltn_pmul2l.
rewrite (reindex (fun k => Ordinal (fP k))); last first.
  have f'P (k : 'I_n): (k %/ q < d)%N by rewrite ltn_divLR // mulnC divnK.
  exists (fun k => Ordinal (f'P k)) => [k _ | k /eqnP/=].
    by apply: val_inj; rewrite /= mulKn.
  rewrite in_d // => Dd; apply: val_inj; rewrite /= mulnC divnK // /q -Dd.
  by rewrite divnA ?mulKn ?dvdn_gcdl ?dvdn_gcdr.
apply: eq_big => k; rewrite ?exprM // -val_eqE in_d //=.
rewrite -eqn_mul ?dvdn_gcdr ?gcdn_gt0 ?n_gt0 ?orbT //.
rewrite -[n in gcdn _ n](divnK d_dv_n) -muln_gcdr mulnCA mulnA divnK //.
by rewrite mulnC eqn_mul // divnn n_gt0 eq_sym.
Qed.

End Field.

End CyclotomicPoly.

Local Notation ZtoQ := (intr : int -> rat).
Local Notation ZtoC := (intr : int -> algC).
Local Notation QtoC := (ratr : rat -> algC).

Local Notation intrp := (map_poly intr).
Local Notation pZtoQ := (map_poly ZtoQ).
Local Notation pZtoC := (map_poly ZtoC).
Local Notation pQtoC := (map_poly ratr).

Local Definition algC_intr_inj := @intr_inj algC.
#[local] Hint Resolve algC_intr_inj : core.
Local Notation intCK := (@intrKfloor algC).

Lemma C_prim_root_exists n : (n > 0)%N -> {z : algC | n.-primitive_root z}.
Proof.
pose p : {poly algC} := 'X^n - 1; have [r Dp] := closed_field_poly_normal p.
move=> n_gt0; apply/sigW; rewrite (monicP _) ?monic_Xn_sub_1 // scale1r in Dp.
have rn1: all n.-unity_root r by apply/allP=> z; rewrite -root_prod_XsubC -Dp.
have sz_r: (n < (size r).+1)%N.
  by rewrite -(size_prod_XsubC r id) -Dp size_Xn_sub_1.
have [|z] := hasP (has_prim_root n_gt0 rn1 _ sz_r); last by exists z.
by rewrite -separable_prod_XsubC -Dp separable_Xn_sub_1 // pnatr_eq0 -lt0n.
Qed.

(* (Integral) Cyclotomic polynomials. *)

Definition Cyclotomic n : {poly int} :=
  let: exist z _ := C_prim_root_exists (ltn0Sn n.-1) in
  map_poly Num.floor (cyclotomic z n).

Notation "''Phi_' n" := (Cyclotomic n)
  (at level 8, n at level 2, format "''Phi_' n").

Lemma Cyclotomic_monic n : 'Phi_n \is monic.
Proof.
rewrite /'Phi_n; case: (C_prim_root_exists _) => z /= _.
rewrite monicE lead_coefE coef_map_id0 ?(int_algC_K 0) ?floor0 //.
by rewrite size_poly_eq -lead_coefE (monicP (cyclotomic_monic _ _)) (intCK 1).
Qed.

Lemma Cintr_Cyclotomic n z :
  n.-primitive_root z -> pZtoC 'Phi_n = cyclotomic z n.
Proof.
elim/ltn_ind: n z => n IHn z0 prim_z0.
rewrite /'Phi_n; case: (C_prim_root_exists _) => z /=.
have n_gt0 := prim_order_gt0 prim_z0; rewrite prednK // => prim_z.
have [uDn _ inDn] := divisors_correct n_gt0.
pose q := \prod_(d <- rem n (divisors n)) 'Phi_d.
have mon_q: q \is monic by apply: monic_prod => d _; apply: Cyclotomic_monic.
have defXn1: cyclotomic z n * pZtoC q = 'X^n - 1.
  rewrite (prod_cyclotomic prim_z) (big_rem n) ?inDn //=.
  rewrite divnn n_gt0 rmorph_prod /=; congr (_ * _).
  apply: eq_big_seq => d; rewrite mem_rem_uniq ?inE //= inDn => /andP[n'd ddvn].
  by rewrite -IHn ?dvdn_prim_root // ltn_neqAle n'd dvdn_leq.
have mapXn1 (R1 R2 : ringType) (f : {rmorphism R1 -> R2}):
  map_poly f ('X^n - 1) = 'X^n - 1.
- by rewrite rmorphB /= rmorph1 map_polyXn.
have nz_q: pZtoC q != 0.
  by rewrite -size_poly_eq0 size_map_inj_poly // size_poly_eq0 monic_neq0.
have [r def_zn]: exists r, cyclotomic z n = pZtoC r.
  have defZtoC: ZtoC =1 QtoC \o ZtoQ by move=> a; rewrite /= rmorph_int.
  have /dvdpP[r0 Dr0]: map_poly ZtoQ q %| 'X^n - 1.
    rewrite -(dvdp_map (@ratr algC)) mapXn1 -map_poly_comp.
    by rewrite -(eq_map_poly defZtoC) -defXn1 dvdp_mull.
  have [r [a nz_a Dr]] := rat_poly_scale r0.
  exists (zprimitive r); apply: (mulIf nz_q); rewrite defXn1.
  rewrite -rmorphM -(zprimitive_monic mon_q) -zprimitiveM /=.
  have ->: r * q = a *: ('X^n - 1).
    apply: (map_inj_poly (intr_inj : injective ZtoQ)) => //.
    rewrite map_polyZ mapXn1 Dr0 Dr -scalerAl scalerKV ?intr_eq0 //.
    by rewrite rmorphM.
  by rewrite zprimitiveZ // zprimitive_monic ?monic_Xn_sub_1 ?mapXn1.
rewrite floorpK; last by apply/polyOverP=> i; rewrite def_zn coef_map /=.
pose f e (k : 'I_n) := Ordinal (ltn_pmod (k * e) n_gt0).
have [e Dz0] := prim_rootP prim_z (prim_expr_order prim_z0).
have co_e_n: coprime e n by rewrite -(prim_root_exp_coprime e prim_z) -Dz0.
have injf: injective (f e).
  apply: can_inj (f (egcdn e n).1) _ => k; apply: val_inj => /=.
  rewrite modnMml -mulnA -modnMmr -{1}(mul1n e).
  by rewrite (chinese_modr co_e_n 0) modnMmr muln1 modn_small.
rewrite [_ n](reindex_inj injf); apply: eq_big => k /=.
  by rewrite coprime_modl coprimeMl co_e_n andbT.
by rewrite prim_expr_mod // mulnC exprM -Dz0.
Qed.

Lemma prod_Cyclotomic n :
  (n > 0)%N -> \prod_(d <- divisors n) 'Phi_d = 'X^n - 1.
Proof.
move=> n_gt0; have [z prim_z] := C_prim_root_exists n_gt0.
apply: (map_inj_poly (intr_inj : injective ZtoC)) => //.
rewrite rmorphB rmorph1 rmorph_prod /= map_polyXn (prod_cyclotomic prim_z).
apply: eq_big_seq => d; rewrite -dvdn_divisors // => d_dv_n.
by rewrite -Cintr_Cyclotomic ?dvdn_prim_root.
Qed.

Lemma Cyclotomic0 : 'Phi_0 = 1.
Proof.
rewrite /'Phi_0; case: (C_prim_root_exists _) => z /= _.
by rewrite -[1]polyseqK /cyclotomic big_ord0 map_polyE !polyseq1 /= (intCK 1).
Qed.

Lemma size_Cyclotomic n : size 'Phi_n = (totient n).+1.
Proof.
have [-> | n_gt0] := posnP n; first by rewrite Cyclotomic0 polyseq1.
have [z prim_z] := C_prim_root_exists n_gt0.
rewrite -(size_map_inj_poly (can_inj intCK)) //.
by rewrite (Cintr_Cyclotomic prim_z) size_cyclotomic.
Qed.

Lemma minCpoly_cyclotomic n z :
  n.-primitive_root z -> minCpoly z = cyclotomic z n.
Proof.
move=> prim_z; have n_gt0 := prim_order_gt0 prim_z.
have Dpz := Cintr_Cyclotomic prim_z; set pz := cyclotomic z n in Dpz *.
have mon_pz: pz \is monic by apply: cyclotomic_monic.
have pz0: root pz z by rewrite root_cyclotomic.
have [pf [Dpf mon_pf] dv_pf] := minCpolyP z.
have /dvdpP_rat_int[f [af nz_af Df] [g /esym Dfg]]: pf %| pZtoQ 'Phi_n.
  rewrite -dv_pf; congr (root _ z): pz0; rewrite -Dpz -map_poly_comp.
  by apply: eq_map_poly => b; rewrite /= rmorph_int.
without loss{nz_af} [mon_f mon_g]: af f g Df Dfg / f \is monic /\ g \is monic.
  move=> IH; pose cf := lead_coef f; pose cg := lead_coef g.
  have cfg1: cf * cg = 1.
    by rewrite -lead_coefM Dfg (monicP (Cyclotomic_monic n)).
  apply: (IH (af *~ cf) (f *~ cg) (g *~ cf)).
  - by rewrite rmorphMz -scalerMzr scalerMzl -mulrzA cfg1.
  - by rewrite mulrzAl mulrzAr -mulrzA cfg1.
  by rewrite !(intz, =^~ scaler_int) !monicE !lead_coefZ mulrC cfg1.
have{af} Df: pQtoC pf = pZtoC f.
  have:= congr1 lead_coef Df.
  rewrite lead_coefZ lead_coef_map_inj //; last exact: intr_inj.
  rewrite !(monicP _) // mulr1 Df => <-; rewrite scale1r -map_poly_comp.
  by apply: eq_map_poly => b; rewrite /= rmorph_int.
have [/size1_polyC Dg | g_gt1] := leqP (size g) 1.
  rewrite monicE Dg lead_coefC in mon_g.
  by rewrite -Dpz -Dfg Dg (eqP mon_g) mulr1 Dpf.
have [zk gzk0]: exists zk, root (pZtoC g) zk.
  have [rg] := closed_field_poly_normal (pZtoC g).
  rewrite lead_coef_map_inj // (monicP mon_g) scale1r => Dg.
  rewrite -(size_map_inj_poly (can_inj intCK)) // Dg in g_gt1.
  rewrite size_prod_XsubC in g_gt1.
  by exists rg`_0; rewrite Dg root_prod_XsubC mem_nth.
have [k cokn Dzk]: exists2 k, coprime k n & zk = z ^+ k.
  have: root pz zk by rewrite -Dpz -Dfg rmorphM rootM gzk0 orbT.
  rewrite -[pz](big_image _ _ _ _ (fun r => 'X - r%:P)) root_prod_XsubC.
  by case/imageP=> k; exists k.
have co_fg (R : idomainType): n%:R != 0 :> R -> @coprimep R (intrp f) (intrp g).
  move=> nz_n; have: separable_poly (intrp ('X^n - 1) : {poly R}).
    by rewrite rmorphB rmorph1 /= map_polyXn separable_Xn_sub_1.
  rewrite -prod_Cyclotomic // (big_rem n) -?dvdn_divisors //= -Dfg.
  by rewrite !rmorphM /= !separable_mul => /and3P[] /and3P[].
suffices fzk0: root (pZtoC f) zk.
  have [] // := negP (coprimep_root (co_fg _ _) fzk0).
  by rewrite pnatr_eq0 -lt0n.
move: gzk0 cokn; rewrite {zk}Dzk; elim/ltn_ind: k => k IHk gzk0 cokn.
have [|k_gt1] := leqP k 1; last have [p p_pr /dvdnP[k1 Dk]] := pdivP k_gt1.
  rewrite -[leq k 1](mem_iota 0 2) !inE => /pred2P[k0 | ->]; last first.
    by rewrite -Df dv_pf.
  have /eqP := size_Cyclotomic n; rewrite -Dfg size_Mmonic ?monic_neq0 //.
  rewrite k0 /coprime gcd0n in cokn; rewrite (eqP cokn).
  rewrite -(size_map_inj_poly (can_inj intCK)) // -Df -Dpf.
  by rewrite -(subnKC g_gt1) -(subnKC (size_minCpoly z)) !addnS.
move: cokn; rewrite Dk coprimeMl => /andP[cok1n].
rewrite prime_coprime // (dvdn_charf (char_Fp p_pr)) => /co_fg {co_fg}.
have charFpX: p \in [char {poly 'F_p}] by rewrite (rmorph_char polyC) ?char_Fp.
rewrite -(coprimep_pexpr _ _ (prime_gt0 p_pr)) -(Frobenius_autE charFpX).
rewrite -[g]comp_polyXr map_comp_poly -horner_map /= Frobenius_autE -rmorphXn.
rewrite -!map_poly_comp (@eq_map_poly _ _ _ (polyC \o *~%R 1)); last first.
  by move=> a; rewrite /= !rmorph_int.
rewrite map_poly_comp -[_.[_]]map_comp_poly /= => co_fg.
suffices: coprimep (pZtoC f) (pZtoC (g \Po 'X^p)).
  move/coprimep_root=> /=/(_ (z ^+ k1))/implyP.
  rewrite map_comp_poly map_polyXn horner_comp hornerXn.
  rewrite -exprM -Dk [_ == 0]gzk0 implybF => /negP[].
  have: root pz (z ^+ k1).
    by rewrite root_cyclotomic // prim_root_exp_coprime.
  rewrite -Dpz -Dfg rmorphM rootM => /orP[] //= /IHk-> //.
  rewrite -[k1]muln1 Dk ltn_pmul2l ?prime_gt1 //.
  by have:= ltnW k_gt1; rewrite Dk muln_gt0 => /andP[].
suffices: coprimep f (g \Po 'X^p).
  case/Bezout_coprimepP=> [[u v]]; rewrite -size_poly_eq1.
  rewrite -(size_map_inj_poly (can_inj intCK)) // rmorphD !rmorphM /=.
  rewrite size_poly_eq1 => {}co_fg; apply/Bezout_coprimepP.
  by exists (pZtoC u, pZtoC v).
apply: contraLR co_fg => /coprimepPn[|d]; first exact: monic_neq0.
rewrite andbC -size_poly_eq1 dvdp_gcd => /and3P[sz_d].
pose d1 := zprimitive d.
have d_dv_mon h: d %| h -> h \is monic -> exists h1, h = d1 * h1.
  case/Pdiv.Idomain.dvdpP=> [[c h1] /= nz_c Dh] mon_h; exists (zprimitive h1).
  by rewrite -zprimitiveM mulrC -Dh zprimitiveZ ?zprimitive_monic.
case/d_dv_mon=> // f1 Df1 /d_dv_mon[|f2 ->].
  rewrite monicE lead_coefE size_comp_poly size_polyXn /=.
  rewrite comp_polyE coef_sum polySpred ?monic_neq0 //= mulnC.
  rewrite big_ord_recr /= -lead_coefE (monicP mon_g) scale1r.
  rewrite -exprM coefXn eqxx big1 ?add0r // => i _.
  rewrite coefZ -exprM coefXn eqn_pmul2l ?prime_gt0 //.
  by rewrite eqn_leq leqNgt ltn_ord mulr0.
have monFp h: h \is monic -> size (map_poly intr h) = size h.
  by move=> mon_h; rewrite size_poly_eq // -lead_coefE (monicP mon_h) oner_eq0.
apply/coprimepPn; last exists (map_poly intr d1).
  by rewrite -size_poly_eq0 monFp // size_poly_eq0 monic_neq0.
rewrite Df1 !rmorphM dvdp_gcd !dvdp_mulr //= -size_poly_eq1.
rewrite monFp ?size_zprimitive //.
rewrite monicE [_ d1]intEsg sgz_lead_primitive -zprimitive_eq0 -/d1.
rewrite -lead_coef_eq0 -absz_eq0.
have/esym/eqP := congr1 (absz \o lead_coef) Df1.
by rewrite /= (monicP mon_f) lead_coefM abszM muln_eq1 => /andP[/eqP-> _].
Qed.

Lemma Cyclotomic1 : 'Phi_1 = 'X - 1.
Proof.
by have := @prod_Cyclotomic 1%N isT; rewrite big_cons big_nil mulr1.
Qed.

Lemma Cyclotomic2 : 'Phi_2 = 'X + 1.
Proof.
have := @prod_Cyclotomic 2%N isT; rewrite !big_cons big_nil mulr1/=.
rewrite Cyclotomic1 -(@expr1n [ringType of {poly int}] 2%N).
by rewrite subr_sqr expr1n => /mulfI->//; rewrite polyXsubC_eq0.
Qed.

Lemma prim_root1 (F : fieldType) n : (n.-primitive_root (1 : F)) = (n == 1)%N.
Proof.
case: n => [|[|n]]//.
  by apply/'forall_eqP => i; rewrite ord1//= eqxx; apply/unity_rootP.
apply/'forall_eqP => /= /(_ (@Ordinal _ n _))/=/(_ _)/unity_rootP.
by rewrite !ltnS leqnSn ltn_eqF//; apply => //; rewrite expr1n.
Qed.

Lemma prim2_rootN1 (F : fieldType) : 2%:R != 0 :> F ->
  2.-primitive_root (- 1 : F).
Proof.
move=> tow_neq0; apply/'forall_eqP => -[[|[|]]]//= _; last first.
  by apply/unity_rootP; rewrite -signr_odd.
by apply/unity_rootP/eqP; rewrite expr1 eq_sym -addr_eq0 -mulr2n.
Qed.

Section PhiCyclotomic.

Variable (F : fieldType).

Local Notation ZtoF := (intr : int -> F).
Local Notation pZtoF := (map_poly ZtoF).

Lemma Phi_cyclotomic (n : nat) (w : F) : n.-primitive_root w ->
   pZtoF 'Phi_n = cyclotomic w n.
Proof.
elim/ltn_ind: n w => n ihn w prim_w.
have n_gt0 := prim_order_gt0 prim_w.
pose P k := pZtoF 'Phi_k.
pose Q k := cyclotomic (w ^+ (n %/ k)) k.
have eP : \prod_(d <- divisors n) P d = 'X^n - 1.
  by rewrite -rmorph_prod /= prod_Cyclotomic // rmorphB /= map_polyC map_polyXn.
have eQ : \prod_(d <- divisors n) Q d = 'X^n - 1 by rewrite -prod_cyclotomic.
have fact (u : nat -> {poly F}) : \prod_(d <- divisors n) u d =
              u n * \prod_(d <- rem n (divisors n)) u d.
  by rewrite [LHS](big_rem n) ?divisors_id.
pose p := \prod_(d <- rem n (divisors n)) P d.
pose q := \prod_(d <- rem n (divisors n)) Q d.
have ePp : P n * p = 'X^n - 1 by rewrite -eP fact.
have eQq : Q n * q = 'X^n - 1 by rewrite -eQ fact.
have Xnsub1N0 : 'X^n - 1 != 0 :> {poly F}.
  by rewrite -size_poly_gt0 size_Xn_sub_1.
have pN0 : p != 0 by apply: dvdpN0 Xnsub1N0; rewrite -ePp dvdp_mulIr.
have epq : p = q.
  case: (divisors_correct n_gt0) => uniqd sortedd dP.
  apply: eq_big_seq=> i; rewrite mem_rem_uniq ?divisors_uniq // inE.
  case/andP=> NiSn di; apply: ihn; last by apply: dvdn_prim_root; rewrite -?dP.
  suff: (i <= n)%N by rewrite leq_eqVlt (negPf NiSn).
  by apply: dvdn_leq => //; rewrite -dP.
have {epq} : P n * p = Q n * p by rewrite [in RHS]epq ePp eQq.
by move/(mulIf pN0); rewrite /Q divnn n_gt0.
Qed.

End PhiCyclotomic.

Section CyclotomicExt.

Variables (F0 : fieldType) (L : fieldExtType F0).
Variables (E : {subfield L}) (w : L) (n : nat).
Hypothesis w_is_nth_root : n.-primitive_root w.

Lemma splitting_Fadjoin_cyclotomic :
  splittingFieldFor E (cyclotomic w n) <<E; w>>.
Proof.
exists [seq w ^+ val k | k <- enum 'I_n & coprime (val k) n].
  by rewrite /cyclotomic big_map big_filter big_enum_cond/= eqpxx.
rewrite map_comp -(filter_map _ (fun i => coprime i n)) val_enum_ord.
have [n_gt1|] := ltnP 1 n; last first.
  case: n w_is_nth_root (prim_order_gt0 w_is_nth_root) => [|[|]]//= wnth _ _.
  by rewrite adjoin_seq1 expr0 -[w]expr1 prim_expr_order.
set s := (X in <<_ & X>>%VS); suff /eq_adjoin-> : s =i w :: s.
  rewrite adjoin_cons (Fadjoin_seq_idP _)//.
  by apply/allP => _/mapP[i _ ->]/=; rewrite rpredX// memv_adjoin.
move=> x; rewrite in_cons orbC; symmetry; have []//= := boolP (_ \in _).
apply: contraNF => /eqP ->; rewrite -[w]expr1 map_f//.
by rewrite mem_filter mem_iota// coprime1n.
Qed.

Lemma cyclotomic_over : cyclotomic w n \is a polyOver E.
Proof.
by apply/polyOverP=> i; rewrite -Phi_cyclotomic // coef_map /= rpred_int.
Qed.

Hint Resolve cyclotomic_over : core.

End CyclotomicExt.

Section Cyclotomic.

(* MISSING *)
Lemma primitive_root_pow (F : fieldType) (m : nat) (w w' : F) :
    m.-primitive_root w' -> m.-primitive_root w ->
  exists2 k, coprime k m & w = w' ^+ k.
Proof.
move/root_cyclotomic<-.
rewrite /cyclotomic -big_filter; have [t et [uniqs tP /= perms]] := big_enumP.
pose rs := [seq w' ^+ (val i) | i <- t]; set p := (X in root X).
have {p} -> :  p = \prod_(w <- rs) ('X - w%:P) by rewrite /p big_map.
rewrite root_prod_XsubC; case/mapP=> [[i ltim]]; rewrite tP /= => coprim ew.
by exists i.
Qed.

Variables (F0 : fieldType) (L : splittingFieldType F0).
Variables (E : {subfield L}) (w : L) (n : nat).
Hypothesis w_is_nth_root : n.-primitive_root w.

(** Easy **)
(*     - E(x) is Galois                                                       *)
Lemma galois_Fadjoin_cyclotomic : galois E <<E; w>>.
Proof.
apply/splitting_galoisField; exists (cyclotomic w n).
split; rewrite ?cyclotomic_over//; last exact: splitting_Fadjoin_cyclotomic.
rewrite /cyclotomic -(big_image _ _ _ (fun x => 'X - x%:P))/=.
rewrite separable_prod_XsubC map_inj_uniq ?enum_uniq// => i j /eqP.
by rewrite (eq_prim_root_expr w_is_nth_root) !modn_small// => /eqP/val_inj.
Qed.

Lemma abelian_cyclotomic : abelian 'Gal(<<E; w>> / E)%g.
Proof.
case: (boolP (w \in E)) => [w_in_E |w_notin_E].
  suff -> : ('Gal(<<E; w>> / E) = 1)%g by apply: abelian1.
  apply/eqP; rewrite -subG1; apply/subsetP => x x_in.
  rewrite inE gal_adjoin_eq ?group1 // (fixed_gal _ x_in w_in_E) ?gal_id //.
  by have /Fadjoin_idP H := w_in_E; rewrite -{1}H subvv.
rewrite card_classes_abelian /classes.
apply/eqP; apply: card_in_imset => f g f_in g_in; rewrite -!orbitJ.
move/orbit_eqP/orbitP => [] h h_in <- {f f_in}; apply/eqP.
rewrite gal_adjoin_eq //= /conjg /= ?groupM ?groupV //.
rewrite ?galM ?memv_gal ?memv_adjoin //.
have hg_gal f : f \in 'Gal(<<E; w>> / E)%g -> f w ^+ n = 1.
  by move=> f_in; apply/prim_expr_order; rewrite fmorph_primitive_root.
have := svalP (prim_rootP w_is_nth_root (hg_gal _ g_in)).
have h1_in : (h ^-1)%g \in 'Gal(<<E; w>> / E)%g by rewrite ?groupV.
have := svalP (prim_rootP w_is_nth_root (hg_gal _ h1_in)).
set ih1 := sval _ => hh1; set ig := sval _ => hg.
rewrite hh1 rmorphX /= hg exprAC -hh1 rmorphX /=.
by rewrite -galM ?memv_adjoin // mulVg gal_id.
Qed.

(*     - Gal(E(x) / E) is then solvable                                       *)
Lemma solvable_Fadjoin_cyclotomic : solvable 'Gal(<<E; w>> / E).
Proof. exact/abelian_sol/abelian_cyclotomic. Qed.

End Cyclotomic.
