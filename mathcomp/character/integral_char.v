(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun eqtype ssrnat seq path div choice.
From mathcomp
Require Import fintype tuple finfun bigop prime ssralg poly finset.
From mathcomp
Require Import fingroup morphism perm automorphism quotient action finalg zmodp.
From mathcomp
Require Import commutator cyclic center pgroup sylow gseries nilpotent abelian.
From mathcomp
Require Import ssrnum ssrint polydiv rat matrix mxalgebra intdiv mxpoly.
From mathcomp
Require Import vector falgebra fieldext separable galois algC cyclotomic algnum.
From mathcomp
Require Import mxrepresentation classfun character.

(******************************************************************************)
(* This file provides some standard results based on integrality properties   *)
(* of characters, such as theorem asserting that the degree of an irreducible *)
(* character of G divides the order of G (Isaacs 3.11), or the famous p^a.q^b *)
(* solvability theorem of Burnside.                                           *)
(*   Defined here:                                                            *)
(*    'K_k == the kth class sum in gring F G, where k : 'I_#|classes G|, and  *)
(*            F is inferred from the context.                                 *)
(*            := gset_mx F G (enum_val k) (see mxrepresentation.v).           *)
(* --> The 'K_k form a basis of 'Z(group_ring F G)%MS.                        *)
(*   gring_classM_coef i j k == the coordinate of 'K_i *m 'K_j on 'K_k; this  *)
(*            is usually abbreviated as a i j k.                              *)
(*   gring_classM_coef_set A B z == the set of all (x, y) in setX A B such    *)
(*            that x * y = z; if A and B are respectively the ith and jth     *)
(*            conjugacy class of G, and z is in the kth conjugacy class, then *)
(*            gring_classM_coef i j k is exactly the cardinal of this set.    *)
(*  'omega_i[A] == the mode of 'chi[G]_i on (A \in 'Z(group_ring algC G))%MS, *)
(*            i.e., the z such that gring_op 'Chi_i A  = z%:M.                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Lemma group_num_field_exists (gT : finGroupType) (G : {group gT}) :
  {Qn : splittingFieldType rat & galois 1 {:Qn} &
    {QnC : {rmorphism Qn -> algC}
         & forall nuQn : argumentType (mem ('Gal({:Qn}%VS / 1%VS))),
              {nu : {rmorphism algC -> algC} |
                 {morph QnC: a / nuQn a >-> nu a}}
         & {w : Qn & #|G|.-primitive_root w /\ <<1; w>>%VS = fullv
              & forall (hT : finGroupType) (H : {group hT}) (phi : 'CF(H)),
                       phi \is a character ->
                       forall x, (#[x] %| #|G|)%N -> {a | QnC a = phi x}}}}.
Proof.
have [z prim_z] := C_prim_root_exists (cardG_gt0 G); set n := #|G| in prim_z *.
have [Qn [QnC [[|w []] // [Dz] genQn]]] := num_field_exists [:: z].
have prim_w: n.-primitive_root w by rewrite -Dz fmorph_primitive_root in prim_z.
have Q_Xn1: ('X^n - 1 : {poly Qn}) \is a polyOver 1%AS.
  by rewrite rpredB ?rpred1 ?rpredX //= polyOverX.
have splitXn1: splittingFieldFor 1 ('X^n - 1) {:Qn}.
  pose r := codom (fun i : 'I_n => w ^+ i).
  have Dr: 'X^n - 1 = \prod_(y <- r) ('X - y%:P).
    by rewrite -(factor_Xn_sub_1 prim_w) big_mkord big_map enumT.
  exists r; first by rewrite -Dr eqpxx.
  apply/eqP; rewrite eqEsubv subvf -genQn adjoin_seqSr //; apply/allP=> /=.
  by rewrite andbT -root_prod_XsubC -Dr; apply/unity_rootP/prim_expr_order.
have Qn_ax : SplittingField.axiom Qn by exists ('X^n - 1).
exists (SplittingFieldType _ _ Qn_ax).
  apply/splitting_galoisField.
  exists ('X^n - 1); split => //.
  apply: separable_Xn_sub_1; rewrite -(fmorph_eq0 QnC) rmorph_nat.
  by rewrite pnatr_eq0 -lt0n cardG_gt0.
exists QnC => [// nuQn|].
  by apply: (extend_algC_subfield_aut QnC [rmorphism of nuQn]).
rewrite span_seq1 in genQn.
exists w => // hT H phi Nphi x x_dv_n.
apply: sig_eqW; have [rH ->] := char_reprP Nphi.
have [Hx | /cfun0->] := boolP (x \in H); last by exists 0; rewrite rmorph0.
have [e [_ [enx1 _] [-> _] _]] := repr_rsim_diag rH Hx.
have /fin_all_exists[k Dk] i: exists k, e 0 i = z ^+ k.
  have [|k ->] := (prim_rootP prim_z) (e 0 i); last by exists k.
  by have /dvdnP[q ->] := x_dv_n; rewrite mulnC exprM enx1 expr1n.
exists (\sum_i w ^+ k i); rewrite rmorph_sum; apply/eq_bigr => i _.
by rewrite rmorphX Dz Dk.
Qed.

Section GenericClassSums.

(* This is Isaacs, Theorem (2.4), generalized to an arbitrary field, and with *)
(* the combinatorial definition of the coeficients exposed.                   *)
(* This part could move to mxrepresentation.*)

Variable (gT : finGroupType) (G : {group gT}) (F : fieldType).

Definition gring_classM_coef_set (Ki Kj : {set gT}) g :=
  [set xy in [predX Ki & Kj] | let: (x, y) := xy in x * y == g]%g.

Definition gring_classM_coef (i j k : 'I_#|classes G|) :=
  #|gring_classM_coef_set (enum_val i) (enum_val j) (repr (enum_val k))|.

Definition gring_class_sum (i : 'I_#|classes G|) := gset_mx F G (enum_val i).

Local Notation "''K_' i" := (gring_class_sum i)
  (at level 8, i at level 2, format "''K_' i") : ring_scope.
Local Notation a := gring_classM_coef.

Lemma gring_class_sum_central i : ('K_i \in 'Z(group_ring F G))%MS.
Proof. by rewrite -classg_base_center (eq_row_sub i) // rowK. Qed.

Lemma set_gring_classM_coef (i j k : 'I_#|classes G|) g :
    g \in enum_val k ->
  a i j k = #|gring_classM_coef_set (enum_val i) (enum_val j) g|.
Proof.
rewrite /a; have /repr_classesP[] := enum_valP k; move: (repr _) => g1 Gg1 ->.
have [/imsetP[zi Gzi ->] /imsetP[zj Gzj ->]] := (enum_valP i, enum_valP j).
move=> g1Gg; have Gg := subsetP (class_subG Gg1 (subxx _)) _ g1Gg.
set Aij := gring_classM_coef_set _ _.
without loss suffices IH: g g1 Gg Gg1 g1Gg / (#|Aij g1| <= #|Aij g|)%N.
  by apply/eqP; rewrite eqn_leq !IH // class_sym.
have [w Gw Dg] := imsetP g1Gg; pose J2 (v : gT) xy := (xy.1 ^ v, xy.2 ^ v)%g.
have J2inj: injective (J2 w).
  by apply: can_inj (J2 w^-1)%g _ => [[x y]]; rewrite /J2 /= !conjgK.
rewrite -(card_imset _ J2inj) subset_leq_card //; apply/subsetP.
move=> _ /imsetP[[x y] /setIdP[/andP[/= x1Gx y1Gy] Dxy1] ->]; rewrite !inE /=.
rewrite !(class_sym _ (_ ^ _)) !classGidl // class_sym x1Gx class_sym y1Gy.
by rewrite -conjMg (eqP Dxy1) /= -Dg.
Qed.

Theorem gring_classM_expansion i j : 'K_i *m 'K_j = \sum_k (a i j k)%:R *: 'K_k.
Proof.
have [/imsetP[zi Gzi dKi] /imsetP[zj Gzj dKj]] := (enum_valP i, enum_valP j).
pose aG := regular_repr F G; have sKG := subsetP (class_subG _ (subxx G)).
transitivity (\sum_(x in zi ^: G) \sum_(y in zj ^: G) aG (x * y)%g).
  rewrite mulmx_suml -/aG dKi; apply: eq_bigr => x /sKG Gx.
  rewrite mulmx_sumr -/aG dKj; apply: eq_bigr => y /sKG Gy.
  by rewrite repr_mxM ?Gx ?Gy.
pose h2 xy : gT := (xy.1 * xy.2)%g.
pose h1 xy := enum_rank_in (classes1 G) (h2 xy ^: G).
rewrite pair_big (partition_big h1 xpredT) //=; apply: eq_bigr => k _.
rewrite (partition_big h2 (mem (enum_val k))) /= => [|[x y]]; last first.
  case/andP=> /andP[/= /sKG Gx /sKG Gy] /eqP <-.
  by rewrite enum_rankK_in ?class_refl ?mem_classes ?groupM ?Gx ?Gy.
rewrite scaler_sumr; apply: eq_bigr => g Kk_g; rewrite scaler_nat.
rewrite (set_gring_classM_coef _ _ Kk_g) -sumr_const; apply: eq_big => [] [x y].
  rewrite !inE /= dKi dKj /h1 /h2 /=; apply: andb_id2r => /eqP ->.
  have /imsetP[zk Gzk dKk] := enum_valP k; rewrite dKk in Kk_g.
  by rewrite (class_eqP Kk_g) -dKk enum_valK_in eqxx andbT.
by rewrite /h2 /= => /andP[_ /eqP->].
Qed.

Fact gring_irr_mode_key : unit. Proof. by []. Qed.
Definition gring_irr_mode_def (i : Iirr G) := ('chi_i 1%g)^-1 *: 'chi_i.
Definition gring_irr_mode := locked_with gring_irr_mode_key gring_irr_mode_def.
Canonical gring_irr_mode_unlockable := [unlockable fun gring_irr_mode].

End GenericClassSums.

Arguments gring_irr_mode {gT G%G} i%R _%g : extra scopes.

Notation "''K_' i" := (gring_class_sum _ i)
  (at level 8, i at level 2, format "''K_' i") : ring_scope.

Notation "''omega_' i [ A ]" := (xcfun (gring_irr_mode i) A)
   (at level 8, i at level 2, format "''omega_' i [ A ]") : ring_scope.

Section IntegralChar.

Variables (gT : finGroupType) (G : {group gT}).

(* This is Isaacs, Corollary (3.6). *)
Lemma Aint_char (chi : 'CF(G)) x : chi \is a character -> chi x \in Aint.
Proof.
have [Gx /char_reprP[rG ->] {chi} | /cfun0->//] := boolP (x \in G).
have [e [_ [unit_e _] [-> _] _]] := repr_rsim_diag rG Gx.
rewrite rpred_sum // => i _; apply: (@Aint_unity_root #[x]) => //.
exact/unity_rootP.
Qed.

Lemma Aint_irr i x : 'chi[G]_i x \in Aint.
Proof. exact/Aint_char/irr_char. Qed.

Local Notation R_G := (group_ring algCfield G).
Local Notation a := gring_classM_coef.

(* This is Isaacs (2.25). *)
Lemma mx_irr_gring_op_center_scalar n (rG : mx_representation algCfield G n) A :
  mx_irreducible rG -> (A \in 'Z(R_G))%MS -> is_scalar_mx (gring_op rG A).
Proof.
move/groupC=> irrG /center_mxP[R_A cGA].
apply: mx_abs_irr_cent_scalar irrG _ _; apply/centgmxP => x Gx.
by rewrite -(gring_opG rG Gx) -!gring_opM ?cGA // envelop_mx_id.
Qed.

Section GringIrrMode.

Variable i : Iirr G.

Let n := irr_degree (socle_of_Iirr i).
Let mxZn_inj: injective (@scalar_mx algCfield n).
Proof. by rewrite -[n]prednK ?irr_degree_gt0 //; apply: fmorph_inj. Qed.

Lemma cfRepr_gring_center n1 (rG : mx_representation algCfield G n1) A :
  cfRepr rG = 'chi_i -> (A \in 'Z(R_G))%MS -> gring_op rG A = 'omega_i[A]%:M.
Proof.
move=> def_rG Z_A; rewrite unlock xcfunZl -{2}def_rG xcfun_repr.
have irr_rG: mx_irreducible rG.
  have sim_rG: mx_rsim 'Chi_i rG by apply: cfRepr_inj; rewrite irrRepr.
  exact: mx_rsim_irr sim_rG (socle_irr _).
have /is_scalar_mxP[e ->] := mx_irr_gring_op_center_scalar irr_rG Z_A.
congr _%:M; apply: (canRL (mulKf (irr1_neq0 i))).
by rewrite mulrC -def_rG cfunE repr_mx1 group1 -mxtraceZ scalemx1.
Qed.

Lemma irr_gring_center A :
  (A \in 'Z(R_G))%MS -> gring_op 'Chi_i A = 'omega_i[A]%:M.
Proof. exact: cfRepr_gring_center (irrRepr i). Qed.

Lemma gring_irr_modeM A B :
    (A \in 'Z(R_G))%MS -> (B \in 'Z(R_G))%MS ->
  'omega_i[A *m B] = 'omega_i[A] * 'omega_i[B].
Proof.
move=> Z_A Z_B; have [[R_A cRA] [R_B cRB]] := (center_mxP Z_A, center_mxP Z_B).
apply: mxZn_inj; rewrite scalar_mxM -!irr_gring_center ?gring_opM //.
apply/center_mxP; split=> [|C R_C]; first exact: envelop_mxM.
by rewrite mulmxA cRA // -!mulmxA cRB.
Qed.

Lemma gring_mode_class_sum_eq (k : 'I_#|classes G|) g :
  g \in enum_val k -> 'omega_i['K_k] = #|g ^: G|%:R * 'chi_i g / 'chi_i 1%g.
Proof.
have /imsetP[x Gx DxG] := enum_valP k; rewrite DxG => /imsetP[u Gu ->{g}].
rewrite unlock classGidl ?cfunJ {u Gu}// mulrC mulr_natl.
rewrite xcfunZl raddf_sum DxG -sumr_const /=; congr (_ * _).
by apply: eq_bigr => _ /imsetP[u Gu ->]; rewrite xcfunG ?groupJ ?cfunJ.
Qed.

(* This is Isaacs, Theorem (3.7). *)
Lemma Aint_gring_mode_class_sum k : 'omega_i['K_k] \in Aint.
Proof.
move: k; pose X := [tuple 'omega_i['K_k] | k < #|classes G| ].
have memX k: 'omega_i['K_k] \in X by apply: image_f.
have S_P := Cint_spanP X; set S := Cint_span X in S_P.
have S_X: {subset X <= S} by apply: mem_Cint_span.
have S_1: 1 \in S.
  apply: S_X; apply/codomP; exists (enum_rank_in (classes1 G) 1%g).
  rewrite (@gring_mode_class_sum_eq _ 1%g) ?enum_rankK_in ?classes1 //.
  by rewrite mulfK ?irr1_neq0 // class1G cards1.
suffices Smul: mulr_closed S.
  by move=> k; apply: fin_Csubring_Aint S_P _ _; rewrite ?S_X.
split=> // _ _ /S_P[x ->] /S_P[y ->].
rewrite mulr_sumr rpred_sum // => j _.
rewrite mulrzAr mulr_suml rpredMz ?rpred_sum // => k _.
rewrite mulrzAl rpredMz {x y}// !nth_mktuple.
rewrite -gring_irr_modeM ?gring_class_sum_central //.
rewrite gring_classM_expansion raddf_sum rpred_sum // => jk _.
by rewrite scaler_nat raddfMn rpredMn ?S_X ?memX.
Qed.

(* A more usable reformulation that does not involve the class sums. *)
Corollary Aint_class_div_irr1 x :
  x \in G -> #|x ^: G|%:R * 'chi_i x / 'chi_i 1%g \in Aint.
Proof.
move=> Gx; have clGxG := mem_classes Gx; pose k := enum_rank_in clGxG (x ^: G).
have k_x: x \in enum_val k by rewrite enum_rankK_in // class_refl.
by rewrite -(gring_mode_class_sum_eq k_x) Aint_gring_mode_class_sum.
Qed.

(* This is Isaacs, Theorem (3.8). *)
Theorem coprime_degree_support_cfcenter g :
    coprime (truncC ('chi_i 1%g)) #|g ^: G| -> g \notin ('Z('chi_i))%CF ->
  'chi_i g = 0.
Proof.
set m := truncC _ => co_m_gG notZg.
have [Gg | /cfun0-> //] := boolP (g \in G).
have Dm: 'chi_i 1%g = m%:R by rewrite truncCK ?Cnat_irr1.
have m_gt0: (0 < m)%N by rewrite -ltC_nat -Dm irr1_gt0.
have nz_m: m%:R != 0 :> algC by rewrite pnatr_eq0 -lt0n.
pose alpha := 'chi_i g / m%:R.
have a_lt1: `|alpha| < 1.
  rewrite normrM normfV normr_nat -{2}(divff nz_m).
  rewrite ltr_def (can_eq (mulfVK nz_m)) eq_sym -{1}Dm -irr_cfcenterE // notZg.
  by rewrite ler_pmul2r ?invr_gt0 ?ltr0n // -Dm char1_ge_norm ?irr_char.
have Za: alpha \in Aint.
  have [u _ /dvdnP[v eq_uv]] := Bezoutl #|g ^: G| m_gt0.
  suffices ->: alpha = v%:R * 'chi_i g - u%:R * (alpha * #|g ^: G|%:R).
    rewrite rpredB // rpredM ?rpred_nat ?Aint_irr //.
    by rewrite mulrC mulrA -Dm Aint_class_div_irr1.
  rewrite -mulrCA -[v%:R](mulfK nz_m) -!natrM -eq_uv (eqnP co_m_gG).
  by rewrite mulrAC -mulrA -/alpha mulr_natl mulr_natr mulrS addrK.
have [Qn galQn [QnC gQnC [_ _ Qn_g]]] := group_num_field_exists <[g]>.
have{Qn_g} [a Da]: exists a, QnC a = alpha.
  rewrite /alpha; have [a <-] := Qn_g _ G _ (irr_char i) g (dvdnn _).
  by exists (a / m%:R); rewrite fmorph_div rmorph_nat.
have Za_nu nu: sval (gQnC nu) alpha \in Aint by rewrite Aint_aut.
have norm_a_nu nu: `|sval (gQnC nu) alpha| <= 1.
  move: {nu}(sval _) => nu; rewrite fmorph_div rmorph_nat normrM normfV.
  rewrite normr_nat -Dm -(ler_pmul2r (irr1_gt0 (aut_Iirr nu i))) mul1r.
  congr (_ <= _): (char1_ge_norm g (irr_char (aut_Iirr nu i))).
  by rewrite !aut_IirrE !cfunE Dm rmorph_nat divfK.
pose beta := QnC (galNorm 1 {:Qn} a).
have Dbeta: beta = \prod_(nu in 'Gal({:Qn} / 1)) sval (gQnC nu) alpha.
  rewrite /beta rmorph_prod. apply: eq_bigr => nu _.
  by case: (gQnC nu) => f /= ->; rewrite Da.
have Zbeta: beta \in Cint.
  apply: Cint_rat_Aint; last by rewrite Dbeta rpred_prod.
  rewrite /beta; have /vlineP[/= c ->] := mem_galNorm galQn (memvf a).
  by rewrite alg_num_field fmorph_rat rpred_rat.
have [|nz_a] := boolP (alpha == 0).
  by rewrite (can2_eq (divfK _) (mulfK _)) // mul0r => /eqP.
have: beta != 0 by rewrite Dbeta; apply/prodf_neq0 => nu _; rewrite fmorph_eq0.
move/(norm_Cint_ge1 Zbeta); rewrite ltr_geF //; apply: ler_lt_trans a_lt1.
rewrite -[`|alpha|]mulr1 Dbeta (bigD1 1%g) ?group1 //= -Da.
case: (gQnC _) => /= _ <-; rewrite gal_id normrM.
rewrite -subr_ge0 -mulrBr mulr_ge0 ?normr_ge0 // Da subr_ge0.
elim/big_rec: _ => [|nu c _]; first by rewrite normr1 lerr.
apply: ler_trans; rewrite -subr_ge0 -{1}[`|c|]mul1r normrM -mulrBl.
by rewrite mulr_ge0 ?normr_ge0 // subr_ge0 norm_a_nu.
Qed.

End GringIrrMode.

(* This is Isaacs, Theorem (3.9). *)
Theorem primes_class_simple_gt1 C :
  simple G -> ~~ abelian G -> C \in (classes G)^# -> (size (primes #|C|) > 1)%N.
Proof.
move=> simpleG not_cGG /setD1P[ntC /imsetP[g Gg defC]].
have{ntC} nt_g: g != 1%g by rewrite defC classG_eq1 in ntC.
rewrite ltnNge {C}defC; set m := #|_|; apply/negP=> p_natC.
have{p_natC} [p p_pr [a Dm]]: {p : nat & prime p & {a | m = p ^ a}%N}.
  have /prod_prime_decomp->: (0 < m)%N by rewrite /m -index_cent1.
  rewrite prime_decompE; case Dpr: (primes _) p_natC => [|p []] // _.
    by exists 2 => //; rewrite big_nil; exists 0%N.
  rewrite big_seq1; exists p; last by exists (logn p m).
  by have:= mem_primes p m; rewrite Dpr mem_head => /esym/and3P[].
have{simpleG} [ntG minG] := simpleP _ simpleG.
pose p_dv1 i := (p %| 'chi[G]_i 1%g)%C.
have p_dvd_supp_g i: ~~ p_dv1 i && (i != 0) -> 'chi_i g = 0.
  rewrite /p_dv1 irr1_degree dvdC_nat -prime_coprime // => /andP[co_p_i1 nz_i].
  have fful_i: cfker 'chi_i = [1].
    have /minG[//|/eqP] := cfker_normal 'chi_i.
    by rewrite eqEsubset subGcfker (negPf nz_i) andbF.
  have trivZ: 'Z(G) = [1] by have /minG[|/center_idP/idPn] := center_normal G.
  have trivZi: ('Z('chi_i))%CF = [1].
    apply/trivgP; rewrite -quotient_sub1 ?norms1 //= -fful_i cfcenter_eq_center.
    rewrite fful_i subG1 -(isog_eq1 (isog_center (quotient1_isog G))) /=.
    by rewrite trivZ.
  rewrite coprime_degree_support_cfcenter ?trivZi ?inE //.
  by rewrite -/m Dm irr1_degree natCK coprime_sym coprime_expl.
pose alpha := \sum_(i | p_dv1 i && (i != 0)) 'chi_i 1%g / p%:R * 'chi_i g.
have nz_p: p%:R != 0 :> algC by rewrite pnatr_eq0 -lt0n prime_gt0.
have Dalpha: alpha = - 1 / p%:R.
  apply/(canRL (mulfK nz_p))/eqP; rewrite -addr_eq0 addrC; apply/eqP/esym.
  transitivity (cfReg G g); first by rewrite cfRegE (negPf nt_g).
  rewrite cfReg_sum sum_cfunE (bigD1 0) //= irr0 !cfunE cfun11 cfun1E Gg.
  rewrite mulr1; congr (1 + _); rewrite (bigID p_dv1) /= addrC big_andbC.
  rewrite big1 => [|i /p_dvd_supp_g chig0]; last by rewrite cfunE chig0 mulr0.
  rewrite add0r big_andbC mulr_suml; apply: eq_bigr => i _.
  by rewrite mulrAC divfK // cfunE.
suffices: (p %| 1)%C by rewrite (dvdC_nat p 1) dvdn1 -(subnKC (prime_gt1 p_pr)).
rewrite unfold_in (negPf nz_p).
rewrite Cint_rat_Aint ?rpred_div ?rpred1 ?rpred_nat //.
rewrite -rpredN // -mulNr -Dalpha rpred_sum // => i /andP[/dvdCP[c Zc ->] _].
by rewrite mulfK // rpredM ?Aint_irr ?Aint_Cint.
Qed.

End IntegralChar.

Section MoreIntegralChar.

Implicit Type gT : finGroupType.

(* This is Burnside's famous p^a.q^b theorem (Isaacs, Theorem (3.10)). *)
Theorem Burnside_p_a_q_b gT (G : {group gT}) :
  (size (primes #|G|) <= 2)%N -> solvable G.
Proof.
move: {2}_.+1 (ltnSn #|G|) => n; elim: n => // n IHn in gT G *.
rewrite ltnS => leGn piGle2; have [simpleG | ] := boolP (simple G); last first.
  rewrite negb_forall_in => /exists_inP[N sNG]; rewrite eq_sym.
  have [-> | ] := altP (N =P G).
    rewrite groupP /= genGid normG andbT eqb_id negbK => /eqP->.
    exact: solvable1.
  rewrite [N == G]eqEproper sNG eqbF_neg !negbK => ltNG /and3P[grN].
  case/isgroupP: grN => {N}N -> in sNG ltNG *; rewrite /= genGid => ntN nNG.
  have nsNG: N <| G by apply/andP.
  have dv_le_pi m: (m %| #|G| -> size (primes m) <= 2)%N.
    move=> m_dv_G; apply: leq_trans piGle2.
    by rewrite uniq_leq_size ?primes_uniq //; apply: pi_of_dvd.
  rewrite (series_sol nsNG) !IHn ?dv_le_pi ?cardSg ?dvdn_quotient //.
    by apply: leq_trans leGn; apply: ltn_quotient.
  by apply: leq_trans leGn; apply: proper_card.
have [->|[p p_pr p_dv_G]] := trivgVpdiv G; first exact: solvable1.
have piGp: p \in \pi(G) by rewrite mem_primes p_pr cardG_gt0.
have [P sylP] := Sylow_exists p G; have [sPG pP p'GP] := and3P sylP.
have ntP: P :!=: 1%g by rewrite -rank_gt0 (rank_Sylow sylP) p_rank_gt0.
have /trivgPn[g /setIP[Pg cPg] nt_g]: 'Z(P) != 1%g.
  by rewrite center_nil_eq1 // (pgroup_nil pP).
apply: abelian_sol; have: (size (primes #|g ^: G|) <= 1)%N.
  rewrite -ltnS -[_.+1]/(size (p :: _)) (leq_trans _ piGle2) //.
  rewrite -index_cent1 uniq_leq_size // => [/= | q].
    rewrite primes_uniq -p'natEpi ?(pnat_dvd _ p'GP) ?indexgS //.
    by rewrite subsetI sPG sub_cent1.
  by rewrite inE => /predU1P[-> // |]; apply: pi_of_dvd; rewrite ?dvdn_indexg.
rewrite leqNgt; apply: contraR => /primes_class_simple_gt1-> //.
by rewrite !inE classG_eq1 nt_g mem_classes // (subsetP sPG).
Qed.

(* This is Isaacs, Theorem (3.11). *)
Theorem dvd_irr1_cardG gT (G : {group gT}) i : ('chi[G]_i 1%g %| #|G|)%C.
Proof.
rewrite unfold_in -if_neg irr1_neq0 Cint_rat_Aint //=.
  by rewrite rpred_div ?rpred_nat // rpred_Cnat ?Cnat_irr1.
rewrite -[n in n / _]/(_ *+ true) -(eqxx i) -mulr_natr.
rewrite -first_orthogonality_relation mulVKf ?neq0CG //.
rewrite sum_by_classes => [|x y Gx Gy]; rewrite -?conjVg ?cfunJ //.
rewrite mulr_suml rpred_sum // => K /repr_classesP[Gx {1}->].
by rewrite !mulrA mulrAC rpredM ?Aint_irr ?Aint_class_div_irr1.
Qed.

(* This is Isaacs, Theorem (3.12). *)
Theorem dvd_irr1_index_center gT (G : {group gT}) i :
  ('chi[G]_i 1%g %| #|G : 'Z('chi_i)%CF|)%C.
Proof.
without loss fful: gT G i / cfaithful 'chi_i.
  rewrite -{2}[i](quo_IirrK _ (subxx _)) ?mod_IirrE ?cfModE ?cfker_normal //.
  rewrite morph1; set i1 := quo_Iirr _ i => /(_ _ _ i1) IH.
  have fful_i1: cfaithful 'chi_i1.
    by rewrite quo_IirrE ?cfker_normal ?cfaithful_quo.
  have:= IH fful_i1; rewrite cfcenter_fful_irr // -cfcenter_eq_center.
  rewrite index_quotient_eq ?cfcenter_sub ?cfker_norm //.
  by rewrite setIC subIset // normal_sub ?cfker_center_normal.
have [lambda lin_lambda Dlambda] := cfcenter_Res 'chi_i.
have DchiZ: {in G & 'Z(G), forall x y, 'chi_i (x * y)%g = 'chi_i x * lambda y}.
  rewrite -(cfcenter_fful_irr fful) => x y Gx Zy.
  apply: (mulfI (irr1_neq0 i)); rewrite mulrCA.
  transitivity ('chi_i x * ('chi_i 1%g *: lambda) y); last by rewrite !cfunE.
  rewrite -Dlambda cfResE ?cfcenter_sub //.
  rewrite -irrRepr cfcenter_repr !cfunE in Zy *.
  case/setIdP: Zy => Gy /is_scalar_mxP[e De].
  rewrite repr_mx1 group1 (groupM Gx Gy) (repr_mxM _ Gx Gy) Gx Gy De.
  by rewrite mul_mx_scalar mxtraceZ mulrCA mulrA mulrC -mxtraceZ scalemx1.
have inj_lambda: {in 'Z(G) &, injective lambda}.
  rewrite -(cfcenter_fful_irr fful) => x y Zx Zy eq_xy.
  apply/eqP; rewrite eq_mulVg1 -in_set1 (subsetP fful) // cfkerEirr inE.
  apply/eqP; transitivity ('Res['Z('chi_i)%CF] 'chi_i (x^-1 * y)%g).
    by rewrite cfResE ?cfcenter_sub // groupM ?groupV.
  rewrite Dlambda !cfunE lin_charM ?groupV // -eq_xy -lin_charM ?groupV //.
  by rewrite mulrC mulVg lin_char1 ?mul1r.
rewrite unfold_in -if_neg irr1_neq0 Cint_rat_Aint //.
  by rewrite rpred_div ?rpred_nat // rpred_Cnat ?Cnat_irr1.
rewrite (cfcenter_fful_irr fful) nCdivE natf_indexg ?center_sub //=.
have ->: #|G|%:R = \sum_(x in G) 'chi_i x * 'chi_i (x^-1)%g.
  rewrite -[_%:R]mulr1; apply: canLR (mulVKf (neq0CG G)) _.
  by rewrite first_orthogonality_relation eqxx.
rewrite (big_setID [set x | 'chi_i x == 0]) /= -setIdE.
rewrite big1 ?add0r => [| x /setIdP[_ /eqP->]]; last by rewrite mul0r.
pose h x := (x ^: G * 'Z(G))%g; rewrite (partition_big_imset h).
rewrite !mulr_suml rpred_sum //= => _ /imsetP[x /setDP[Gx nz_chi_x] ->].
have: #|x ^: G|%:R * ('chi_i x * 'chi_i x^-1%g) / 'chi_i 1%g \in Aint.
  by rewrite !mulrA mulrAC rpredM ?Aint_irr ?Aint_class_div_irr1.
congr 2 (_ * _ \in Aint); apply: canRL (mulfK (neq0CG _)) _.
rewrite inE in nz_chi_x.
transitivity ('chi_i x * 'chi_i (x^-1)%g *+ #|h x|); last first.
  rewrite -sumr_const.
  apply: eq_big => [y | _ /mulsgP[_ z /imsetP[u Gu ->] Zz] ->].
    rewrite !inE -andbA; apply/idP/and3P=> [|[_ _ /eqP <-]]; last first.
      by rewrite -{1}[y]mulg1 mem_mulg ?class_refl.
    case/mulsgP=> _ z /imsetP[u Gu ->] Zz ->; have /centerP[Gz cGz] := Zz.
    rewrite groupM 1?DchiZ ?groupJ ?cfunJ //; split=> //.
      by rewrite mulf_neq0 // lin_char_neq0 /= ?cfcenter_fful_irr.
    rewrite -[z](mulKg u) -cGz // -conjMg /h classGidl {u Gu}//.
    apply/eqP/setP=> w; apply/mulsgP/mulsgP=> [][_ z1 /imsetP[v Gv ->] Zz1 ->].
      exists (x ^ v)%g (z * z1)%g; rewrite ?mem_imset ?groupM //.
      by rewrite conjMg -mulgA /(z ^ v)%g cGz // mulKg.
    exists ((x * z) ^ v)%g (z^-1 * z1)%g; rewrite ?mem_imset ?groupM ?groupV //.
    by rewrite conjMg -mulgA /(z ^ v)%g cGz // mulKg mulKVg.
  rewrite !irr_inv DchiZ ?groupJ ?cfunJ // rmorphM mulrACA -!normCK -exprMn.
  by rewrite (normC_lin_char lin_lambda) ?mulr1 //= cfcenter_fful_irr.
rewrite mulrAC -natrM mulr_natl; congr (_ *+ _).
symmetry; rewrite /h /mulg /= /set_mulg [in _ @2: (_, _)]unlock cardsE.
rewrite -cardX card_in_image // => [] [y1 z1] [y2 z2] /=.
move=> /andP[/=/imsetP[u1 Gu1 ->] Zz1] /andP[/=/imsetP[u2 Gu2 ->] Zz2] {y1 y2}.
move=> eq12; have /eqP := congr1 'chi_i eq12.
rewrite !(cfunJ, DchiZ) ?groupJ // (can_eq (mulKf nz_chi_x)).
rewrite (inj_in_eq inj_lambda) // => /eqP eq_z12; rewrite eq_z12 in eq12 *.
by rewrite (mulIg _ _ _ eq12).
Qed.

(* This is Isaacs, Problem (3.7). *)
Lemma gring_classM_coef_sum_eq gT (G : {group gT}) j1 j2 k g1 g2 g :
   let a := @gring_classM_coef gT G j1 j2 in let a_k := a k in
   g1 \in enum_val j1 -> g2 \in enum_val j2 -> g \in enum_val k ->
   let sum12g := \sum_i 'chi[G]_i g1 * 'chi_i g2 * ('chi_i g)^* / 'chi_i 1%g in
  a_k%:R = (#|enum_val j1| * #|enum_val j2|)%:R / #|G|%:R * sum12g.
Proof.
move=> a /= Kg1 Kg2 Kg; rewrite mulrAC; apply: canRL (mulfK (neq0CG G)) _.
transitivity (\sum_j (#|G| * a j)%:R *+ (j == k) : algC).
  by rewrite (bigD1 k) //= eqxx -natrM mulnC big1 ?addr0 // => j /negPf->.
have defK (j : 'I_#|classes G|) x: x \in enum_val j -> enum_val j = x ^: G.
  by have /imsetP[y Gy ->] := enum_valP j => /class_eqP.
have Gg: g \in G.
  by case/imsetP: (enum_valP k) Kg => x Gx -> /imsetP[y Gy ->]; apply: groupJ.
transitivity (\sum_j \sum_i 'omega_i['K_j] * 'chi_i 1%g * ('chi_i g)^* *+ a j).
  apply: eq_bigr => j _; have /imsetP[z Gz Dj] := enum_valP j.
  have Kz: z \in enum_val j by rewrite Dj class_refl.
  rewrite -(Lagrange (subsetIl G 'C[z])) index_cent1 -mulnA natrM -mulrnAl.
  have ->: (j == k) = (z \in enum_val k).
    by rewrite -(inj_eq enum_val_inj); apply/eqP/idP=> [<-|/defK->].
  rewrite (defK _ g) // -second_orthogonality_relation // mulr_suml.
  apply: eq_bigr=> i _; rewrite natrM mulrA mulr_natr mulrC mulrA.
  by rewrite (gring_mode_class_sum_eq i Kz) divfK ?irr1_neq0.
rewrite exchange_big /= mulr_sumr; apply: eq_bigr => i _.
transitivity ('omega_i['K_j1 *m 'K_j2] * 'chi_i 1%g * ('chi_i g)^*).
  rewrite gring_classM_expansion -/a raddf_sum !mulr_suml /=.
  by apply: eq_bigr => j _; rewrite xcfunZr -!mulrA mulr_natl.
rewrite !mulrA 2![_ / _]mulrAC (defK _ _ Kg1) (defK _ _ Kg2); congr (_ * _).
rewrite gring_irr_modeM ?gring_class_sum_central // mulnC natrM.
rewrite (gring_mode_class_sum_eq i Kg2) !mulrA divfK ?irr1_neq0 //.
by congr (_ * _); rewrite [_ * _]mulrC (gring_mode_class_sum_eq i Kg1) !mulrA.
Qed.

(* This is Isaacs, Problem (2.16). *)
Lemma index_support_dvd_degree gT (G H : {group gT}) chi :
    H \subset G -> chi \is a character -> chi \in 'CF(G, H) ->
    (H :==: 1%g) || abelian G ->
  (#|G : H| %| chi 1%g)%C.
Proof.
move=> sHG Nchi Hchi ZHG.
suffices: (#|G : H| %| 'Res[H] chi 1%g)%C by rewrite cfResE ?group1.
rewrite ['Res _]cfun_sum_cfdot sum_cfunE rpred_sum // => i _.
rewrite cfunE dvdC_mulr ?Cint_Cnat ?Cnat_irr1 //.
have [j ->]: exists j, 'chi_i = 'Res 'chi[G]_j.
  case/predU1P: ZHG => [-> | cGG] in i *.
    suffices ->: i = 0 by exists 0; rewrite !irr0 cfRes_cfun1 ?sub1G.
    apply/val_inj; case: i => [[|i] //=]; rewrite ltnNge NirrE.
    by rewrite (@leq_trans 1) // leqNgt classes_gt1 eqxx.
  have linG := char_abelianP G cGG; have linG1 j := eqP (proj2 (andP (linG j))).
  have /fin_all_exists[rH DrH] j: exists k, 'Res[H, G] 'chi_j = 'chi_k.
    apply/irrP/lin_char_irr/andP.
    by rewrite cfRes_char ?irr_char // cfRes1 ?linG1.
  suffices{i} all_rH: codom rH =i Iirr H.
    by exists (iinv (all_rH i)); rewrite DrH f_iinv.
  apply/subset_cardP; last exact/subsetP; apply/esym/eqP.
  rewrite card_Iirr_abelian ?(abelianS sHG) //.
  rewrite -(eqn_pmul2r (indexg_gt0 G H)) Lagrange //; apply/eqP.
  rewrite -sum_nat_const -card_Iirr_abelian // -sum1_card.
  rewrite (partition_big rH (mem (codom rH))) /=; last exact: image_f.
  have nsHG: H <| G by rewrite -sub_abelian_normal.
  apply: eq_bigr => _ /codomP[i ->]; rewrite -card_quotient ?normal_norm //.
  rewrite -card_Iirr_abelian ?quotient_abelian //.
  have Mlin j1 j2: exists k, 'chi_j1 * 'chi_j2 = 'chi[G]_k.
    exact/irrP/lin_char_irr/rpredM.
  have /fin_all_exists[rQ DrQ] (j : Iirr (G / H)) := Mlin i (mod_Iirr j).
  have mulJi: ('chi[G]_i)^*%CF * 'chi_i = 1.
    apply/cfun_inP=> x Gx; rewrite !cfunE -lin_charV_conj ?linG // cfun1E Gx.
    by rewrite lin_charV ?mulVf ?lin_char_neq0 ?linG.
  have inj_rQ: injective rQ.
    move=> j1 j2 /(congr1 (fun k => (('chi_i)^*%CF * 'chi_k) / H)%CF).
    by rewrite -!DrQ !mulrA mulJi !mul1r !mod_IirrE ?cfModK // => /irr_inj.
  rewrite -(card_imset _ inj_rQ) -sum1_card; apply: eq_bigl => j.
  rewrite -(inj_eq irr_inj) -!DrH; apply/eqP/imsetP=> [eq_ij | [k _ ->]].
    have [k Dk] := Mlin (conjC_Iirr i) j; exists (quo_Iirr H k) => //.
    apply/irr_inj; rewrite -DrQ quo_IirrK //.
      by rewrite -Dk conjC_IirrE mulrCA mulrA mulJi mul1r.
    apply/subsetP=> x Hx; have Gx := subsetP sHG x Hx.
    rewrite cfkerEirr inE linG1 -Dk conjC_IirrE; apply/eqP.
    transitivity ((1 : 'CF(G)) x); last by rewrite cfun1E Gx.
    by rewrite -mulJi !cfunE -!(cfResE _ sHG Hx) eq_ij.
  rewrite -DrQ; apply/cfun_inP=> x Hx; rewrite !cfResE // cfunE mulrC.
  by rewrite cfker1 ?linG1 ?mul1r ?(subsetP _ x Hx) // mod_IirrE ?cfker_mod.
have: (#|G : H| %| #|G : H|%:R * '[chi, 'chi_j])%C.
  by rewrite dvdC_mulr ?Cint_Cnat ?Cnat_cfdot_char_irr.
congr (_ %| _)%C; rewrite (cfdotEl _ Hchi) -(Lagrange sHG) mulnC natrM.
rewrite invfM -mulrA mulVKf ?neq0CiG //; congr (_ * _).
by apply: eq_bigr => x Hx; rewrite !cfResE.
Qed.

(* This is Isaacs, Theorem (3.13). *)
Theorem faithful_degree_p_part gT (p : nat) (G P : {group gT}) i :
    cfaithful 'chi[G]_i -> p.-nat (truncC ('chi_i 1%g)) ->
    p.-Sylow(G) P -> abelian P ->
  'chi_i 1%g = (#|G : 'Z(G)|`_p)%:R.
Proof.
have [p_pr | pr'p] := boolP (prime p); last first.
  have p'n n: (n > 0)%N -> p^'.-nat n.
    by move/p'natEpi->; rewrite mem_primes (negPf pr'p).
  rewrite irr1_degree natCK => _ /pnat_1-> => [_ _|].
    by rewrite part_p'nat ?p'n.
  by rewrite p'n ?irr_degree_gt0.
move=> fful_i /p_natP[a Dchi1] sylP cPP.
have Dchi1C: 'chi_i 1%g = (p ^ a)%:R by rewrite -Dchi1 irr1_degree natCK.
have pa_dv_ZiG: (p ^ a %| #|G : 'Z(G)|)%N.
  rewrite -dvdC_nat -[pa in (pa %| _)%C]Dchi1C -(cfcenter_fful_irr fful_i).
  exact: dvd_irr1_index_center.
have [sPG pP p'PiG] := and3P sylP.
have ZchiP: 'Res[P] 'chi_i \in 'CF(P, P :&: 'Z(G)).
  apply/cfun_onP=> x; rewrite inE; have [Px | /cfun0->//] := boolP (x \in P).
  rewrite /= -(cfcenter_fful_irr fful_i) cfResE //.
  apply: coprime_degree_support_cfcenter.
  rewrite Dchi1 coprime_expl // prime_coprime // -p'natE //.
  apply: pnat_dvd p'PiG; rewrite -index_cent1 indexgS // subsetI sPG.
  by rewrite sub_cent1 (subsetP cPP).
have /andP[_ nZG] := center_normal G; have nZP := subset_trans sPG nZG.
apply/eqP; rewrite Dchi1C eqr_nat eqn_dvd -{1}(pfactorK a p_pr) -p_part.
rewrite partn_dvd //= -dvdC_nat -[pa in (_ %| pa)%C]Dchi1C -card_quotient //=.
rewrite -(card_Hall (quotient_pHall nZP sylP)) card_quotient // -indexgI.
rewrite -(cfResE _ sPG) // index_support_dvd_degree ?subsetIl ?cPP ?orbT //.
by rewrite cfRes_char ?irr_char.
Qed.

(* This is Isaacs, Lemma (3.14). *)
(* Note that the assumption that G be cyclic is unnecessary, as S will be     *)
(* empty if this is not the case.                                             *)
Lemma sum_norm2_char_generators gT (G : {group gT}) (chi : 'CF(G)) :
    let S := [pred s | generator G s] in
    chi \is a character -> {in S, forall s, chi s != 0} ->
  \sum_(s in S) `|chi s| ^+ 2 >= #|S|%:R.
Proof.
move=> S Nchi nz_chi_S; pose n := #|G|.
have [g Sg | S_0] := pickP (generator G); last first.
  by rewrite eq_card0 // big_pred0 ?lerr.
have defG: <[g]> = G by apply/esym/eqP.
have [cycG Gg]: cyclic G /\ g \in G by rewrite -defG cycle_cyclic cycle_id.
pose I := {k : 'I_n | coprime n k}; pose ItoS (k : I) := (g ^+ sval k)%g.
have imItoS: codom ItoS =i S.
  move=> s; rewrite inE /= /ItoS /I /n /S -defG -orderE.
  apply/codomP/idP=> [[[i cogi] ->] | Ss]; first by rewrite generator_coprime.
  have [m ltmg Ds] := cyclePmin (cycle_generator Ss).
  by rewrite Ds generator_coprime in Ss; apply: ex_intro (Sub (Sub m _) _) _.
have /injectiveP injItoS: injective ItoS.
  move=> k1 k2 /eqP; apply: contraTeq.
  by rewrite eq_expg_mod_order orderE defG -/n !modn_small.
have [Qn galQn [QnC gQnC [eps [pr_eps defQn] QnG]]] := group_num_field_exists G.
have{QnG} QnGg := QnG _ G _ _ g (order_dvdG Gg).
pose calG := 'Gal({:Qn} / 1).
have /fin_all_exists2[ItoQ inItoQ defItoQ] (k : I):
  exists2 nu, nu \in calG & nu eps = eps ^+ val k.
- case: k => [[m _] /=]; rewrite coprime_sym => /Qn_aut_exists[nuC DnuC].
  have [nuQ DnuQ] := restrict_aut_to_normal_num_field QnC nuC.
  have hom_nu: kHom 1 {:Qn} (linfun nuQ).
    rewrite k1HomE; apply/ahom_inP.
    by split=> [u v | ]; rewrite !lfunE ?rmorphM ?rmorph1.
  have [|nu cGnu Dnu] := kHom_to_gal _ (normalFieldf 1) hom_nu.
    by rewrite !subvf.
  exists nu => //; apply: (fmorph_inj QnC).
  rewrite -Dnu ?memvf // lfunE DnuQ rmorphX DnuC //.
  by rewrite prim_expr_order // fmorph_primitive_root.
have{defQn} imItoQ: calG = ItoQ @: {:I}.
  apply/setP=> nu; apply/idP/imsetP=> [cGnu | [k _ ->] //].
  have pr_nu_e: n.-primitive_root (nu eps) by rewrite fmorph_primitive_root.
  have [i Dnue] := prim_rootP pr_eps (prim_expr_order pr_nu_e).
  rewrite Dnue prim_root_exp_coprime // coprime_sym in pr_nu_e.
  apply: ex_intro2 (Sub i _) _ _ => //; apply/eqP.
  rewrite /calG /= -defQn in ItoQ inItoQ defItoQ nu cGnu Dnue *.
  by rewrite gal_adjoin_eq // defItoQ -Dnue.
have injItoQ: {in {:I} &, injective ItoQ}.
  move=> k1 k2 _ _ /(congr1 (fun nu : gal_of _ => nu eps))/eqP.
  by apply: contraTeq; rewrite !defItoQ (eq_prim_root_expr pr_eps) !modn_small.
pose pi1 := \prod_(s in S) chi s; pose pi2 := \prod_(s in S) `|chi s| ^+ 2.
have Qpi1: pi1 \in Crat.
  have [a Da] := QnGg _ Nchi; suffices ->: pi1 = QnC (galNorm 1 {:Qn} a).
    have /vlineP[q ->] := mem_galNorm galQn (memvf a).
    by rewrite rmorphZ_num rmorph1 mulr1 Crat_rat.
  rewrite /galNorm rmorph_prod -/calG imItoQ big_imset //=.
  rewrite /pi1 -(eq_bigl _ _ imItoS) -big_uniq // big_map big_filter /=.
  apply: eq_bigr => k _; have [nuC DnuC] := gQnC (ItoQ k); rewrite DnuC Da.
  have [r ->] := char_sum_irr Nchi; rewrite !sum_cfunE rmorph_sum.
  apply: eq_bigr => i _; have /QnGg[b Db] := irr_char i.
  have Lchi_i: 'chi_i \is a linear_char by rewrite irr_cyclic_lin.
  have /(prim_rootP pr_eps)[m Dem]: b ^+ n = 1.
    apply/eqP; rewrite -(fmorph_eq1 QnC) rmorphX Db -lin_charX //.
    by rewrite -expg_mod_order orderE defG modnn lin_char1.
  rewrite -Db -DnuC Dem rmorphX /= defItoQ exprAC -{m}Dem rmorphX {b}Db.
  by rewrite lin_charX.
clear I ItoS imItoS injItoS ItoQ inItoQ defItoQ imItoQ injItoQ.
clear Qn galQn QnC gQnC eps pr_eps QnGg calG.
have{Qpi1} Zpi1: pi1 \in Cint.
  by rewrite Cint_rat_Aint // rpred_prod // => s _; apply: Aint_char.
have{pi1 Zpi1} pi2_ge1: 1 <= pi2.
  have ->: pi2 = `|pi1| ^+ 2.
    by rewrite (big_morph Num.norm (@normrM _) (@normr1 _)) -prodrXl.
  by rewrite Cint_normK // sqr_Cint_ge1 //; apply/prodf_neq0.
have Sgt0: (#|S| > 0)%N by rewrite (cardD1 g) [g \in S]Sg.
rewrite -mulr_natr -ler_pdivl_mulr ?ltr0n //.
have n2chi_ge0 s: s \in S -> 0 <= `|chi s| ^+ 2 by rewrite exprn_ge0 ?normr_ge0.
rewrite -(expr_ge1 Sgt0); last by rewrite divr_ge0 ?ler0n ?sumr_ge0.
by rewrite (ler_trans pi2_ge1) // lerif_AGM.
Qed.

(* This is Burnside's vanishing theorem (Isaacs, Theorem (3.15)). *)
Theorem nonlinear_irr_vanish gT (G : {group gT}) i :
  'chi[G]_i 1%g > 1 -> exists2 x, x \in G & 'chi_i x = 0.
Proof.
move=> chi1gt1; apply/exists_eq_inP; apply: contraFT (ltr_geF chi1gt1).
rewrite negb_exists_in => /forall_inP-nz_chi.
rewrite -(norm_Cnat (Cnat_irr1 i)) -(@expr_le1 _ 2) ?normr_ge0 //.
rewrite -(ler_add2r (#|G|%:R * '['chi_i])) {1}cfnorm_irr mulr1.
rewrite (cfnormE (cfun_onG _)) mulVKf ?neq0CG // (big_setD1 1%g) //=.
rewrite addrCA ler_add2l (cardsD1 1%g) group1 mulrS ler_add2l.
rewrite -sumr_const !(partition_big_imset (fun s => <[s]>)) /=.
apply: ler_sum => _ /imsetP[g /setD1P[ntg Gg] ->].
have sgG: <[g]> \subset G by rewrite cycle_subG.
pose S := [pred s | generator <[g]> s]; pose chi := 'Res[<[g]>] 'chi_i.
have defS: [pred s in G^# | <[s]> == <[g]>] =i S.
  move=> s; rewrite inE /= eq_sym andb_idl // !inE -cycle_eq1 -cycle_subG.
  by move/eqP <-; rewrite cycle_eq1 ntg.
have resS: {in S, 'chi_i =1 chi}.
  by move=> s /cycle_generator=> g_s; rewrite cfResE ?cycle_subG.
rewrite !(eq_bigl _ _ defS) sumr_const.
rewrite (eq_bigr (fun s => `|chi s| ^+ 2)) => [|s /resS-> //].
apply: sum_norm2_char_generators => [|s Ss].
  by rewrite cfRes_char ?irr_char.
by rewrite -resS // nz_chi ?(subsetP sgG) ?cycle_generator.
Qed.

End MoreIntegralChar.