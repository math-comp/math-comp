(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
Require Import fingroup morphism perm automorphism quotient action zmodp.
Require Import gfunctor gproduct cyclic pgroup frobenius ssrnum.
Require Import matrix mxalgebra mxrepresentation vector algC classfun character.
Require Import inertia vcharacter PFsection1.

(******************************************************************************)
(* This file covers Peterfalvi, Section 2: the Dade isometry                  *)
(* Defined here:                                                              *)
(*   Dade_hypothesis G L A <-> G, L, and A satisfy the hypotheses under which *)
(*                               which the Dade isometry relative to G, L and *)
(*                               A is well-defined.                           *)
(* For ddA : Dade_hypothesis G L A, we also define                            *)
(*              Dade ddA == the Dade isometry relative to G, L and A.         *)
(* Dade_signalizer ddA a == the normal complement to 'C_L[a] in 'C_G[a] for   *)
(*                          a in A (this is usually denoted by H a).          *)
(*   Dade_support1 ddA a == the set of elements identified with a by the Dade *)
(*                         isometry.                                          *)
(*      Dade_support ddA == the natural support of the Dade isometry.         *)
(* The following are used locally in expansion of the Dade isometry as a sum  *)
(* of induced characters:                                                     *)
(*         Dade_transversal ddA == a transversal of the L-conjugacy classes   *)
(*                                 of non empty subsets of A.                 *)
(*    Dade_set_signalizer ddA B == the generalization of H to B \subset A,    *)
(*                                 denoted 'H(B) below.                       *)
(*    Dade_set_normalizer ddA B == the generalization of 'C_G[a] to B.        *)
(*                                 denoted 'M(B) = 'H(B) ><| 'N_L(B) below.   *)
(*    Dade_cfun_restriction ddA B aa == the composition of aa \in 'CF(L, A)   *)
(*                                 with the projection of 'M(B) onto 'N_L(B), *)
(*                                 parallel to 'H(B).                         *)
(* In addition, if sA1A : A1 \subset A and nA1L : L \subset 'N(A1), we have   *)
(*  restr_Dade_hyp ddA sA1A nA1L : Dade_hypothesis G L A1 H                   *)
(*      restr_Dade ddA sA1A nA1L == the restriction of the Dade isometry to   *)
(*                                  'CF(L, A1).                               *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Reserved Notation "alpha ^\tau" (at level 2, format "alpha ^\tau").

Section Two.

Variable gT : finGroupType.

(* This is Peterfalvi (2.1). *)
Lemma partition_cent_rcoset (H : {group gT}) g (C := 'C_H[g]) (Cg := C :* g) :
    g \in 'N(H) -> coprime #|H| #[g] ->
  partition (Cg :^: H) (H :* g) /\ #|Cg :^: H| = #|H : C|.
Proof.
move=> nHg coHg; pose pi := \pi(#[g]).
have notCg0: Cg != set0 by apply/set0Pn; exists g; exact: rcoset_refl.
have id_pi: {in Cg, forall u, u.`_ pi = g}.
  move=> _ /rcosetP[u /setIP[Hu cgu] ->]; rewrite consttM; last exact/cent1P.
  rewrite (constt_p_elt (pgroup_pi _)) (constt1P _) ?mul1g //.
  by rewrite (mem_p_elt _ Hu) // /pgroup -coprime_pi' // coprime_sym.
have{id_pi} /and3P[_ tiCg /eqP defC]: normedTI Cg H C.
  apply/normedTI_P; rewrite subsetI subsetIl normsM ?normG ?subsetIr //.
  split=> // x Hx /pred0Pn[u /andP[/= Cu Cxu]]; rewrite !inE Hx /= conjg_set1.
  by rewrite -{2}(id_pi _ Cu) -(conjgKV x u) consttJ id_pi -?mem_conjg.
have{tiCg} partCg := partition_class_support notCg0 tiCg.
have{defC} oCgH: #|Cg :^: H| = #|H : C| by rewrite -defC -astab1Js -card_orbit.
split=> //; congr (partition _ _): (partCg); apply/eqP.
rewrite eqEcard card_rcoset {1}class_supportEr; apply/andP; split.
  apply/bigcupsP=> x Hx; rewrite conjsgE -rcosetM conjgCV rcosetM mulgA.
  by rewrite mulSg ?mul_subG ?subsetIl // sub1set ?memJ_norm ?groupV.
have oCg Cx: Cx \in Cg :^: H -> #|Cx| = #|C|.
  by case/imsetP=> x _ ->; rewrite cardJg card_rcoset.
by rewrite (card_uniform_partition oCg partCg) oCgH mulnC Lagrange ?subsetIl.
Qed.

Definition is_Dade_signalizer (G L A : {set gT}) (H : gT -> {group gT}) :=
  {in A, forall a, H a ><| 'C_L[a] = 'C_G[a]}.

(* This is Peterfalvi Definition (2.2). *)
Definition Dade_hypothesis (G L A : {set gT}) :=
  [/\ A <| L, L \subset G, 1%g \notin A,
   (*a*) {in A &, forall x, {subset x ^: G <= x ^: L}}
 & (*b*) exists2 H, is_Dade_signalizer G L A H
 & (*c*) {in A &, forall a b, coprime #|H a| #|'C_L[b]| }].

Variables (G L : {group gT}) (A : {set gT}).

Let pi := [pred p | [exists a in A, p \in \pi('C_L[a])]].

Let piCL a : a \in A -> pi.-group 'C_L[a].
Proof.
move=> Aa; apply: sub_pgroup (pgroup_pi _) => p cLa_p.
by apply/exists_inP; exists a.
Qed.

Fact Dade_signalizer_key : unit. Proof. by []. Qed.
Definition Dade_signalizer_def a := 'O_pi^'('C_G[a])%G.
Definition Dade_signalizer of Dade_hypothesis G L A :=
  locked_with Dade_signalizer_key Dade_signalizer_def.

Hypothesis ddA : Dade_hypothesis G L A.
Notation H := (Dade_signalizer ddA).
Canonical Dade_signalizer_unlockable := [unlockable fun H].

Let pi'H a : pi^'.-group (H a). Proof. by rewrite unlock pcore_pgroup. Qed.
Let nsHC a : H a <| 'C_G[a]. Proof. by rewrite unlock pcore_normal. Qed.

Lemma Dade_signalizer_sub a : H a \subset G.
Proof. by have /andP[/subsetIP[]] := nsHC a. Qed.

Lemma Dade_signalizer_cent a : H a \subset 'C[a].
Proof. by have /andP[/subsetIP[]] := nsHC a. Qed.

Let nsAL : A <| L. Proof. by have [->] := ddA. Qed.
Let sAL : A \subset L. Proof. exact: normal_sub nsAL. Qed.
Let nAL : L \subset 'N(A). Proof. exact: normal_norm nsAL. Qed.
Let sLG : L \subset G. Proof. by have [_ ->] := ddA. Qed.
Let notA1 : 1%g \notin A. Proof. by have [_ _ ->] := ddA. Qed.
Let conjAG : {in A &, forall x, {subset x ^: G <= x ^: L}}.
Proof. by have [_ _ _ ? _] := ddA. Qed.
Let sHG := Dade_signalizer_sub.
Let cHA := Dade_signalizer_cent.
Let notHa0 a : H a :* a :!=: set0.
Proof. by rewrite -cards_eq0 -lt0n card_rcoset cardG_gt0. Qed.

Let HallCL a : a \in A -> pi.-Hall('C_G[a]) 'C_L[a].
Proof.
move=> Aa; have [_ _ _ _ [H1 /(_ a Aa)/sdprodP[_ defCa _ _] coH1L]] := ddA.
have [|//] := coprime_mulGp_Hall defCa _ (piCL Aa).
apply: sub_pgroup (pgroup_pi _) => p; apply: contraL => /exists_inP[b Ab].
by apply: (@pnatPpi \pi(_)^'); rewrite -coprime_pi' ?cardG_gt0 ?coH1L.
Qed.

Lemma def_Dade_signalizer H1 : is_Dade_signalizer G L A H1 -> {in A, H =1 H1}.
Proof.
move=> defH1 a Aa; apply/val_inj; rewrite unlock /=; have defCa := defH1 a Aa.
have /sdprod_context[nsH1Ca _ _ _ _] := defCa.
by apply/normal_Hall_pcore=> //; apply/(sdprod_normal_pHallP _ (HallCL Aa)).
Qed.

Lemma Dade_sdprod : is_Dade_signalizer G L A H.
Proof.
move=> a Aa; have [_ _ _ _ [H1 defH1 _]] := ddA.
by rewrite (def_Dade_signalizer defH1) ?defH1.
Qed.
Let defCA := Dade_sdprod.

Lemma Dade_coprime : {in A &, forall a b, coprime #|H a| #|'C_L[b]| }.
Proof. by move=> a b _ Ab; apply: p'nat_coprime (pi'H a) (piCL Ab). Qed.
Let coHL := Dade_coprime.

Definition Dade_support1 a := class_support (H a :* a) G.
Local Notation dd1 := Dade_support1.

Lemma mem_Dade_support1 a x : a \in A -> x \in H a -> (x * a)%g \in dd1 a.
Proof. by move=> Aa Hx; rewrite -(conjg1 (x * a)) !mem_imset2 ?set11. Qed.

(* This is Peterfalvi (2.3), except for the existence part, which is covered  *)
(* below in the NormedTI section.                                             *)
Lemma Dade_normedTI_P :
  reflect (A != set0 /\ {in A, forall a, H a = 1%G}) (normedTI A G L).
Proof.
apply: (iffP idP) => [tiAG | [nzA trivH]].
  split=> [|a Aa]; first by have [] := andP tiAG.
  apply/trivGP; rewrite -(coprime_TIg (coHL Aa Aa)) subsetIidl subsetI cHA.
  by rewrite (subset_trans (normal_sub (nsHC a))) ?(cent1_normedTI tiAG).
apply/normedTI_memJ_P; split=> // a g Aa Gg.
apply/idP/idP=> [Aag | Lg]; last by rewrite memJ_norm ?(subsetP nAL).
have /imsetP[k Lk def_ag] := conjAG Aa Aag (mem_imset _ Gg).
suffices: (g * k^-1)%g \in 'C_G[a].
  by rewrite -Dade_sdprod ?trivH // sdprod1g inE groupMr ?groupV // => /andP[].
rewrite !inE groupM ?groupV // ?(subsetP sLG) //=.
by rewrite conjg_set1 conjgM def_ag conjgK.
Qed.

(* This is Peterfalvi (2.4)(a) (extended to all a thanks to our choice of H). *)
Lemma DadeJ a x : x \in L -> H (a ^ x) :=: H a :^ x.
Proof.
by move/(subsetP sLG)=> Gx; rewrite unlock -pcoreJ conjIg -cent1J conjGid.
Qed.

Lemma Dade_support1_id a x : x \in L -> dd1 (a ^ x) = dd1 a.
Proof.
move=> Lx; rewrite {1}/dd1 DadeJ // -conjg_set1 -conjsMg.
by rewrite class_supportGidl ?(subsetP sLG).
Qed.

Let piHA a u : a \in A -> u \in H a :* a -> u.`_pi = a.
Proof.
move=> Aa /rcosetP[{u}u Hu ->]; have pi'u: pi^'.-elt u by apply: mem_p_elt Hu.
rewrite (consttM _ (cent1P (subsetP (cHA a) u Hu))).
suffices pi_a: pi.-elt a by rewrite (constt1P pi'u) (constt_p_elt _) ?mul1g.
by rewrite (mem_p_elt (piCL Aa)) // inE cent1id (subsetP sAL).
Qed.

(* This is Peterfalvi (2.4)(b). *)
Lemma Dade_support1_TI : {in A &, forall a b,
  ~~ [disjoint dd1 a & dd1 b] -> exists2 x, x \in L & b = a ^ x}.
Proof.
move=> a b Aa Ab /= /pred0Pn[_ /andP[/imset2P[x u /(piHA Aa) def_x Gu ->]]] /=.
case/imset2P=> y v /(piHA Ab) def_y Gv /(canLR (conjgK v)) def_xuv.
have def_b: a ^ (u * v^-1) = b by rewrite -def_x -consttJ conjgM def_xuv def_y.
by apply/imsetP/conjAG; rewrite // -def_b mem_imset ?groupM ?groupV.
Qed.

(* This is an essential strengthening of Peterfalvi (2.4)(c). *)
Lemma Dade_cover_TI : {in A, forall a, normedTI (H a :* a) G 'C_G[a]}.
Proof.
move=> a Aa; apply/normedTI_P; split=> // [|g Gg].
  by rewrite subsetI subsetIl normsM ?subsetIr ?normal_norm ?nsHC.
rewrite disjoint_sym => /pred0Pn[_ /andP[/imsetP[u Ha_u ->] Ha_ug]].
by rewrite !inE Gg /= conjg_set1 -{1}(piHA Aa Ha_u) -consttJ (piHA Aa).
Qed.

(* This is Peterfalvi (2.4)(c). *)
Lemma norm_Dade_cover : {in A, forall a, 'N_G(H a :* a) = 'C_G[a]}.
Proof. by move=> a /Dade_cover_TI /and3P[_ _ /eqP]. Qed.

Definition Dade_support := \bigcup_(a in A) dd1 a.
Local Notation Atau := Dade_support.

Lemma not_support_Dade_1 : 1%g \notin Atau.
Proof.
apply: contra notA1 => /bigcupP[a Aa /imset2P[u x Ha_u _ ux1]].
suffices /set1P <-: a \in [1] by [].
have [_ _ _ <-] := sdprodP (defCA Aa).
rewrite 2!inE cent1id (subsetP sAL) // !andbT.
by rewrite -groupV -(mul1g a^-1)%g -mem_rcoset -(conj1g x^-1) ux1 conjgK.
Qed.

Lemma Dade_support_sub : Atau \subset G.
Proof.
apply/bigcupsP=> a Aa; rewrite class_support_subG // mul_subG ?sHG //.
by rewrite sub1set (subsetP sLG) ?(subsetP sAL).
Qed.

Lemma Dade_support_norm : G \subset 'N(Atau).
Proof.
by rewrite norms_bigcup //; apply/bigcapsP=> a _; exact: class_support_norm.
Qed.

Lemma Dade_support_normal : Atau <| G.
Proof. by rewrite /normal Dade_support_sub Dade_support_norm. Qed.

Lemma Dade_support_subD1 : Atau \subset G^#.
Proof. by rewrite subsetD1 Dade_support_sub not_support_Dade_1. Qed.

(* This is Peterfalvi Definition (2.5). *)
Fact Dade_subproof (alpha : 'CF(L)) :
  is_class_fun <<G>> [ffun x => oapp alpha 0 [pick a in A | x \in dd1 a]].
Proof.
rewrite genGid; apply: intro_class_fun => [x y Gx Gy | x notGx].
  congr (oapp _ _); apply: eq_pick => a; rewrite memJ_norm //.
  apply: subsetP Gy; exact: class_support_norm.
case: pickP => // a /andP[Aa Ha_u].
by rewrite (subsetP Dade_support_sub) // in notGx; apply/bigcupP; exists a.
Qed.
Definition Dade alpha := Cfun 1 (Dade_subproof alpha).

Lemma Dade_is_linear : linear Dade.
Proof.
move=> mu alpha beta; apply/cfunP=> x; rewrite !cfunElock.
by case: pickP => [a _ | _] /=; rewrite ?mulr0 ?addr0 ?cfunE.
Qed.
Canonical Dade_additive := Additive Dade_is_linear.
Canonical Dade_linear := Linear Dade_is_linear.

Local Notation "alpha ^\tau" := (Dade alpha).

(* This is the validity of Peterfalvi, Definition (2.5) *)
Lemma DadeE alpha a u : a \in A -> u \in dd1 a -> alpha^\tau u = alpha a.
Proof.
move=> Aa Ha_u; rewrite cfunElock.
have [b /= /andP[Ab Hb_u] | ] := pickP; last by move/(_ a); rewrite Aa Ha_u.
have [|x Lx ->] := Dade_support1_TI Aa Ab; last by rewrite cfunJ.
by apply/pred0Pn; exists u; rewrite /= Ha_u.
Qed.

Lemma Dade_id alpha : {in A, forall a, alpha^\tau a = alpha a}.
Proof.
by move=> a Aa; rewrite /= -{1}[a]mul1g (DadeE _ Aa) ?mem_Dade_support1.
Qed.

Lemma Dade_cfunS alpha : alpha^\tau \in 'CF(G, Atau).
Proof.
apply/cfun_onP=> x; rewrite cfunElock.
by case: pickP => [a /andP[Aa Ha_x] /bigcupP[] | //]; exists a.
Qed.

Lemma Dade_cfun alpha : alpha^\tau \in 'CF(G, G^#).
Proof. by rewrite (cfun_onS Dade_support_subD1) ?Dade_cfunS. Qed.

Lemma Dade1 alpha : alpha^\tau 1%g = 0.
Proof. by rewrite (cfun_on0 (Dade_cfun _)) // !inE eqxx. Qed.

Lemma Dade_id1 :
  {in 'CF(L, A) & 1%g |: A, forall alpha a, alpha^\tau a = alpha a}.
Proof.
move=> alpha a Aalpha; case/setU1P=> [-> |]; last exact: Dade_id.
by rewrite Dade1 (cfun_on0 Aalpha).
Qed.

Section AutomorphismCFun.

Variable u : {rmorphism algC -> algC}.
Local Notation "alpha ^u" := (cfAut u alpha).

Lemma Dade_aut alpha : (alpha^u)^\tau = (alpha^\tau)^u. 
Proof.
apply/cfunP => g; rewrite cfunE.
have [/bigcupP[a Aa A1g] | notAtau_g] := boolP (g \in Atau).
  by rewrite !(DadeE _ Aa A1g) cfunE.
by rewrite !(cfun_on0 _ notAtau_g) ?rmorph0 ?Dade_cfunS.
Qed.

End AutomorphismCFun.

Lemma Dade_conjC alpha : (alpha^*)^\tau = ((alpha^\tau)^*)%CF. 
Proof. exact: Dade_aut. Qed.

(* This is Peterfalvi (2.7), main part *)
Lemma general_Dade_reciprocity alpha (phi : 'CF(G)) (psi : 'CF(L)) :
    alpha \in 'CF(L, A) ->
  {in A, forall a, psi a = #|H a|%:R ^-1 * (\sum_(x in H a) phi (x * a)%g)} ->
  '[alpha^\tau, phi] = '[alpha, psi].
Proof.
move=> CFalpha psiA; rewrite (cfdotEl _ (Dade_cfunS _)).
pose T := [set repr (a ^: L) | a in A].
have sTA: {subset T <= A}.
  move=> _ /imsetP[a Aa ->]; have [x Lx ->] := repr_class L a.
  by rewrite memJ_norm ?(subsetP nAL).
pose P_G := [set dd1 x | x in T].
have dd1_id: {in A, forall a, dd1 (repr (a ^: L)) = dd1 a}.
  by move=> a Aa /=; have [x Lx ->] := repr_class L a; apply: Dade_support1_id.
have ->: Atau = cover P_G.
  apply/setP=> u; apply/bigcupP/bigcupP=> [[a Aa Fa_u] | [Fa]]; last first.
    by case/imsetP=> a /sTA Aa -> Fa_u; exists a. 
  by exists (dd1 a) => //; rewrite -dd1_id //; do 2!apply: mem_imset.
have [tiP_G inj_dd1]: trivIset P_G /\ {in T &, injective dd1}.
  apply: trivIimset => [_ _ /imsetP[a Aa ->] /imsetP[b Ab ->] |]; last first.
    apply/imsetP=> [[a]]; move/sTA=> Aa; move/esym; move/eqP; case/set0Pn.
    by exists (a ^ 1)%g; apply: mem_imset2; rewrite ?group1 ?rcoset_refl.
  rewrite !dd1_id //; apply: contraR.
  by case/Dade_support1_TI=> // x Lx ->; rewrite classGidl.
rewrite big_trivIset //= big_imset {P_G tiP_G inj_dd1}//=.
symmetry; rewrite (cfdotEl _ CFalpha).
pose P_A := [set a ^: L | a in T].
have rLid x: repr (x ^: L) ^: L = x ^: L.
  by have [y Ly ->] := repr_class L x; rewrite classGidl.
have {1}<-: cover P_A = A.
  apply/setP=> a; apply/bigcupP/idP=> [[_ /imsetP[d /sTA Ab ->]] | Aa].
    by case/imsetP=> x Lx ->; rewrite memJ_norm ?(subsetP nAL).
  by exists (a ^: L); rewrite ?class_refl // -rLid; do 2!apply: mem_imset.
have [tiP_A injFA]: trivIset P_A /\ {in T &, injective (class^~ L)}.
  apply: trivIimset => [_ _ /imsetP[a Aa ->] /imsetP[b Ab ->] |]; last first.
    by apply/imsetP=> [[a _ /esym/eqP/set0Pn[]]]; exists a; exact: class_refl.
  rewrite !rLid; apply: contraR => /pred0Pn[c /andP[/=]].
  by do 2!move/class_transr <-.
rewrite big_trivIset //= big_imset {P_A tiP_A injFA}//=.
apply: canRL (mulKf (neq0CG G)) _; rewrite mulrA big_distrr /=.
apply: eq_bigr => a /sTA=> {T sTA}Aa.
have [La def_Ca] := (subsetP sAL a Aa, defCA Aa).
rewrite (eq_bigr (fun _ => alpha a * (psi a)^*)) => [|ax]; last first.
  by case/imsetP=> x Lx ->{ax}; rewrite !cfunJ.
rewrite sumr_const -index_cent1 mulrC -mulr_natr -!mulrA.
rewrite (eq_bigr (fun xa => alpha a * (phi xa)^*)) => [|xa Fa_xa]; last first.
  by rewrite (DadeE _ Aa).
rewrite -big_distrr /= -rmorph_sum; congr (_ * _).
rewrite mulrC mulrA -natrM mulnC -(Lagrange (subsetIl G 'C[a])).
rewrite -mulnA mulnCA -(sdprod_card def_Ca) -mulnA Lagrange ?subsetIl //.
rewrite mulnA natrM mulfK ?neq0CG // -conjC_nat -rmorphM; congr (_ ^*).
have /and3P[_ tiHa _] := Dade_cover_TI Aa.
rewrite (set_partition_big _ (partition_class_support _ _)) //=.
rewrite (eq_bigr (fun _ => \sum_(x in H a) phi (x * a)%g)); last first.
  move=> _ /imsetP[x Gx ->]; rewrite -rcosetE.
  rewrite (big_imset _ (in2W (conjg_inj x))) (big_imset _ (in2W (mulIg a))) /=.
  by apply: eq_bigr => u Hu; rewrite cfunJ ?groupM ?(subsetP sLG a).
rewrite sumr_const card_orbit astab1Js norm_Dade_cover //.
by rewrite natrM -mulrA mulr_natl psiA // mulVKf ?neq0CG.
Qed.

(* This is Peterfalvi (2.7), second part. *)
Lemma Dade_reciprocity alpha (phi : 'CF(G)) :
    alpha \in 'CF(L, A) ->
    {in A, forall a, {in H a, forall u, phi (u * a)%g = phi a}} ->
  '[alpha^\tau, phi] = '[alpha, 'Res[L] phi].
Proof.
move=> CFalpha phiH; apply: general_Dade_reciprocity => // a Aa.
rewrite cfResE ?(subsetP sAL) //; apply: canRL (mulKf (neq0CG _)) _.
by rewrite mulr_natl -sumr_const; apply: eq_bigr => x Hx; rewrite phiH.
Qed.

(* This is Peterfalvi (2.6)(a). *)
Lemma Dade_isometry : {in 'CF(L, A) &, isometry Dade}.
Proof.
move=> alpha beta CFalpha CFbeta /=.
rewrite Dade_reciprocity ?Dade_cfun => // [|a Aa u Hu]; last first.
  by rewrite (DadeE _ Aa) ?mem_Dade_support1 ?Dade_id.
rewrite !(cfdotEl _ CFalpha); congr (_ * _); apply: eq_bigr => x Ax.
by rewrite cfResE ?(subsetP sAL) // Dade_id.
Qed.

(* Supplement to Peterfalvi (2.3)/(2.6)(a); implies Isaacs Lemma 7.7. *)
Lemma Dade_Ind : normedTI A G L -> {in 'CF(L, A), Dade =1 'Ind}.
Proof.
case/Dade_normedTI_P=> _ trivH alpha Aalpha.
rewrite [alpha^\tau]cfun_sum_cfdot ['Ind _]cfun_sum_cfdot.
apply: eq_bigr => i _; rewrite -cfdot_Res_r -Dade_reciprocity // => a Aa /= u.
by rewrite trivH // => /set1P->; rewrite mul1g.
Qed.

Definition Dade_set_signalizer (B : {set gT}) := \bigcap_(a in B) H a.
Local Notation "''H' ( B )" := (Dade_set_signalizer B)
  (at level 8, format "''H' ( B )") : group_scope.
Canonical Dade_set_signalizer_group B := [group of 'H(B)].
Definition Dade_set_normalizer B := 'H(B) <*> 'N_L(B).
Local Notation "''M' ( B )" := (Dade_set_normalizer B)
  (at level 8, format "''M' ( B )") : group_scope.
Canonical Dade_set_normalizer_group B := [group of 'M(B)].

Let calP := [set B : {set gT} | B \subset A & B != set0].

(* This is Peterfalvi (2.8). *)
Lemma Dade_set_sdprod : {in calP, forall B, 'H(B) ><| 'N_L(B) = 'M(B)}.
Proof.
move=> B /setIdP[sBA notB0]; apply: sdprodEY => /=.
  apply/subsetP=> x /setIP[Lx nBx]; rewrite inE.
  apply/bigcapsP=> a Ba; have Aa := subsetP sBA a Ba.
  by rewrite sub_conjg -DadeJ ?groupV // bigcap_inf // memJ_norm ?groupV.
have /set0Pn[a Ba] := notB0; have Aa := subsetP sBA a Ba.
have [_ /mulG_sub[sHaC _] _ tiHaL] := sdprodP (defCA Aa).
rewrite -(setIidPl sLG) -setIA setICA (setIidPl sHaC) in tiHaL.
by rewrite setICA ['H(B)](bigD1 a) //= !setIA tiHaL !setI1g.
Qed.

Section DadeExpansion.

Variable aa : 'CF(L).
Hypothesis CFaa : aa \in 'CF(L, A).

Definition Dade_restrm B :=
  if B \in calP then remgr 'H(B) 'N_L(B) else trivm 'M(B).
Fact Dade_restrM B : {in 'M(B) &, {morph Dade_restrm B : x y / x * y}%g}.
Proof.
rewrite /Dade_restrm; case: ifP => calP_B; last exact: morphM.
have defM := Dade_set_sdprod calP_B; have [nsHM _ _ _ _] := sdprod_context defM.
by apply: remgrM; first exact: sdprod_compl.
Qed.
Canonical Dade_restr_morphism B := Morphism (@Dade_restrM B).
Definition Dade_cfun_restriction B :=
  cfMorph ('Res[Dade_restrm B @* 'M(B)] aa).

Local Notation "''aa_' B" := (Dade_cfun_restriction B)
  (at level 3, B at level 2, format "''aa_' B") : ring_scope.

Definition Dade_transversal := [set repr (B :^: L) | B in calP].
Local Notation calB := Dade_transversal.

Lemma Dade_restrictionE B x :
  B \in calP -> 'aa_B x = aa (remgr 'H(B) 'N_L(B) x) *+ (x \in 'M(B)).
Proof.
move=> calP_B; have /sdprodP[_ /= defM _ _] := Dade_set_sdprod calP_B.
have [Mx | /cfun0-> //] := boolP (x \in 'M(B)).
rewrite mulrb cfMorphE // morphimEdom /= /Dade_restrm calP_B.
rewrite cfResE ?mem_imset {x Mx}//= -defM.
by apply/subsetP=> _ /imsetP[x /mem_remgr/setIP[Lx _] ->].
Qed.
Local Notation rDadeE := Dade_restrictionE.

Lemma Dade_restriction_vchar B : aa \in 'Z[irr L] -> 'aa_B \in 'Z[irr 'M(B)].
Proof.
rewrite /'aa_B => /vcharP[a1 Na1 [a2 Na2 ->]].
by rewrite !linearB /= rpredB // char_vchar ?cfMorph_char ?cfRes_char.
Qed.

Let sMG B : B \in calP -> 'M(B) \subset G.
Proof.
case/setIdP=> /subsetP sBA /set0Pn[a Ba].
by rewrite join_subG ['H(B)](bigD1 a Ba) !subIset ?sLG ?sHG ?sBA.
Qed.

(* This is Peterfalvi (2.10.1) *)
Lemma Dade_Ind_restr_J :
  {in L & calP, forall x B, 'Ind[G] 'aa_(B :^ x) = 'Ind[G] 'aa_B}.
Proof.
move=> x B Lx dB; have [defMB [sBA _]] := (Dade_set_sdprod dB, setIdP dB).
have dBx: B :^ x \in calP.
  by rewrite !inE -{2}(normsP nAL x Lx) conjSg -!cards_eq0 cardJg in dB *.
have defHBx: 'H(B :^ x) = 'H(B) :^ x.
  rewrite /'H(_) (big_imset _ (in2W (conjg_inj x))) -bigcapJ /=.
  by apply: eq_bigr => a Ba; rewrite DadeJ ?(subsetP sBA).
have defNBx: 'N_L(B :^ x) = 'N_L(B) :^ x by rewrite conjIg -normJ (conjGid Lx).
have [_ mulHNB _ tiHNB] := sdprodP defMB.
have defMBx: 'M(B :^ x) = 'M(B) :^ x.
  rewrite -mulHNB conjsMg -defHBx -defNBx.
  by case/sdprodP: (Dade_set_sdprod dBx).
have def_aa_x y: 'aa_(B :^ x) (y ^ x) = 'aa_B y.
  rewrite !rDadeE // defMBx memJ_conjg !mulrb -mulHNB defHBx defNBx.
  have [[h z Hh Nz ->] | // ] := mulsgP.
  by rewrite conjMg !remgrMid ?cfunJ ?memJ_conjg // -conjIg tiHNB conjs1g. 
apply/cfunP=> y; have Gx := subsetP sLG x Lx.
rewrite [eq]lock !cfIndE ?sMG //= {1}defMBx cardJg -lock; congr (_ * _).
rewrite (reindex_astabs 'R x) ?astabsR //=.
by apply: eq_bigr => z _; rewrite conjgM def_aa_x.
Qed.

(* This is Peterfalvi (2.10.2) *)
Lemma Dade_setU1 : {in calP & A, forall B a, 'H(a |: B) = 'C_('H(B))[a]}.
Proof.
move=> B a dB Aa; rewrite /'H(_) bigcap_setU big_set1 -/'H(B).
apply/eqP; rewrite setIC eqEsubset setIS // subsetI subsetIl /=.
have [sHBG pi'HB]: 'H(B) \subset G /\ pi^'.-group 'H(B).
  have [sBA /set0Pn[b Bb]] := setIdP dB; have Ab := subsetP sBA b Bb.
  have sHBb: 'H(B) \subset H b by rewrite ['H(B)](bigD1 b) ?subsetIl.
  by rewrite (pgroupS sHBb) ?pi'H ?(subset_trans sHBb) ?sHG.
have [nsHa _ defCa _ _] := sdprod_context (defCA Aa).
have [hallHa _] := coprime_mulGp_Hall defCa (pi'H a) (piCL Aa).
by rewrite (sub_normal_Hall hallHa) ?(pgroupS (subsetIl _ _)) ?setSI.
Qed.

Let calA g (X : {set gT}) := [set x in G | g ^ x \in X]%g.

(* This is Peterfalvi (2.10.3) *)
Lemma Dade_Ind_expansion B g :
    B \in calP ->
  [/\ g \notin Atau -> ('Ind[G, 'M(B)] 'aa_B) g = 0
    & {in A, forall a, g \in dd1 a ->
       ('Ind[G, 'M(B)] 'aa_B) g =
          (aa a / #|'M(B)|%:R) *
               \sum_(b in 'N_L(B) :&: a ^: L) #|calA g ('H(B) :* b)|%:R}].
Proof.
move=> dB; set LHS := 'Ind _ g.
have defMB := Dade_set_sdprod dB; have [_ mulHNB nHNB tiHNB] := sdprodP defMB.
have [sHMB sNMB] := mulG_sub mulHNB.
have{LHS} ->: LHS = #|'M(B)|%:R^-1 * \sum_(x in calA g 'M(B)) 'aa_B (g ^ x). 
  rewrite {}/LHS cfIndE ?sMG //; congr (_ * _).
  rewrite (bigID [pred x | g ^ x \in 'M(B)]) /= addrC big1 ?add0r => [|x].
    by apply: eq_bigl => x; rewrite inE.
  by case/andP=> _ notMgx; rewrite cfun0.
pose fBg x := remgr 'H(B) 'N_L(B) (g ^ x).
pose supp_aBg := [pred b in A | g \in dd1 b].
have supp_aBgP: {in calA g 'M(B), forall x,
  ~~ supp_aBg (fBg x) -> 'aa_B (g ^ x)%g = 0}.
- move=> x /setIdP[]; set b := fBg x => Gx MBgx notHGx; rewrite rDadeE // MBgx. 
  have Nb: b \in 'N_L(B) by rewrite mem_remgr ?mulHNB.
  have Cb: b \in 'C_L[b] by rewrite inE cent1id; have [-> _] := setIP Nb.
  rewrite (cfun_on0 CFaa) // -/(fBg x) -/b; apply: contra notHGx => Ab.
  have nHb: b \in 'N('H(B)) by rewrite (subsetP nHNB).
  have [sBA /set0Pn[a Ba]] := setIdP dB; have Aa := subsetP sBA a Ba.
  have [|/= partHBb _] := partition_cent_rcoset nHb.
    rewrite (coprime_dvdr (order_dvdG Cb)) //= ['H(B)](bigD1 a) //=.
    by rewrite (coprimeSg (subsetIl _ _)) ?coHL. 
  have Hb_gx: g ^ x \in 'H(B) :* b by rewrite mem_rcoset mem_divgr ?mulHNB.
  have [defHBb _ _] := and3P partHBb; rewrite -(eqP defHBb) in Hb_gx.
  case/bigcupP: Hb_gx => Cy; case/imsetP=> y HBy ->{Cy} Cby_gx.
  have sHBa: 'H(B) \subset H a by rewrite bigcap_inf.
  have sHBG: 'H(B) \subset G := subset_trans sHBa (sHG a).
  rewrite Ab -(memJ_conjg _ x) class_supportGidr //  -(conjgKV y (g ^ x)).
  rewrite mem_imset2 // ?(subsetP sHBG) {HBy}// -mem_conjg.
  apply: subsetP Cby_gx; rewrite {y}conjSg mulSg //.
  have [nsHb _ defCb _ _] := sdprod_context (defCA Ab).
  have [hallHb _] := coprime_mulGp_Hall defCb (pi'H b) (piCL Ab).
  rewrite (sub_normal_Hall hallHb) ?setSI // (pgroupS _ (pi'H a)) //=.
  by rewrite subIset ?sHBa.  
split=> [notHGg | a Aa Hag].
  rewrite big1 ?mulr0 // => x; move/supp_aBgP; apply; set b := fBg x.
  by apply: contra notHGg; case/andP=> Ab Hb_x; apply/bigcupP; exists b.
rewrite -mulrA mulrCA; congr (_ * _); rewrite big_distrr /=.
set nBaL := _ :&: _; rewrite (bigID [pred x | fBg x \in nBaL]) /= addrC.
rewrite big1 ?add0r => [|x /andP[calAx not_nBaLx]]; last first.
  apply: supp_aBgP => //; apply: contra not_nBaLx.
  set b := fBg x => /andP[Ab Hb_g]; have [Gx MBx] := setIdP calAx.
  rewrite inE mem_remgr ?mulHNB //; apply/imsetP/Dade_support1_TI => //.
  by apply/pred0Pn; exists g; exact/andP.
rewrite (partition_big fBg (mem nBaL)) /= => [|x]; last by case/andP.
apply: eq_bigr => b; case/setIP=> Nb aLb; rewrite mulr_natr -sumr_const.
apply: eq_big => x; rewrite ![x \in _]inE -!andbA.
  apply: andb_id2l=> Gx; apply/and3P/idP=> [[Mgx _] /eqP <- | HBb_gx].
    by rewrite mem_rcoset mem_divgr ?mulHNB.
  suffices ->: fBg x = b.
    by rewrite inE Nb (subsetP _ _ HBb_gx) // -mulHNB mulgS ?sub1set.
  by rewrite /fBg; have [h Hh ->] := rcosetP HBb_gx; exact: remgrMid.
move/and4P=> [_ Mgx _ /eqP def_fx].
rewrite rDadeE // Mgx -/(fBg x) def_fx; case/imsetP: aLb => y Ly ->.
by rewrite cfunJ // (subsetP sAL).
Qed.

(* This is Peterfalvi (2.10) *)
Lemma Dade_expansion :
  aa^\tau = - \sum_(B in calB) (- 1) ^+ #|B| *: 'Ind[G, 'M(B)] 'aa_B.
Proof.
apply/cfunP=> g; rewrite !cfunElock sum_cfunE.
pose n1 (B : {set gT}) : algC := (-1) ^+ #|B| / #|L : 'N_L(B)|%:R.
pose aa1 B := ('Ind[G, 'M(B)] 'aa_B) g.
have dBJ: {acts L, on calP | 'Js}.
  move=> x Lx /= B; rewrite !inE -!cards_eq0 cardJg.
  by rewrite -{1}(normsP nAL x Lx) conjSg.
transitivity (- (\sum_(B in calP) n1 B * aa1 B)); last first.
  congr (- _); rewrite {1}(partition_big_imset (fun B => repr (B :^: L))) /=.
  apply: eq_bigr => B /imsetP[B1 dB1 defB].
  have B1L_B: B \in B1 :^: L by rewrite defB (mem_repr B1) ?orbit_refl.
  have{dB1} dB1L: {subset B1 :^: L <= calP}.
    by move=> _ /imsetP[x Lx ->]; rewrite dBJ.
  have dB: B \in calP := dB1L B B1L_B.
  rewrite (eq_bigl (mem (B :^: L))) => [|B2 /=]; last first.
    apply/andP/idP=> [[_ /eqP <-] | /(orbit_trans B1L_B) B1L_B2].
      by rewrite orbit_sym (mem_repr B2) ?orbit_refl.
    by rewrite [B2 :^: L](orbit_transl B1L_B2) -defB dB1L.
  rewrite (eq_bigr (fun _ => n1 B * aa1 B)) => [|_ /imsetP[x Lx ->]].
    rewrite cfunE sumr_const -mulr_natr mulrAC card_orbit astab1Js divfK //.
    by rewrite pnatr_eq0 -lt0n indexg_gt0.
  rewrite /aa1 Dade_Ind_restr_J //; congr (_ * _).
  by rewrite /n1 cardJg -{1 2}(conjGid Lx) normJ -conjIg indexJg.
case: pickP => /= [a /andP[Aa Ha_g] | notHAg]; last first.
  rewrite big1 ?oppr0 // /aa1 => B dB.
  have [->] := Dade_Ind_expansion g dB; first by rewrite mulr0.
  by apply/bigcupP=> [[a Aa Ha_g]]; case/andP: (notHAg a).
pose P_ b := [set B in calP | b \in 'N_L(B)].
pose aa2 B b : algC := #|calA g ('H(B) :* b)|%:R.
pose nn2 (B : {set gT}) : algC := (-1) ^+ #|B| / #|'H(B)|%:R.
pose sumB b := \sum_(B in P_ b) nn2 B * aa2 B b.
transitivity (- aa a / #|L|%:R * \sum_(b in a ^: L) sumB b); last first.
  rewrite !mulNr; congr (- _).
  rewrite (exchange_big_dep (mem calP)) => [|b B _] /=; last by case/setIdP.
  rewrite big_distrr /aa1; apply: eq_bigr => B dB; rewrite -big_distrr /=.
  have [_ /(_ a) -> //] := Dade_Ind_expansion g dB; rewrite !mulrA.
  congr (_ * _); last by apply: eq_bigl => b; rewrite inE dB /= andbC -in_setI.
  rewrite -mulrA mulrCA -!mulrA; congr (_ * _).
  rewrite -invfM mulrCA -invfM -!natrM; congr (_ / _%:R).
  rewrite -(sdprod_card (Dade_set_sdprod dB)) mulnA mulnAC; congr (_ * _)%N.
  by rewrite mulnC Lagrange ?subsetIl.
rewrite (eq_bigr (fun _ => sumB a)) /= => [|_ /imsetP[x Lx ->]]; last first.
  rewrite {1}/sumB (reindex_inj (@conjsg_inj _ x)) /=.
  symmetry; apply: eq_big => B.
    rewrite ![_ \in P_ _]inE dBJ //.
    by rewrite -{2}(conjGid Lx) normJ -conjIg memJ_conjg.
  case/setIdP=> dB Na; have [sBA _] := setIdP dB.
  have defHBx: 'H(B :^ x) = 'H(B) :^ x.
    rewrite /'H(_) (big_imset _ (in2W (conjg_inj x))) -bigcapJ /=.
    by apply: eq_bigr => b Bb; rewrite DadeJ ?(subsetP sBA).
  rewrite /nn2 /aa2 defHBx !cardJg; congr (_ * _%:R).
  rewrite -(card_rcoset _ x); apply: eq_card => y.
  rewrite !(inE, mem_rcoset, mem_conjg) conjMg conjVg conjgK -conjgM.
  by rewrite groupMr // groupV (subsetP sLG).
rewrite sumr_const mulrC [sumB a](bigD1 [set a]) /=; last first.
  by rewrite 3!inE cent1id sub1set Aa -cards_eq0 cards1 (subsetP sAL).
rewrite -[_ *+ _]mulr_natr -mulrA mulrDl -!mulrA ['H(_)]big_set1 cards1.
have ->: aa2 [set a] a = #|'C_G[a]|%:R.
  have [u x Ha_ux Gx def_g] := imset2P Ha_g.
  rewrite -(card_lcoset _ x^-1); congr _%:R; apply: eq_card => y.
  rewrite ['H(_)]big_set1 mem_lcoset invgK inE def_g -conjgM.
  rewrite -(groupMl y Gx) inE; apply: andb_id2l => Gxy.
  by have [_ _ -> //] := normedTI_memJ_P (Dade_cover_TI Aa); rewrite inE Gxy.
rewrite mulN1r mulrC mulrA -natrM -(sdprod_card (defCA Aa)).
rewrite -mulnA card_orbit astab1J Lagrange ?subsetIl // mulnC natrM.
rewrite mulrAC mulfK ?neq0CG // mulrC divfK ?neq0CG // opprK.
rewrite (bigID [pred B : {set gT} | a \in B]) /= mulrDl addrA.
apply: canRL (subrK _) _; rewrite -mulNr -sumrN; congr (_ + _ * _).
symmetry.
rewrite (reindex_onto (fun B => a |: B) (fun B => B :\ a)) /=; last first.
  by move=> B; case/andP=> _; exact: setD1K.
symmetry; apply: eq_big => B.
  rewrite setU11 andbT -!andbA; apply/and3P/and3P; case.
    do 2![case/setIdP] => sBA ntB /setIP[La nBa] _ notBa.
    rewrite 3!inE subUset sub1set Aa sBA La setU1K // -cards_eq0 cardsU1 notBa.
    rewrite -sub1set normsU ?sub1set ?cent1id //= eq_sym eqEcard subsetUl /=.
    by rewrite cards1 cardsU1 notBa ltnS leqn0 cards_eq0.
  do 2![case/setIdP] => /subUsetP[_ sBA] _ /setIP[La].
  rewrite inE conjUg (normP (cent1id a)) => /subUsetP[_ sBa_aB].
  rewrite eq_sym eqEcard subsetUl cards1 (cardsD1 a) setU11 ltnS leqn0 /=.
  rewrite cards_eq0 => notB0 /eqP defB.
  have notBa: a \notin B by rewrite -defB setD11.
  split=> //; last by apply: contraNneq notBa => ->; exact: set11.
  rewrite !inE sBA La -{1 3}defB notB0 subsetD1 sBa_aB.
  by rewrite mem_conjg /(a ^ _) invgK mulgA mulgK.
do 2![case/andP] => /setIdP[dB Na] _ notBa.
suffices ->: aa2 B a = #|'H(B) : 'H(a |: B)|%:R * aa2 (a |: B) a.
  rewrite /nn2 cardsU1 notBa exprS mulN1r !mulNr; congr (- _).
  rewrite !mulrA; congr (_ * _); rewrite -!mulrA; congr (_ * _).
  apply: canLR (mulKf (neq0CG _)) _; apply: canRL (mulfK (neq0CG _)) _ => /=.
  by rewrite -natrM mulnC Lagrange //= Dade_setU1 ?subsetIl.
rewrite /aa2 Dade_setU1 //= -natrM; congr _%:R.
have defMB := Dade_set_sdprod dB; have [_ mulHNB nHNB tiHNB] := sdprodP defMB.
have [sHMB sNMB] := mulG_sub mulHNB; have [La nBa] := setIP Na.
have nHa: a \in 'N('H(B)) by rewrite (subsetP nHNB).
have Ca: a \in 'C_L[a] by rewrite inE cent1id La.
have [|/= partHBa nbHBa] := partition_cent_rcoset nHa.
  have [sBA] := setIdP dB; case/set0Pn=> b Bb; have Ab := subsetP sBA b Bb.
  rewrite (coprime_dvdr (order_dvdG Ca)) //= ['H(B)](bigD1 b) //=.
  by rewrite (coprimeSg (subsetIl _ _)) ?coHL. 
pose pHBa := mem ('H(B) :* a).
rewrite -sum1_card (partition_big (fun x => g ^ x) pHBa) /= => [|x]; last first.
  by case/setIdP=> _ ->.
rewrite (set_partition_big _ partHBa) /= -nbHBa -sum_nat_const.
apply: eq_bigr => _ /imsetP[x Hx ->].
rewrite (big_imset _ (in2W (conjg_inj x))) /=.
rewrite -(card_rcoset _ x) -sum1_card; symmetry; set HBaa := 'C_(_)[a] :* a.
rewrite (partition_big (fun y => g ^ (y * x^-1)) (mem HBaa)); last first.
  by move=> y; rewrite mem_rcoset => /setIdP[].
apply: eq_bigr => /= u Ca_u; apply: eq_bigl => z.
rewrite -(canF_eq (conjgKV x)) -conjgM; apply: andb_id2r; move/eqP=> def_u.
have sHBG: 'H(B) \subset G.
  have [sBA /set0Pn[b Bb]] := setIdP dB; have Ab := subsetP sBA b Bb.
  by rewrite (bigcap_min b) ?sHG.
rewrite mem_rcoset !inE groupMr ?groupV ?(subsetP sHBG x Hx) //=.
congr (_ && _); have [/eqP defHBa _ _] := and3P partHBa.
symmetry; rewrite def_u Ca_u -defHBa -(mulgKV x z) conjgM def_u -/HBaa.
by rewrite cover_imset -class_supportEr mem_imset2.
Qed.

End DadeExpansion.

(* This is Peterfalvi (2.6)(b) *)
Lemma Dade_vchar alpha : alpha \in 'Z[irr L, A] -> alpha^\tau \in 'Z[irr G].
Proof.
rewrite [alpha \in _]zchar_split => /andP[Zaa CFaa].
rewrite Dade_expansion // rpredN rpred_sum // => B dB.
suffices calP_B: B \in calP.
  by rewrite rpredZsign cfInd_vchar // Dade_restriction_vchar.
case/imsetP: dB => B0 /setIdP[sB0A notB00] defB.
have [x Lx ->]: exists2 x, x \in L & B = B0 :^ x.
  by apply/imsetP; rewrite defB (mem_repr B0) ?orbit_refl.
by rewrite inE -cards_eq0 cardJg cards_eq0 -(normsP nAL x Lx) conjSg sB0A.
Qed.

(* This summarizes Peterfalvi (2.6). *)
Lemma Dade_Zisometry : {in 'Z[irr L, A], isometry Dade, to 'Z[irr G, G^#]}.
Proof.
split; first by apply: sub_in2 Dade_isometry; exact: zchar_on.
by move=> phi Zphi; rewrite /= zchar_split Dade_vchar ?Dade_cfun.
Qed.

End Two.

Section RestrDade.

Variables (gT : finGroupType) (G L : {group gT}) (A A1 : {set gT}).
Hypothesis ddA : Dade_hypothesis G L A.
Hypotheses (sA1A : A1 \subset A) (nA1L : L \subset 'N(A1)).
Let ssA1A := subsetP sA1A.

(* This is Peterfalvi (2.11), first part. *)
Lemma restr_Dade_hyp : Dade_hypothesis G L A1.
Proof.
have [/andP[sAL nAL] notA_1 sLG conjAG [H defCa coHL]] := ddA.
have nsA1L: A1 <| L by rewrite /normal (subset_trans sA1A).
split; rewrite ?(contra (@ssA1A _)) //; first exact: sub_in2 conjAG.
by exists H; [exact: sub_in1 defCa | exact: sub_in2 coHL].
Qed.
Local Notation ddA1 := restr_Dade_hyp.

Local Notation H dd := (Dade_signalizer dd).
Lemma restr_Dade_signalizer H1 : {in A, H ddA =1 H1} -> {in A1, H ddA1 =1 H1}.
Proof.
move=> defH1; apply: def_Dade_signalizer => a /ssA1A Aa.
by rewrite -defH1 ?Dade_sdprod.
Qed.

Lemma restr_Dade_support1 : {in A1, Dade_support1 ddA1 =1 Dade_support1 ddA}.
Proof.
by move=> a A1a; rewrite /Dade_support1 (@restr_Dade_signalizer (H ddA)).
Qed.

Lemma restr_Dade_support :
  Dade_support ddA1 = \bigcup_(a in A1) Dade_support1 ddA a.
Proof. by rewrite -(eq_bigr _ restr_Dade_support1). Qed.

Definition restr_Dade := Dade ddA1.

(* This is Peterfalvi (2.11), second part. *)
Lemma restr_DadeE : {in 'CF(L, A1), restr_Dade =1 Dade ddA}.
Proof.
move=> aa CF1aa; apply/cfunP=> g; rewrite cfunElock.
have CFaa: aa \in 'CF(L, A) := cfun_onS sA1A CF1aa.
have [a /= /andP[A1a Ha_g] | no_a /=] := pickP.
  by apply/esym/DadeE; rewrite -1?restr_Dade_support1 ?ssA1A.
rewrite cfunElock; case: pickP => //= a /andP[_ Ha_g].
rewrite (cfun_on0 CF1aa) //; apply: contraFN (no_a a) => A1a.
by rewrite A1a restr_Dade_support1.
Qed.

End RestrDade.

Section NormedTI.

Variables (gT : finGroupType) (G L : {group gT}) (A : {set gT}).
Hypotheses (tiAG : normedTI A G L) (sAG1 : A \subset G^#).

(* This is the existence part of Peterfalvi (2.3). *)
Lemma normedTI_Dade : Dade_hypothesis G L A.
Proof.
have [[sAG notA1] [_ _ /eqP defL]] := (subsetD1P sAG1, and3P tiAG).
have [_ sLG tiAG_L] := normedTI_memJ_P tiAG.
split=> // [|a b Aa Ab /imsetP[x Gx def_b]|].
- rewrite /(A <| L) -{2}defL subsetIr andbT; apply/subsetP=> a Aa.
  by rewrite -(tiAG_L a) ?(subsetP sAG) // conjgE mulKg.
- by rewrite def_b mem_imset // -(tiAG_L a) -?def_b.
exists (fun _ => 1%G) => [a Aa | a b _ _]; last by rewrite cards1 coprime1n.
by rewrite sdprod1g -(setIidPl sLG) -setIA (setIidPr (cent1_normedTI tiAG Aa)).
Qed.

Let def_ddA := Dade_Ind normedTI_Dade tiAG.

(* This is the identity part of Isaacs, Lemma 7.7. *)
Lemma normedTI_Ind_id1 :
  {in 'CF(L, A) & 1%g |: A, forall alpha, 'Ind[G] alpha =1 alpha}.
Proof. by move=> aa a CFaa A1a; rewrite /= -def_ddA // Dade_id1. Qed.

(* A more restricted, but more useful form. *)
Lemma normedTI_Ind_id :
  {in 'CF(L, A) & A, forall alpha, 'Ind[G] alpha =1 alpha}.
Proof. by apply: sub_in11 normedTI_Ind_id1 => //; apply/subsetP/subsetUr. Qed.

(* This is the isometry part of Isaacs, Lemma 7.7. *)
(* The statement in Isaacs is slightly more general in that it allows for     *)
(* beta \in 'CF(L, 1%g |: A); this appears to be more cumbersome than useful. *)
Lemma normedTI_isometry : {in 'CF(L, A) &, isometry 'Ind[G]}.
Proof. by move=> aa bb CFaa CFbb; rewrite /= -!def_ddA // Dade_isometry. Qed.

End NormedTI.