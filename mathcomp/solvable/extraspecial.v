(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun eqtype ssrnat seq div choice fintype.
From mathcomp
Require Import bigop finset prime binomial fingroup morphism perm automorphism.
From mathcomp
Require Import presentation quotient action commutator gproduct gfunctor.
From mathcomp
Require Import ssralg finalg zmodp cyclic pgroup center gseries.
From mathcomp
Require Import nilpotent sylow abelian finmodule matrix maximal extremal.

(******************************************************************************)
(* This file contains the fine structure thorems for extraspecial p-groups.   *)
(* Together with the material in the maximal and extremal libraries, it       *)
(* completes the coverage of Aschbacher, section 23.                          *)
(* We define canonical representatives for the group classes that cover the   *)
(* extremal p-groups (non-abelian p-groups with a cyclic maximal subgroup):   *)
(* 'Mod_m == the modular group of order m, for m = p ^ n, p prime and n >= 3. *)
(*   'D_m == the dihedral group of order m, for m = 2n >= 4.                  *)
(*   'Q_m == the generalized quaternion group of order m, for q = 2 ^ n >= 8. *)
(*  'SD_m == the semi-dihedral group of order m, for m = 2 ^ n >= 16.         *)
(* In each case the notation is defined in the %type, %g and %G scopes, where *)
(* it denotes a finGroupType, a full gset and the full group for that type.   *)
(* However each notation is only meaningful under the given conditions, in    *)
(*   We construct and study the following extraspecial groups:                *)
(*    p^{1+2} == if p is prime, an extraspecial group of order p^3 that has   *)
(*               exponent p or 4, and p-rank 2: thus p^{1+2} is isomorphic to *)
(*               'D_8 if p - 2, and NOT isomorphic to 'Mod_(p^3) if p is odd. *)
(*  p^{1+2*n} == the central product of n copies of p^{1+2}, thus of order    *)
(*               p^(1+2*n) if p is a prime, and, when n > 0, a representative *)
(*               of the (unique) isomorphism class of extraspecial groups of  *)
(*               order p^(1+2*n), of exponent p or 4, and p-rank n+1.         *)
(*       'D^n == an alternative (and preferred) notation for 2^{1+2*n}, which *)
(*               is isomorphic to the central product of n copies od 'D_8.    *)
(*     'D^n*Q == the central product of 'D^n with 'Q_8, thus isomorphic to    *)
(*               all extraspecial groups of order 2 ^ (2 * n + 3) that are    *)
(*               not isomorphic to 'D^n.+1 (or, equivalently, have 2-rank n). *)
(* As in extremal.v, these notations are simultaneously defined in the %type, *)
(* %g and %G scopes -- depending on the syntactic context, they denote either *)
(* a finGroupType, the set, or the group of all its elements.                 *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GroupScope GRing.Theory.

Reserved Notation "p ^{1+2}" (at level 2, format "p ^{1+2}").
Reserved Notation "p ^{1+2* n }"
  (at level 2, n at level 2, format "p ^{1+2* n }").
Reserved Notation "''D^' n" (at level 8, n at level 2, format "''D^' n").
Reserved Notation "''D^' n * 'Q'"
  (at level 8, n at level 2, format "''D^' n * 'Q'").

Module Pextraspecial.

Section Construction.

Variable p : nat.

Definition act ij (k : 'Z_p) := let: (i, j) := ij in (i + k * j, j).
Lemma actP : is_action [set: 'Z_p] act.
Proof.
apply: is_total_action=> [] [i j] => [|k1 k2] /=; first by rewrite mul0r addr0.
by rewrite mulrDl addrA.
Qed.
Canonical action := Action actP.

Lemma gactP : is_groupAction [set: 'Z_p * 'Z_p] action.
Proof.
move=> k _ /=; rewrite inE.
apply/andP; split; first by apply/subsetP=> ij _; rewrite inE.
apply/morphicP=> /= [[i1 j1] [i2 j2] _ _].
by rewrite !permE /= mulrDr -addrA (addrCA i2) (addrA i1).
Qed.
Definition groupAction := GroupAction gactP.

Fact gtype_key : unit. Proof. by []. Qed.
Definition gtype := locked_with gtype_key (sdprod_groupType groupAction).

Definition ngtype := ncprod [set: gtype].

End Construction.

Definition ngtypeQ n := xcprod [set: ngtype 2 n] 'Q_8.

End Pextraspecial.

Notation "p ^{1+2}" := (Pextraspecial.gtype p) : type_scope.
Notation "p ^{1+2}" := [set: gsort p^{1+2}] : group_scope.
Notation "p ^{1+2}" := [set: gsort p^{1+2}]%G : Group_scope.

Notation "p ^{1+2* n }" := (Pextraspecial.ngtype p n) : type_scope.
Notation "p ^{1+2* n }" := [set: gsort p^{1+2*n}] : group_scope.
Notation "p ^{1+2* n }" := [set: gsort p^{1+2*n}]%G : Group_scope.

Notation "''D^' n" := (Pextraspecial.ngtype 2 n) : type_scope.
Notation "''D^' n" := [set: gsort 'D^n] : group_scope.
Notation "''D^' n" := [set: gsort 'D^n]%G : Group_scope.

Notation "''D^' n * 'Q'" := (Pextraspecial.ngtypeQ n) : type_scope.
Notation "''D^' n * 'Q'" := [set: gsort 'D^n*Q] : group_scope.
Notation "''D^' n * 'Q'" := [set: gsort 'D^n*Q]%G : Group_scope.

Section ExponentPextraspecialTheory.

Variable p : nat.
Hypothesis p_pr : prime p.
Let p_gt1 := prime_gt1 p_pr.
Let p_gt0 := ltnW p_gt1.

Local Notation gtype := Pextraspecial.gtype.
Local Notation actp := (Pextraspecial.groupAction p).

Lemma card_pX1p2 : #|p^{1+2}| = (p ^ 3)%N.
Proof.
rewrite [@gtype _]unlock -(sdprod_card (sdprod_sdpair _)).
rewrite !card_injm ?injm_sdpair1 ?injm_sdpair2 // !cardsT card_prod card_ord.
by rewrite -mulnA Zp_cast.
Qed.

Lemma Grp_pX1p2 :
  p^{1+2} \isog Grp (x : y : (x ^+ p, y ^+ p, [~ x, y, x], [~ x, y, y])).
Proof.
rewrite [@gtype _]unlock; apply: intro_isoGrp => [|rT H].
  apply/existsP; pose x := sdpair1 actp (0, 1)%R; pose y := sdpair2 actp 1%R.
  exists (x, y); rewrite /= !xpair_eqE; set z := [~ x, y]; set G := _ <*> _.
  have def_z: z = sdpair1 actp (1, 0)%R.
    rewrite [z]commgEl -sdpair_act ?inE //=.
    rewrite -morphV -?morphM ?inE //=; congr (sdpair1 _ (_, _)) => /=.
      by rewrite mulr1 mulKg.
    by rewrite mulVg.
  have def_xi i: x ^+ i = sdpair1 _ (0, i%:R)%R.
    rewrite -morphX ?inE //; congr (sdpair1 _ _).
    by apply/eqP; rewrite /eq_op /= !morphX ?inE ?expg1n //=.
  have def_yi i: y ^+ i = sdpair2 _ i%:R.
    by rewrite -morphX ?inE //.
  have def_zi i: z ^+ i = sdpair1 _ (i%:R, 0)%R.
    rewrite def_z -morphX ?inE //; congr (sdpair1 _ _).
    by apply/eqP; rewrite /eq_op /= !morphX ?inE ?expg1n ?andbT //=.
  rewrite def_xi def_yi char_Zp ?morph1 //.
  rewrite def_z -morphR ?inE // !commgEl -sdpair_act ?inE //= mulr0 addr0.
  rewrite mulVg -[_ * _]/(_ , _) /= !invg1 mulg1 !mul1g mulVg morph1 !andbT.
  have Gx: x \in G by rewrite -cycle_subG joing_subl.
  have Gy: y \in G by rewrite -cycle_subG joing_subr.
  rewrite eqEsubset subsetT -im_sdpair mulG_subG /= -/G; apply/andP; split.
    apply/subsetP=> u /morphimP[[i j] _ _ def_u].
    suffices ->: u = z ^+ i * x ^+ j by rewrite groupMl groupX ?groupR.
    rewrite def_zi def_xi !natr_Zp -morphM ?inE // def_u.
    by congr (sdpair1 _ (_, _)); rewrite ?mulg1 ?mul1g.
  apply/subsetP=> v /morphimP[k _ _ def_v].
  suffices ->: v = y ^+ k by rewrite groupX.
  by rewrite def_yi natr_Zp.
case/existsP=> [[x y] /=]; set z := [~ x, y].
case/eqP=> defH xp yp /eqP/commgP czx /eqP/commgP czy.
have zp: z ^+ p = 1 by rewrite -commXg // xp comm1g.
pose f1 (ij : 'Z_p * 'Z_p) := let: (i, j) := ij in z ^+ i * x ^+ j.
have f1M: {in setT &, {morph f1 : u v / u * v}}.
  case=> /= [i1 j1] [i2 j2] _ _ /=; rewrite {3 6}Zp_cast // !expg_mod //.
  rewrite !expgD !mulgA; congr (_ * _); rewrite -!mulgA; congr (_ * _).
  by apply: commuteX2.
pose f2 (k : 'Z_p) := y ^+ k.
have f2M: {in setT &, {morph f2 : u v / u * v}}.
  by move=> k1 k2 _ _; rewrite /f2 /= {3}Zp_cast // expg_mod // expgD.
have actf: {in setT & setT, morph_act actp 'J (Morphism f1M) (Morphism f2M)}.
  case=> /= i j k _ _; rewrite modnDmr {4}Zp_cast // expg_mod // expgD.
  rewrite /f2 conjMg {1}/conjg (commuteX2 i k czy) mulKg -mulgA.
  congr (_ * _); rewrite (commuteX2 _ _ czx) mulnC expgM.
  by rewrite -commXg // -commgX ?mulKVg // commXg // /commute commuteX.
apply/homgP; exists (xsdprod_morphism actf).
apply/eqP; rewrite eqEsubset -{2}defH -genM_join gen_subG /= im_xsdprodm.
have Hx: x \in H by rewrite -cycle_subG -defH joing_subl.
have Hy: y \in H by rewrite -cycle_subG -defH joing_subr.
rewrite mulG_subG -andbA; apply/and3P; split.
- apply/subsetP=> _ /morphimP[[i j] _ _ -> /=].
  by rewrite groupMl groupX ?groupR.
- by apply/subsetP=> _ /morphimP[k _ _ ->]; rewrite groupX.
rewrite mulgSS ?cycle_subG //= morphimEdom; apply/imsetP.
  by exists (0, 1)%R; rewrite ?inE //= mul1g.
by exists 1%R; rewrite ?inE.
Qed.

Lemma pX1p2_pgroup : p.-group p^{1+2}.
Proof. by rewrite /pgroup card_pX1p2 pnat_exp pnat_id. Qed.

(* This is part of the existence half of Aschbacher ex. (8.7)(1) *)
Lemma pX1p2_extraspecial : extraspecial p^{1+2}.
Proof.
apply: (p3group_extraspecial pX1p2_pgroup); last first.
  by rewrite card_pX1p2 pfactorK.
case/existsP: (isoGrp_hom Grp_pX1p2) card_pX1p2 => [[x y]] /=.
case/eqP=> <- xp yp _ _ oXY.
apply: contraL (dvdn_cardMg <[x]> <[y]>) => cXY_XY.
rewrite -cent_joinEl ?(sub_abelian_cent2 cXY_XY) ?joing_subl ?joing_subr //.
rewrite oXY -!orderE pfactor_dvdn ?muln_gt0 ?order_gt0 // -leqNgt.
rewrite -(pfactorK 2 p_pr) dvdn_leq_log ?expn_gt0 ?p_gt0 //.
by rewrite dvdn_mul ?order_dvdn ?xp ?yp.
Qed.

(* This is part of the existence half of Aschbacher ex. (8.7)(1) *)
Lemma exponent_pX1p2 : odd p -> exponent p^{1+2} %| p.
Proof.
move=> p_odd; have pG := pX1p2_pgroup.
have ->: p^{1+2} = 'Ohm_1(p^{1+2}).
  apply/eqP; rewrite eqEsubset Ohm_sub andbT (OhmE 1 pG).
  case/existsP: (isoGrp_hom Grp_pX1p2) => [[x y]] /=.
  case/eqP=> <- xp yp _ _; rewrite joing_idl joing_idr genS //.
  by rewrite subsetI subset_gen subUset !sub1set !inE xp yp!eqxx.
rewrite exponent_Ohm1_class2 ?card_pX1p2 ?odd_exp // nil_class2.
by have [[_ ->] _ ] := pX1p2_extraspecial.
Qed.

(* This is the uniqueness half of Aschbacher ex. (8.7)(1) *)
Lemma isog_pX1p2 (gT : finGroupType) (G : {group gT}) :
  extraspecial G -> exponent G %| p -> #|G| = (p ^ 3)%N -> G \isog p^{1+2}.
Proof.
move=> esG expGp oG; apply/(isoGrpP _ Grp_pX1p2).
rewrite card_pX1p2; split=> //.
have pG: p.-group G by rewrite /pgroup oG pnat_exp pnat_id.
have oZ := card_center_extraspecial pG esG.
have [x Gx notZx]: exists2 x, x \in G & x \notin 'Z(G).
  apply/subsetPn; rewrite proper_subn // properEcard center_sub oZ oG.
  by rewrite (ltn_exp2l 1 3).
have ox: #[x] = p.
  by apply: nt_prime_order; rewrite ?(exponentP expGp) ?(group1_contra notZx).
have [y Gy not_cxy]: exists2 y, y \in G & y \notin 'C[x].
  by apply/subsetPn; rewrite sub_cent1; rewrite inE Gx in notZx.
apply/existsP; exists (x, y) => /=; set z := [~ x, y].
have [[defPhiG defG'] _] := esG.
have Zz: z \in 'Z(G) by rewrite -defG' mem_commg.
have [Gz cGz] := setIP Zz; rewrite !xpair_eqE !(exponentP expGp) //.
have [_ nZG] := andP (center_normal G).
rewrite /commg /conjg !(centP cGz) // !mulKg mulVg !eqxx !andbT.
have sXY_G: <[x]> <*> <[y]> \subset G by rewrite join_subG !cycle_subG Gx.
have defZ: <[z]> = 'Z(G).
  apply/eqP; rewrite eqEcard cycle_subG Zz oZ /= -orderE.
  rewrite (nt_prime_order p_pr) ?(exponentP expGp) //.
  by rewrite (sameP commgP cent1P) cent1C.
have sZ_XY: 'Z(G) \subset <[x]> <*> <[y]>.
  by rewrite -defZ cycle_subG groupR // mem_gen // inE cycle_id ?orbT.
rewrite eqEcard sXY_G /= oG -(Lagrange sZ_XY) oZ leq_pmul2l //.
rewrite -card_quotient ?(subset_trans sXY_G) //.
rewrite quotientY ?quotient_cycle ?cycle_subG ?(subsetP nZG) //.
have abelGz: p.-abelem (G / 'Z(G)) by rewrite -defPhiG Phi_quotient_abelem.
have [cGzGz expGz] := abelemP p_pr abelGz.
rewrite cent_joinEr ?(sub_abelian_cent2 cGzGz) ?cycle_subG ?mem_quotient //.
have oZx: #|<[coset 'Z(G) x]>| = p.
  rewrite -orderE (nt_prime_order p_pr) ?expGz ?mem_quotient //.
  by apply: contra notZx; move/eqP=> Zx; rewrite coset_idr ?(subsetP nZG).
rewrite TI_cardMg ?oZx -?orderE ?(nt_prime_order p_pr) ?expGz ?mem_quotient //.
  apply: contra not_cxy; move/eqP=> Zy.
  rewrite -cent_cycle (subsetP _ y (coset_idr _ Zy)) ?(subsetP nZG) //.
  by rewrite subIset ?centS ?orbT ?cycle_subG.
rewrite prime_TIg ?oZx // cycle_subG; apply: contra not_cxy.
case/cycleP=> i; rewrite -morphX ?(subsetP nZG) // => /rcoset_kercosetP.
rewrite groupX ?(subsetP nZG) // cent1C => /(_ isT isT); apply: subsetP.
rewrite mul_subG ?sub1set ?groupX ?cent1id //= -cent_cycle subIset // orbC.
by rewrite centS ?cycle_subG.
Qed.

End ExponentPextraspecialTheory.

Section GeneralExponentPextraspecialTheory.

Variable p : nat.

Lemma pX1p2id : p^{1+2*1} \isog p^{1+2}.
Proof. exact: ncprod1. Qed.

Lemma pX1p2S n : xcprod_spec p^{1+2} p^{1+2*n} p^{1+2*n.+1}%type.
Proof. exact: ncprodS. Qed.

Lemma card_pX1p2n n : prime p -> #|p^{1+2*n}| = (p ^ n.*2.+1)%N.
Proof.
move=> p_pr; have pG := pX1p2_pgroup p_pr.
have oG := card_pX1p2 p_pr; have esG := pX1p2_extraspecial p_pr.
have oZ := card_center_extraspecial pG esG.
elim: n => [|n IHn]; first by rewrite (card_isog (ncprod0 _)) oZ.
case: pX1p2S => gz isoZ; rewrite -im_cpair cardMg_divn setI_im_cpair.
rewrite -injm_center ?{1}card_injm ?injm_cpairg1 ?injm_cpair1g ?center_sub //.
by rewrite oG oZ IHn -expnD mulKn ?prime_gt0.
Qed.

Lemma pX1p2n_pgroup n : prime p -> p.-group p^{1+2*n}.
Proof. by move=> p_pr; rewrite /pgroup card_pX1p2n // pnat_exp pnat_id. Qed.

(* This is part of the existence half of Aschbacher (23.13) *)
Lemma exponent_pX1p2n n : prime p -> odd p -> exponent p^{1+2*n} = p.
Proof.
move=> p_pr odd_p; apply: prime_nt_dvdP => //.
  rewrite -dvdn1 -trivg_exponent -cardG_gt1 card_pX1p2n //.
  by rewrite (ltn_exp2l 0) // prime_gt1.
elim: n => [|n IHn].
  by rewrite (dvdn_trans (exponent_dvdn _)) ?card_pX1p2n.
case: pX1p2S => gz isoZ; rewrite -im_cpair /=.
apply/exponentP=> xy; case/imset2P=> x y C1x C2y ->{xy}.
rewrite expgMn; last by red; rewrite -(centsP (im_cpair_cent isoZ)).
rewrite (exponentP _ y C2y) ?exponent_injm ?injm_cpair1g // mulg1.
by rewrite (exponentP _ x C1x) ?exponent_injm ?injm_cpairg1 // exponent_pX1p2.
Qed.

(* This is part of the existence half of Aschbacher (23.13) and (23.14) *)
Lemma pX1p2n_extraspecial n : prime p -> n > 0 -> extraspecial p^{1+2*n}.
Proof.
move=> p_pr; elim: n => [//|n IHn _].
have esG := pX1p2_extraspecial p_pr.
have [n0 | n_gt0] := posnP n.
  by apply: isog_extraspecial esG; rewrite isog_sym n0 pX1p2id.
case: pX1p2S (pX1p2n_pgroup n.+1 p_pr) => gz isoZ pGn.
apply: (cprod_extraspecial pGn (im_cpair_cprod isoZ) (setI_im_cpair isoZ)).
  by apply: injm_extraspecial esG; rewrite ?injm_cpairg1.
by apply: injm_extraspecial (IHn n_gt0); rewrite ?injm_cpair1g.
Qed.

(* This is Aschbacher (23.12) *)
Lemma Ohm1_extraspecial_odd (gT : finGroupType) (G : {group gT}) :
    p.-group G -> extraspecial G -> odd #|G| ->
 let Y := 'Ohm_1(G) in
  [/\ exponent Y = p, #|G : Y| %| p
    & Y != G ->
      exists E : {group gT},
        [/\ #|G : Y| = p, #|E| = p \/ extraspecial E,
            exists2 X : {group gT}, #|X| = p & X \x E = Y
          & exists M : {group gT},
             [/\ M \isog 'Mod_(p ^ 3), M \* E = G & M :&: E = 'Z(M)]]].
Proof.
move=> pG esG oddG Y; have [spG _] := esG.
have [defPhiG defG'] := spG; set Z := 'Z(G) in defPhiG defG'.
have{spG} expG: exponent G %| p ^ 2 by apply: exponent_special.
have p_pr := extraspecial_prime pG esG.
have p_gt1 := prime_gt1 p_pr; have p_gt0 := ltnW p_gt1.
have oZ: #|Z| = p := card_center_extraspecial pG esG.
have nsZG: Z <| G := center_normal G; have [sZG nZG] := andP nsZG.
have nsYG: Y <| G := Ohm_normal 1 G; have [sYG nYG] := andP nsYG.
have ntZ: Z != 1 by rewrite -cardG_gt1 oZ.
have sZY: Z \subset Y.
  by apply: contraR ntZ => ?; rewrite -(setIidPl sZG) TI_Ohm1 ?prime_TIg ?oZ.
have ntY: Y != 1 by apply: subG1_contra ntZ.
have p_odd: odd p by rewrite -oZ (oddSg sZG).
have expY: exponent Y %| p by rewrite exponent_Ohm1_class2 // nil_class2 defG'.
rewrite (prime_nt_dvdP p_pr _ expY) -?dvdn1 -?trivg_exponent //.
have [-> | neYG] := eqVneq Y G; first by rewrite indexgg dvd1n eqxx; split.
have sG1Z: 'Mho^1(G) \subset Z by rewrite -defPhiG (Phi_joing pG) joing_subr.
have Z_Gp: {in G, forall x, x ^+ p \in Z}.
  by move=> x Gx; rewrite /= (subsetP sG1Z) ?(Mho_p_elt 1) ?(mem_p_elt pG).
have{expG} oY': {in G :\: Y, forall u, #[u] = (p ^ 2)%N}.
  move=> u /setDP[Gu notYu]; apply/eqP.
  have [k ou] := p_natP (mem_p_elt pG Gu).
  rewrite eqn_dvd order_dvdn (exponentP expG) // eqxx ou dvdn_Pexp2l // ltnNge.
  apply: contra notYu => k_le_1; rewrite [Y](OhmE _ pG) mem_gen // !inE Gu /=.
  by rewrite -order_dvdn ou dvdn_exp2l.
have isoMod3 (M : {group gT}):
    M \subset G -> ~~ abelian M -> ~~ (M \subset Y) -> #|M| = (p ^ 3)%N ->
  M \isog 'Mod_(p ^ 3).
- move=> sMG not_cMM /subsetPn[u Mu notYu oM].
  have pM := pgroupS sMG pG; have sUM: <[u]> \subset M by rewrite cycle_subG.
  have Y'u: u \in G :\: Y by rewrite inE notYu (subsetP sMG).
  have iUM: #|M : <[u]>| = p by rewrite -divgS // oM expnS -(oY' u) ?mulnK.
  have cM := maximal_cycle_extremal pM not_cMM (cycle_cyclic u) sUM iUM.
  rewrite (sameP eqP (prime_oddPn p_pr)) p_odd orbF in cM.
  rewrite /extremal_class oM pdiv_pfactor // pfactorK //= in cM.
  by do 3!case: ifP => // _ in cM.
have iYG: #|G : Y| = p.
  have [V maxV sYV]: {V : {group gT} | maximal V G & Y \subset V}.
    by apply: maxgroup_exists; rewrite properEneq neYG.
  have [sVG [u Gu notVu]] := properP (maxgroupp maxV).
  without loss [v Vv notYv]: / exists2 v, v \in V & v \notin Y.
    have [->| ] := eqVneq Y V; first by rewrite (p_maximal_index pG).
    by rewrite eqEsubset sYV => not_sVY; apply; apply/subsetPn.
  pose U := <[u]> <*> <[v]>; have Gv := subsetP sVG v Vv.
  have sUG: U \subset G by rewrite join_subG !cycle_subG Gu.
  have Uu: u \in U by rewrite -cycle_subG joing_subl.
  have Uv: v \in U by rewrite -cycle_subG joing_subr.
  have not_sUY: ~~ (U \subset Y) by apply/subsetPn; exists v.
  have sU1U: 'Ohm_1(U) \subset U := Ohm_sub 1 _.
  have sU1Y: 'Ohm_1(U) \subset Y := OhmS 1 sUG.
  suffices defUV: U :&: V = 'Ohm_1(U).
    by rewrite (subsetP sU1Y) // -defUV inE Uv in notYv.
  suffices iU1U: #|U : 'Ohm_1(U)| = p.
    have: maximal 'Ohm_1(U) U by rewrite p_index_maximal ?Ohm_sub ?iU1U.
    case/maxgroupP=> _; apply; rewrite /= -/U.
      by apply/properP; split; last exists u; rewrite ?subsetIl ?inE ?Uu.
    by rewrite subsetI Ohm_sub (subset_trans sU1Y).
  apply/prime_nt_dvdP=> //.
    by apply: contra not_sUY; rewrite /U; move/eqP; move/(index1g sU1U)=> <-.
  have ov: #[v] = (p ^ 2)%N by rewrite oY' // inE notYv.
  have sZv: Z \subset <[v]>.
    suffices defZ: <[v ^+ p]> == Z by rewrite -(eqP defZ) cycleX.
    by rewrite eqEcard cycle_subG Z_Gp //= oZ -orderE (orderXexp 1 ov).
  have nvG: G \subset 'N(<[v]>) by rewrite sub_der1_norm ?cycle_subG // defG'.
  have [cUU | not_cUU] := orP (orbN (abelian U)).
    rewrite -divgS ?Ohm_sub // -(mul_card_Ohm_Mho_abelian 1 cUU) /= -/U.
    by rewrite mulKn ?cardG_gt0 //= -oZ cardSg ?(subset_trans (MhoS 1 sUG)).
  have oU: #|U| = (p ^ 3)%N.
    have nvu := subsetP nvG u Gu; have nvU := subset_trans sUG nvG.
    rewrite -(Lagrange (joing_subr _ _)) -orderE ov mulnC; congr (_ * _)%N.
    rewrite -card_quotient //= quotientYidr ?cycle_subG //=.
    rewrite quotient_cycle // -orderE; apply: nt_prime_order => //.
      by rewrite -morphX //= coset_id // (subsetP sZv) // Z_Gp.
    have svV: <[v]> \subset V by rewrite cycle_subG.
    by apply: contra notVu; move/eqP=> v_u; rewrite (subsetP svV) // coset_idr.
  have isoU := isoMod3 _ sUG not_cUU not_sUY oU; rewrite /= -/U in isoU.
  have [//|[x y] genU modU] := generators_modular_group p_pr _ isoU.
  case/modular_group_structure: genU => // _ _ _ _.
  case: eqP (p_odd) => [[-> //] | _ _]; case/(_ 1%N)=> // _ oU1.
  by rewrite -divgS // oU oU1 mulnK // muln_gt0 p_gt0.
have iC1U (U : {group gT}) x:
  U \subset G -> x \in G :\: 'C(U) -> #|U : 'C_U[x]| = p.
- move=> sUG /setDP[Gx not_cUx]; apply/prime_nt_dvdP=> //.
    apply: contra not_cUx; rewrite -sub_cent1 => /eqP sUCx.
    by rewrite -(index1g _ sUCx) ?subsetIl ?subsetIr.
  rewrite -(@dvdn_pmul2l (#|U| * #|'C_G[x]|)) ?muln_gt0 ?cardG_gt0 //.
  have maxCx: maximal 'C_G[x] G.
    rewrite cent1_extraspecial_maximal //; apply: contra not_cUx.
    by rewrite inE Gx; apply: subsetP (centS sUG) _.
  rewrite {1}mul_cardG setIA (setIidPl sUG) -(p_maximal_index pG maxCx) -!mulnA.
  rewrite !Lagrange ?subsetIl // mulnC dvdn_pmul2l //.
  have [sCxG nCxG] := andP (p_maximal_normal pG maxCx).
  by rewrite -norm_joinEl ?cardSg ?join_subG ?(subset_trans sUG).
have oCG (U : {group gT}):
  Z \subset U -> U \subset G -> #|'C_G(U)| = (p * #|G : U|)%N.
- elim: {U}_.+1 {-2}U (ltnSn #|U|) => // m IHm U leUm sZU sUG.
  have [<- | neZU] := eqVneq Z U.
    by rewrite -oZ Lagrange // (setIidPl _) // centsC subsetIr.
  have{neZU} [x Gx not_cUx]: exists2 x, x \in G & x \notin 'C(U).
    by apply/subsetPn; rewrite eqEsubset sZU subsetI sUG centsC in neZU.
  pose W := 'C_U[x]; have iWU: #|U : W| = p by rewrite iC1U // inE not_cUx.
  have maxW: maximal W U by rewrite p_index_maximal ?subsetIl ?iWU.
  have ltWU: W \proper U by apply: maxgroupp maxW.
  have [sWU [u Uu notWu]] := properP ltWU.
  have defU: W * <[u]> = U.
    have nsWU: W <| U := p_maximal_normal (pgroupS sUG pG) maxW.
    by rewrite (mulg_normal_maximal nsWU) ?cycle_subG.
  have sWG := subset_trans sWU sUG.
  have sZW: Z \subset W.
    by rewrite subsetI sZU -cent_set1 subIset ?centS ?orbT ?sub1set.
  have iCW_CU: #|'C_G(W) : 'C_G(U)| = p.
    rewrite -defU centM cent_cycle setIA /= -/W.
    rewrite iC1U ?subsetIl ?setIS ?centS // inE andbC (subsetP sUG) //=.
    rewrite -sub_cent1; apply/subsetPn; exists x.
      by rewrite inE Gx -sub_cent1 subsetIr.
    by rewrite -defU centM cent_cycle inE -sub_cent1 subsetIr in not_cUx.
  apply/eqP; rewrite -(eqn_pmul2r p_gt0) -{1}iCW_CU Lagrange ?setIS ?centS //.
  rewrite IHm ?(leq_trans (proper_card ltWU)) //= -/W.
  by rewrite -(Lagrange_index sUG sWU) iWU mulnA.
have oCY: #|'C_G(Y)| = (p ^ 2)%N by rewrite oCG // iYG.
have [x cYx notZx]: exists2 x, x \in 'C_G(Y) & x \notin Z.
  apply/subsetPn; rewrite proper_subn // properEcard setIS ?centS //=.
  by rewrite oZ oCY (ltn_exp2l 1 2).
have{cYx} [Gx cYx] := setIP cYx; have nZx := subsetP nZG x Gx.
have defCx: 'C_G[x] = Y.
  apply/eqP; rewrite eq_sym eqEcard subsetI sYG sub_cent1 cYx /=.
  rewrite -(leq_pmul2r p_gt0) -{2}iYG -(iC1U G x) ?Lagrange ?subsetIl //.
  by rewrite !inE Gx ?andbT in notZx *.
have Yx: x \in Y by rewrite -defCx inE Gx cent1id.
have ox: #[x] = p.
  by apply: nt_prime_order; rewrite ?(exponentP expY) // (group1_contra notZx).
have defCy: 'C_G(Y) = Z * <[x]>.
  apply/eqP; rewrite eq_sym eqEcard mulG_subG setIS ?centS //=.
  rewrite cycle_subG inE Gx cYx oCY TI_cardMg ?oZ -?orderE ?ox //=.
  by rewrite setIC prime_TIg -?orderE ?ox ?cycle_subG.
have abelYt: p.-abelem (Y / Z).
  by rewrite (abelemS (quotientS _ sYG)) //= -/Z -defPhiG Phi_quotient_abelem.
have Yxt: coset Z x \in Y / Z by rewrite mem_quotient.
have{Yxt} [Et [sEtYt oEt defYt]] := p_abelem_split1 abelYt Yxt.
have nsZY: Z <| Y := normalS sZY sYG nsZG.
have [E defEt sZE sEY] := inv_quotientS nsZY sEtYt.
have{defYt} [_ defYt _ tiXEt] := dprodP defYt.
have defY: <[x]> \x E = Y.
  have nZX: <[x]> \subset 'N(Z) by rewrite cycle_subG.
  have TIxE: <[x]> :&: E = 1.
    rewrite prime_TIg -?orderE ?ox // -(quotientSGK _ sZE) ?quotient_cycle //.
    rewrite (sameP setIidPl eqP) eq_sym -defEt tiXEt -quotient_cycle //.
    by rewrite -subG1 quotient_sub1 // cycle_subG.
  rewrite dprodE //; last 1 first.
    by rewrite cent_cycle (subset_trans sEY) //= -/Y -defCx subsetIr.
  rewrite -[Y](quotientGK nsZY) -defYt cosetpreM -quotient_cycle //.
  rewrite quotientK // -(normC nZX) defEt quotientGK ?(normalS _ sEY) //.
  by rewrite -mulgA (mulSGid sZE).
have sEG := subset_trans sEY sYG; have nZE := subset_trans sEG nZG.
have defZE: 'Z(E) = Z.
  apply/eqP; rewrite eqEsubset andbC subsetI sZE subIset ?centS ?orbT //.
  rewrite -quotient_sub1 ?subIset ?nZE //= -tiXEt defEt subsetI andbC.
  rewrite quotientS ?center_sub //= -quotient_cycle //.
  rewrite -(quotientMidl _ <[x]>) /= -defCy quotientS // /Y.
  by case/dprodP: defY => _ <- _ _; rewrite centM setIA cent_cycle defCx setSI.
have pE := pgroupS sEG pG.
rewrite iYG; split=> // _; exists E.
split=> //; first 2 [by exists [group of <[x]>]].
  have:= sZE; rewrite subEproper; case/predU1P=> [<- | ltZE]; [by left | right].
  split; rewrite /special defZE ?oZ // (Phi_joing pE).
  have defE': E^`(1) = Z.
    have sE'Z: E^`(1) \subset Z by rewrite -defG' dergS.
    apply/eqP; rewrite eqEcard sE'Z -(prime_nt_dvdP _ _ (cardSg sE'Z)) ?oZ //=.
    rewrite -trivg_card1 (sameP eqP commG1P).
    by rewrite /proper sZE /= -/Z -defZE subsetI subxx in ltZE.
  split=> //; rewrite -defE'; apply/joing_idPl.
  by rewrite /= defE' -defPhiG (Phi_joing pG) joingC sub_gen ?subsetU ?MhoS.
have iEG: #|G : E| = (p ^ 2)%N.
  apply/eqP; rewrite -(@eqn_pmul2l #|E|) // Lagrange // -(Lagrange sYG) iYG.
  by rewrite -(dprod_card defY) -mulnA mulnCA -orderE ox.
pose M := 'C_G(E); exists [group of M] => /=.
have sMG: M \subset G := subsetIl _ _; have pM: p.-group M := pgroupS sMG pG.
have sZM: Z \subset M by rewrite setIS ?centS.
have oM: #|M| = (p ^ 3)%N by rewrite oCG ?iEG.
have defME: M * E = G.
  apply/eqP; rewrite eqEcard mulG_subG sMG sEG /= -(leq_pmul2r p_gt0).
  rewrite -{2}oZ -defZE /('Z(E)) -{2}(setIidPr sEG) setIAC -mul_cardG /= -/M.
  by rewrite -(Lagrange sEG) mulnAC -mulnA mulnC iEG oM.
have defZM: 'Z(M) = Z.
  apply/eqP; rewrite eqEsubset andbC subsetI sZM subIset ?centS ?orbT //=.
  by rewrite /Z /('Z(G)) -{2}defME centM setIA setIAC.
rewrite cprodE 1?centsC ?subsetIr //.
rewrite defME setIAC (setIidPr sEG) defZM isoMod3 //.
  rewrite abelianE (sameP setIidPl eqP) eqEcard subsetIl /= -/('Z(M)) -/M.
  by rewrite defZM oZ oM (leq_exp2l 3 1).
by apply: contra neYG => sMY; rewrite eqEsubset sYG -defME mulG_subG sMY.
Qed.

(* This is the uniqueness half of Aschbacher (23.13); the proof incorporates *)
(* in part the proof that symplectic spaces are hyperbolic (19.16).          *)
Lemma isog_pX1p2n n (gT : finGroupType) (G : {group gT}) :
    prime p -> extraspecial G -> #|G| = (p ^ n.*2.+1)%N -> exponent G %| p ->
  G \isog p^{1+2*n}.
Proof.
move=> p_pr esG oG expG; have p_gt1 := prime_gt1 p_pr.
have not_le_p3_p: ~~ (p ^ 3 <= p) by rewrite (leq_exp2l 3 1).
have pG: p.-group G by rewrite /pgroup oG pnat_exp pnat_id.
have oZ := card_center_extraspecial pG esG.
have{pG esG} [Es p3Es defG] := extraspecial_structure pG esG.
set Z := 'Z(G) in oZ defG p3Es.
elim: Es {+}G => [|E Es IHs] S in n oG expG p3Es defG *.
  rewrite big_nil cprod1g in defG; rewrite -defG.
  have ->: n = 0%N.
    apply: double_inj; apply/eqP.
    by rewrite -eqSS -(eqn_exp2l _ _ p_gt1) -oG -defG oZ.
  by rewrite isog_cyclic_card prime_cyclic ?oZ ?card_pX1p2n //=.
rewrite big_cons -cprodA in defG; rewrite /= -andbA in p3Es.
have [[_ T _ defT] defET cTE] := cprodP defG; rewrite defT in defET cTE defG.
case/and3P: p3Es; move/eqP=> oE; move/eqP=> defZE; move/IHs=> {IHs}IHs.
have not_cEE: ~~ abelian E.
  by apply: contra not_le_p3_p => cEE; rewrite -oE -oZ -defZE (center_idP _).
have sES: E \subset S by rewrite -defET mulG_subl.
have sTS: T \subset S by rewrite -defET mulG_subr.
have expE: exponent E %| p by apply: dvdn_trans (exponentS sES) expG.
have expT: exponent T %| p by apply: dvdn_trans (exponentS sTS) expG.
have{expE not_cEE} isoE: E \isog p^{1+2}.
  apply: isog_pX1p2 => //.
  by apply: card_p3group_extraspecial p_pr oE _; rewrite defZE.
have sZT: 'Z(E) \subset T.
  by case/cprodP: defT => [[U _ -> _] <- _]; rewrite defZE mulG_subr.
case def_n: n => [|n'].
  case/negP: not_le_p3_p; rewrite def_n in oG; rewrite -oE -[p]oG.
  exact: subset_leq_card.
have zI_ET: E :&: T = 'Z(E).
  by apply/eqP; rewrite eqEsubset subsetI sZT subsetIl setIS // centsC.
have{n def_n oG} oT: #|T| = (p ^ n'.*2.+1)%N.
  apply/eqP; rewrite -(eqn_pmul2l (cardG_gt0 E)) mul_cardG zI_ET defET.
  by rewrite defZE oE oG oZ -expnSr -expnD def_n.
have{IHs oT expT defT Es} isoT: T \isog p^{1+2*n'} by rewrite IHs.
case: pX1p2S => gz isoZ; rewrite (isog_cprod_by _ defG) //.
exact: Aut_extraspecial_full (pX1p2_pgroup p_pr) (pX1p2_extraspecial p_pr).
Qed.

End GeneralExponentPextraspecialTheory.

Lemma isog_2X1p2 : 2^{1+2} \isog 'D_8.
Proof.
have pr2: prime 2 by []; have oG := card_pX1p2 pr2; rewrite -[8]oG.
case/existsP: (isoGrp_hom (Grp_pX1p2 pr2)) => [[x y]] /=.
rewrite -/2^{1+2}; case/eqP=> defG x2 y2 _ _.
have not_oG_2: ~~ (#|2^{1+2}| %| 2) by rewrite oG.
have ox: #[x] = 2.
  apply: nt_prime_order => //; apply: contra not_oG_2 => x1.
  by rewrite -defG (eqP x1) cycle1 joing1G order_dvdn y2.
have oy: #[y] = 2.
  apply: nt_prime_order => //; apply: contra not_oG_2 => y1.
  by rewrite -defG (eqP y1) cycle1 joingG1 order_dvdn x2.
rewrite -defG joing_idl joing_idr involutions_gen_dihedral //.
apply: contra not_oG_2 => eq_xy; rewrite -defG (eqP eq_xy) (joing_idPl _) //.
by rewrite -orderE oy.
Qed.

Lemma Q8_extraspecial : extraspecial 'Q_8.
Proof.
have gt32: 3 > 2 by []; have isoQ: 'Q_8 \isog 'Q_(2 ^ 3) by apply: isog_refl.
have [[x y] genQ _] := generators_quaternion gt32 isoQ.
have [_ [defQ' defPhiQ _ _]] := quaternion_structure gt32 genQ isoQ.
case=> defZ oZ _ _ _ _ _; split; last by rewrite oZ.
by split; rewrite ?defPhiQ defZ.
Qed.

Lemma DnQ_P n : xcprod_spec 'D^n 'Q_8 ('D^n*Q)%type.
Proof.
have pQ: 2.-group 'Q_(2 ^ 3) by rewrite /pgroup card_quaternion.
have{pQ} oZQ := card_center_extraspecial pQ Q8_extraspecial.
suffices oZDn: #|'Z('D^n)| = 2.
  by apply: xcprodP; rewrite isog_cyclic_card ?prime_cyclic ?oZQ ?oZDn.
have [-> | n_gt0] := posnP n; first by rewrite center_ncprod0 card_pX1p2n.
have pr2: prime 2 by []; have pDn := pX1p2n_pgroup n pr2.
exact: card_center_extraspecial (pX1p2n_extraspecial pr2 n_gt0).
Qed.

Lemma card_DnQ n : #|'D^n*Q| = (2 ^ n.+1.*2.+1)%N.
Proof.
have oQ: #|'Q_(2 ^ 3)| = 8 by rewrite card_quaternion.
have pQ: 2.-group 'Q_8 by rewrite /pgroup oQ.
case: DnQ_P => gz isoZ.
rewrite -im_cpair cardMg_divn setI_im_cpair cpair_center_id.
rewrite -injm_center 3?{1}card_injm ?injm_cpairg1 ?injm_cpair1g ?center_sub //.
rewrite oQ card_pX1p2n // (card_center_extraspecial pQ Q8_extraspecial).
by rewrite -muln_divA // mulnC -(expnD 2 2).
Qed.

Lemma DnQ_pgroup n : 2.-group 'D^n*Q.
Proof. by rewrite /pgroup card_DnQ pnat_exp. Qed.

(* Final part of the existence half of Aschbacher (23.14). *)
Lemma DnQ_extraspecial n : extraspecial 'D^n*Q.
Proof.
case: DnQ_P (DnQ_pgroup n) => gz isoZ pDnQ.
have [injDn injQ] := (injm_cpairg1 isoZ, injm_cpair1g isoZ).
have [n0 | n_gt0] := posnP n.
  rewrite -im_cpair mulSGid; first exact: injm_extraspecial Q8_extraspecial.
  apply/setIidPl; rewrite setI_im_cpair -injm_center //=.
  by congr (_ @* _); rewrite n0 center_ncprod0.
apply: (cprod_extraspecial pDnQ (im_cpair_cprod isoZ) (setI_im_cpair _)).
  exact: injm_extraspecial (pX1p2n_extraspecial _ _).
exact: injm_extraspecial Q8_extraspecial.
Qed.

(* A special case of the uniqueness half of Achsbacher (23.14). *)
Lemma card_isog8_extraspecial (gT : finGroupType) (G : {group gT}) :
  #|G| = 8 -> extraspecial G -> (G \isog 'D_8) || (G \isog 'Q_8).
Proof.
move=> oG esG; have pG: 2.-group G by rewrite /pgroup oG.
apply/norP=> [[notG_D8 notG_Q8]].
have not_extG: extremal_class G = NotExtremal.
  by rewrite /extremal_class oG andFb (negPf notG_D8) (negPf notG_Q8).
have [x Gx ox] := exponent_witness (pgroup_nil pG).
pose X := <[x]>; have cycX: cyclic X := cycle_cyclic x.
have sXG: X \subset G by rewrite cycle_subG.
have iXG: #|G : X| = 2.
  by rewrite -divgS // oG -orderE -ox exponent_2extraspecial.
have not_cGG := extraspecial_nonabelian esG.
have:= maximal_cycle_extremal pG not_cGG cycX sXG iXG.
by rewrite /extremal2 not_extG.
Qed.

(* The uniqueness half of Achsbacher (23.14). The proof incorporates in part  *)
(* the proof that symplectic spces are hyperbolic (Aschbacher (19.16)), and   *)
(* the determination of quadratic spaces over 'F_2 (21.2); however we use     *)
(* the second part of exercise (8.4) to avoid resorting to Witt's lemma and   *)
(* Galois theory as in (20.9) and (21.1).                                     *)
Lemma isog_2extraspecial (gT : finGroupType) (G : {group gT}) n :
  #|G| = (2 ^ n.*2.+1)%N -> extraspecial G -> G \isog 'D^n \/ G \isog 'D^n.-1*Q.
Proof.
elim: n G => [|n IHn] G oG esG.
  case/negP: (extraspecial_nonabelian esG).
  by rewrite cyclic_abelian ?prime_cyclic ?oG.
have pG: 2.-group G by rewrite /pgroup oG pnat_exp.
have oZ:= card_center_extraspecial pG esG.
have: 'Z(G) \subset 'Ohm_1(G).
  apply/subsetP=> z Zz; rewrite (OhmE _ pG) mem_gen //.
  by rewrite !inE -order_dvdn -oZ order_dvdG ?(subsetP (center_sub G)).
rewrite subEproper; case/predU1P=> [defG1 | ltZG1].
  have [n' n'_gt2 isoG]: exists2 n', n' > 2 & G \isog 'Q_(2 ^ n').
    apply/quaternion_classP; apply/eqP.
    have not_cycG: ~~ cyclic G.
      by apply: contra (extraspecial_nonabelian esG); apply: cyclic_abelian.
    move: oZ; rewrite defG1; move/prime_Ohm1P; rewrite (negPf not_cycG) /=.
    by apply=> //; apply: contra not_cycG; move/eqP->; apply: cyclic1.
  have [n0 n'3]: n = 0%N /\ n' = 3.
    have [[x y] genG _] := generators_quaternion n'_gt2 isoG.
    have n'3: n' = 3.
      have [_ [_ _ oG' _] _ _ _] := quaternion_structure n'_gt2 genG isoG.
      apply/eqP; rewrite -(subnKC (ltnW n'_gt2)) subn2 !eqSS -(@eqn_exp2l 2) //.
      by rewrite -oG' -oZ; case: esG => [[_ ->]].
    by move/eqP: oG; have [-> _ _ _] := genG; rewrite n'3 eqn_exp2l //; case n.
  right; rewrite (isog_trans isoG) // n'3 n0 /=.
  case: DnQ_P => z isoZ; rewrite -im_cpair mulSGid ?sub_isog ?injm_cpair1g //.
  apply/setIidPl; rewrite setI_im_cpair -injm_center ?injm_cpairg1 //.
  by rewrite center_ncprod0.
case/andP: ltZG1 => _; rewrite (OhmE _ pG) gen_subG.
case/subsetPn=> x; case/LdivP=> Gx x2 notZx.
have ox: #[x] = 2 by apply: nt_prime_order (group1_contra notZx).
have Z'x: x \in G :\: 'Z(G) by rewrite inE notZx.
have [E [R [[oE oR] [defG ziER]]]] := split1_extraspecial pG esG Z'x.
case=> defZE defZR [esE Ex] esR.
have isoE: E \isog 2^{1+2}.
  apply: isog_trans (isog_symr isog_2X1p2).
  case/orP: (card_isog8_extraspecial oE esE) => // isoE; case/negP: notZx.
  have gt32: 3 > 2 by [].
  have [[y z] genE _] := generators_quaternion gt32 isoE.
  have [_ _ [defZx _ eq_y2 _ _] _ _] := quaternion_structure gt32 genE isoE.
  by rewrite (eq_y2 x) // -cycle_subG -defZx defZE.
rewrite oG doubleS 2!expnS divnMl ?mulKn // in oR.
case: ifP esR => [_ defR | _ esR].
  have ->: n = 0%N by move/eqP: oR; rewrite defR oZ (eqn_exp2l 1) //; case n.
  left; apply: isog_trans (isog_symr (ncprod1 _)).
  by rewrite -defG defR -defZE cprod_center_id.
have AutZin2_1p2: Aut_in (Aut 2^{1+2}) 'Z(2^{1+2}) \isog Aut 'Z(2^{1+2}).
  exact: Aut_extraspecial_full (pX1p2_pgroup _) (pX1p2_extraspecial _).
have [isoR | isoR] := IHn R oR esR.
  by left; case: pX1p2S => gz isoZ; rewrite (isog_cprod_by _ defG).
have n_gt0: n > 0.
  have pR: 2.-group R by rewrite /pgroup oR pnat_exp.
  have:= min_card_extraspecial pR esR.
  by rewrite oR leq_exp2l // ltnS (leq_double 1).
case: DnQ_P isoR => gR isoZR /=; rewrite isog_sym; case/isogP=> fR injfR im_fR.
have [injDn injQ] := (injm_cpairg1 isoZR, injm_cpair1g isoZR).
pose Dn1 := cpairg1 isoZR @* 'D^n.-1; pose Q := cpair1g isoZR @* 'Q_8.
have defR: fR @* Dn1 \* fR @* Q = R.
  rewrite cprodE ?morphim_cents ?im_cpair_cent //.
  by rewrite -morphimMl ?subsetT ?im_cpair.
rewrite -defR cprodA in defG.
have [[Dn _ defDn _] _ _] := cprodP defG; rewrite defDn in defG.
have isoDn: Dn \isog 'D^n.
  rewrite -(prednK n_gt0); case: pX1p2S => gz isoZ.
  rewrite (isog_cprod_by _ defDn) //; last 1 first.
    by rewrite isog_sym (isog_trans _ (sub_isog _ _)) ?subsetT // sub_isog.
  rewrite /= -morphimIim im_fR setIA ziER; apply/setIidPl.
  rewrite defZE -defZR -{1}im_fR -injm_center // morphimS //.
  by rewrite -cpairg1_center morphimS // center_sub.
right; case: DnQ_P => gz isoZ; rewrite (isog_cprod_by _ defG) //; first 1 last.
- exact: Aut_extraspecial_full (pX1p2n_pgroup _ _) (pX1p2n_extraspecial _ _).
- by rewrite isog_sym (isog_trans _ (sub_isog _ _)) ?subsetT // sub_isog.
rewrite /= -morphimIim; case/cprodP: defDn => _ defDn cDn1E.
rewrite setICA setIA -defDn -group_modr ?morphimS ?subsetT //.
rewrite /= im_fR (setIC R) ziER -center_prod // defZE -defZR.
rewrite mulSGid /=; last first.
  by rewrite -{1}im_fR -injm_center // -cpairg1_center !morphimS ?center_sub.
rewrite -injm_center ?subsetT // -injmI // setI_im_cpair.
by rewrite -injm_center // cpairg1_center injm_center // im_fR mulGid.
Qed.

(* The first concluding remark of Aschbacher (23.14). *)
Lemma rank_Dn n : 'r_2('D^n) = n.+1.
Proof.
elim: n => [|n IHn]; first by rewrite p_rank_abelem ?prime_abelem ?card_pX1p2n.
have oDDn: #|'D^n.+1| = (2 ^ n.+1.*2.+1)%N by apply: card_pX1p2n.
have esDDn: extraspecial 'D^n.+1 by apply: pX1p2n_extraspecial.
do [case: pX1p2S => gz isoZ; set DDn := [set: _]] in oDDn esDDn *.
have pDDn: 2.-group DDn by rewrite /pgroup oDDn pnat_exp.
apply/eqP; rewrite eqn_leq; apply/andP; split.
  have [E EprE]:= p_rank_witness 2 [group of DDn].
  have [sEDDn abelE <-] := pnElemP EprE; have [pE cEE _]:= and3P abelE.
  rewrite -(@leq_exp2l 2) // -p_part part_pnat_id // -leq_sqr -expnM -mulnn.
  rewrite muln2 doubleS expnS -oDDn -(@leq_pmul2r #|'C_DDn(E)|) ?cardG_gt0 //.
  rewrite {1}(card_subcent_extraspecial pDDn) // mulnCA -mulnA Lagrange //=.
  rewrite mulnAC mulnA leq_pmul2r ?cardG_gt0 // setTI.
  have ->: (2 * #|'C(E)| = #|'Z(DDn)| * #|'C(E)|)%N.
    by rewrite (card_center_extraspecial pDDn).
  by rewrite leq_mul ?subset_leq_card ?subsetIl.
have [inj1 injn] := (injm_cpairg1 isoZ, injm_cpair1g isoZ).
pose D := cpairg1 isoZ @* 2^{1+2}; pose Dn := cpair1g isoZ @* 'D^n.
have [E EprE] := p_rank_witness 2 [group of Dn].
rewrite injm_p_rank //= IHn in EprE; have [sEDn abelE dimE]:= pnElemP EprE.
have [x [Dx ox] notDnx]: exists x, [/\ x \in D, #[x] = 2 & x \notin Dn].
  have isoD: D \isog 'D_(2 ^ 3).
    by rewrite isog_sym -(isog_transl _ isog_2X1p2) sub_isog.
  have [//| [x y] genD [oy _]] := generators_2dihedral _ isoD.
  have [_ _ _ X'y] := genD; case/setDP: X'y; rewrite /= -/D => Dy notXy.
  exists y; split=> //; apply: contra notXy => Dny.
  case/dihedral2_structure: genD => // _ _ _ _ [defZD _ _ _ _].
  by rewrite (subsetP (cycleX x 2)) // -defZD -setI_im_cpair inE Dy.
have def_xE: <[x]> \x E = <[x]> <*> E.
  rewrite dprodEY ?prime_TIg -?orderE ?ox //.
    by rewrite (centSS sEDn _ (im_cpair_cent _)) ?cycle_subG.
  by rewrite cycle_subG (contra (subsetP sEDn x)).
apply/p_rank_geP; exists (<[x]> <*> E)%G.
rewrite 2!inE subsetT (dprod_abelem _ def_xE) abelE -(dprod_card def_xE).
by rewrite prime_abelem -?orderE ?ox //= lognM ?cardG_gt0 ?dimE.
Qed.

(* The second concluding remark of Aschbacher (23.14). *)
Lemma rank_DnQ n : 'r_2('D^n*Q) = n.+1.
Proof.
have pDnQ: 2.-group 'D^n*Q := DnQ_pgroup n.
have esDnQ: extraspecial 'D^n*Q := DnQ_extraspecial n.
do [case: DnQ_P => gz isoZ; set DnQ := setT] in pDnQ esDnQ *.
suffices [E]: exists2 E, E \in 'E*_2(DnQ) & logn 2 #|E| = n.+1.
  by rewrite (pmaxElem_extraspecial pDnQ esDnQ); case/pnElemP=> _ _ <-.
have oZ: #|'Z(DnQ)| = 2 by apply: card_center_extraspecial.
pose Dn := cpairg1 isoZ @* 'D^n; pose Q := cpair1g isoZ @* 'Q_8.
have [injDn injQ] := (injm_cpairg1 isoZ, injm_cpair1g isoZ).
have [E EprE]:= p_rank_witness 2 [group of Dn].
have [sEDn abelE dimE] := pnElemP EprE; have [pE cEE eE]:= and3P abelE.
rewrite injm_p_rank // rank_Dn in dimE; exists E => //.
have sZE: 'Z(DnQ) \subset E.
  have maxE := subsetP (p_rankElem_max _ _) E EprE.
  have abelZ: 2.-abelem 'Z(DnQ) by rewrite prime_abelem ?oZ.
  rewrite -(Ohm1_id abelZ) (OhmE _ (abelem_pgroup abelZ)) gen_subG.
  rewrite -(pmaxElem_LdivP _ maxE) // setSI //=.
  by rewrite -cpairg1_center injm_center // setIS ?centS.
have scE: 'C_Dn(E) = E.
  apply/eqP; rewrite eq_sym eqEcard subsetI sEDn -abelianE cEE /=.
  have [n0 | n_gt0] := posnP n.
    rewrite subset_leq_card // subIset // (subset_trans _ sZE) //.
    by rewrite -cpairg1_center morphimS // n0 center_ncprod0.
  have pDn: 2.-group Dn by rewrite morphim_pgroup ?pX1p2n_pgroup.
  have esDn: extraspecial Dn.
    exact: injm_extraspecial (pX1p2n_extraspecial _ _).
  rewrite dvdn_leq ?cardG_gt0 // (card_subcent_extraspecial pDn) //=.
  rewrite -injm_center // cpairg1_center (setIidPl sZE) oZ.
  rewrite -(dvdn_pmul2l (cardG_gt0 E)) mulnn mulnCA Lagrange //.
  rewrite card_injm ?card_pX1p2n // -expnS pfactor_dvdn ?expn_gt0 ?cardG_gt0 //.
  by rewrite lognX dimE mul2n.
apply/pmaxElemP; split=> [|F E2F sEF]; first by rewrite inE subsetT abelE.
have{E2F} [_ abelF] := pElemP E2F; have [pF cFF eF] := and3P abelF.
apply/eqP; rewrite eqEsubset sEF andbT; apply/subsetP=> x Fx.
have DnQx: x \in Dn * Q by rewrite im_cpair inE.
have{DnQx} [y z Dn_y Qz def_x]:= imset2P DnQx.
have{Dn_y} Ey: y \in E.
  have cEz: z \in 'C(E).
    by rewrite (subsetP (centS sEDn)) // (subsetP (im_cpair_cent _)).
  rewrite -scE inE Dn_y -(groupMr _ cEz) -def_x (subsetP (centS sEF)) //.
  by rewrite (subsetP cFF).
rewrite def_x groupMl // (subsetP sZE) // -cpair1g_center injm_center //= -/Q.
have: z \in 'Ohm_1(Q).
  rewrite (OhmE 1 (pgroupS (subsetT Q) pDnQ)) mem_gen // !inE Qz /=.
  rewrite -[z](mulKg y) -def_x (exponentP eF) ?groupM //.
  by rewrite groupV (subsetP sEF).
have isoQ: Q \isog 'Q_(2 ^ 3) by rewrite isog_sym sub_isog.
have [//|[u v] genQ _] := generators_quaternion _ isoQ.
by case/quaternion_structure: genQ => // _ _ [-> _ _ [-> _] _] _ _.
Qed.

(* The final concluding remark of Aschbacher (23.14). *)
Lemma not_isog_Dn_DnQ n : ~~ ('D^n \isog 'D^n.-1*Q).
Proof.
case: n => [|n] /=; first by rewrite isogEcard card_pX1p2n // card_DnQ andbF.
apply: contraL (leqnn n.+1) => isoDn1DnQ.
by rewrite -ltnNge -rank_Dn (isog_p_rank isoDn1DnQ) rank_DnQ.
Qed.
