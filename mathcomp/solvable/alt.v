(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun eqtype ssrnat seq div fintype tuple.
From mathcomp
Require Import tuple bigop prime finset fingroup morphism perm automorphism.
From mathcomp
Require Import quotient action cyclic pgroup gseries sylow primitive_action.

(******************************************************************************)
(*  Definitions of the symmetric and alternate groups, and some properties.   *)
(*     'Sym_T == The symmetric group over type T (which must have a finType   *)
(*               structure).                                                  *)
(*            := [set: {perm T}]                                              *)
(*     'Alt_T == The alternating group over type T.                           *)
(******************************************************************************)

Unset Printing Implicit Defensive.
Set Implicit Arguments.
Unset Strict Implicit.

Import GroupScope.

Definition bool_groupMixin := FinGroup.Mixin addbA addFb addbb.
Canonical bool_baseGroup := Eval hnf in BaseFinGroupType bool bool_groupMixin.
Canonical boolGroup := Eval hnf in FinGroupType addbb.

Section SymAltDef.

Variable T : finType.
Implicit Types (s : {perm T}) (x y z : T).

(** Definitions of the alternate groups and some Properties **)
Definition Sym of phant T : {set {perm T}} := setT.

Canonical Sym_group phT := Eval hnf in [group of Sym phT].

Local Notation "'Sym_T" := (Sym (Phant T)) (at level 0).

Canonical sign_morph := @Morphism _ _ 'Sym_T _ (in2W (@odd_permM _)).

Definition Alt of phant T := 'ker (@odd_perm T).

Canonical Alt_group phT := Eval hnf in [group of Alt phT].

Local Notation "'Alt_T" := (Alt (Phant T)) (at level 0).

Lemma Alt_even p : (p \in 'Alt_T) = ~~ p.
Proof. by rewrite !inE /=; case: odd_perm. Qed.

Lemma Alt_subset : 'Alt_T \subset 'Sym_T.
Proof. exact: subsetT. Qed.

Lemma Alt_normal : 'Alt_T <| 'Sym_T.
Proof. exact: ker_normal. Qed.

Lemma Alt_norm : 'Sym_T \subset 'N('Alt_T).
Proof. by case/andP: Alt_normal. Qed.

Let n := #|T|.

Lemma Alt_index : 1 < n -> #|'Sym_T : 'Alt_T| = 2.
Proof.
move=> lt1n; rewrite -card_quotient ?Alt_norm //=.
have : ('Sym_T / 'Alt_T) \isog (@odd_perm T @* 'Sym_T) by apply: first_isog.
case/isogP=> g /injmP/card_in_imset <-.
rewrite /morphim setIid=> ->; rewrite -card_bool; apply: eq_card => b.
apply/imsetP; case: b => /=; last first.
  by exists (1 : {perm T}); [rewrite setIid inE | rewrite odd_perm1].
case: (pickP T) lt1n => [x1 _ | d0]; last by rewrite /n eq_card0.
rewrite /n (cardD1 x1) ltnS lt0n => /existsP[x2 /=].
by rewrite eq_sym andbT -odd_tperm; exists (tperm x1 x2); rewrite ?inE.
Qed.

Lemma card_Sym : #|'Sym_T| = n`!.
Proof.
rewrite -[n]cardsE -card_perm; apply: eq_card => p.
by apply/idP/subsetP=> [? ?|]; rewrite !inE.
Qed.

Lemma card_Alt : 1 < n -> (2 * #|'Alt_T|)%N = n`!.
Proof.
by move/Alt_index <-; rewrite mulnC (Lagrange Alt_subset) card_Sym.
Qed.

Lemma Sym_trans : [transitive^n 'Sym_T, on setT | 'P].
Proof.
apply/imsetP; pose t1 := [tuple of enum T].
have dt1: t1 \in n.-dtuple(setT) by rewrite inE enum_uniq; apply/subsetP.
exists t1 => //; apply/setP=> t; apply/idP/imsetP=> [|[a _ ->{t}]]; last first.
  by apply: n_act_dtuple => //; apply/astabsP=> x; rewrite !inE.
case/dtuple_onP=> injt _; have injf := inj_comp injt enum_rank_inj.
exists (perm injf); first by rewrite inE.
apply: eq_from_tnth => i; rewrite tnth_map /= [aperm _ _]permE; congr tnth.
by rewrite (tnth_nth (enum_default i)) enum_valK.
Qed.

Lemma Alt_trans : [transitive^n.-2 'Alt_T, on setT | 'P].
Proof.
case n_m2: n Sym_trans => [|[|m]] /= tr_m2; try exact: ntransitive0.
have tr_m := ntransitive_weak (leqW (leqnSn m)) tr_m2.
case/imsetP: tr_m2; case/tupleP=> x; case/tupleP=> y t.
rewrite !dtuple_on_add 2![x \in _]inE inE negb_or /= -!andbA.
case/and4P=> nxy ntx nty dt _; apply/imsetP; exists t => //; apply/setP=> u.
apply/idP/imsetP=> [|[a _ ->{u}]]; last first.
  by apply: n_act_dtuple => //; apply/astabsP=> z; rewrite !inE.
case/(atransP2 tr_m dt)=> /= a _ ->{u}.
case odd_a: (odd_perm a); last by exists a => //; rewrite !inE /= odd_a.
exists (tperm x y * a); first by rewrite !inE /= odd_permM odd_tperm nxy odd_a.
apply/val_inj/eq_in_map => z tz; rewrite actM /= /aperm; congr (a _).
by case: tpermP ntx nty => // <-; rewrite tz.
Qed.

Lemma aperm_faithful (A : {group {perm T}}) : [faithful A, on setT | 'P].
Proof.
by apply/faithfulP=> /= p _ np1; apply/eqP/perm_act1P=> y; rewrite np1 ?inE.
Qed.

End SymAltDef.

Notation "''Sym_' T" := (Sym (Phant T))
  (at level 8, T at level 2, format "''Sym_' T") : group_scope.
Notation "''Sym_' T" := (Sym_group (Phant T)) : Group_scope.

Notation "''Alt_' T" := (Alt (Phant T))
  (at level 8, T at level 2, format "''Alt_' T") : group_scope.
Notation "''Alt_' T" := (Alt_group (Phant T)) : Group_scope.

Lemma trivial_Alt_2 (T : finType) : #|T| <= 2 -> 'Alt_T = 1.
Proof.
rewrite leq_eqVlt => /predU1P[] oT.
  by apply: card_le1_trivg; rewrite -leq_double -mul2n card_Alt oT.
suffices Sym1: 'Sym_T = 1 by apply/trivgP; rewrite -Sym1 subsetT.
by apply: card1_trivg; rewrite card_Sym; case: #|T| oT; do 2?case.
Qed.

Lemma simple_Alt_3 (T : finType) : #|T| = 3 -> simple 'Alt_T.
Proof.
move=> T3; have{T3} oA: #|'Alt_T| = 3.
  by apply: double_inj; rewrite -mul2n card_Alt T3.
apply/simpleP; split=> [|K]; [by rewrite trivg_card1 oA | case/andP=> sKH _].
have:= cardSg sKH; rewrite oA dvdn_divisors // !inE orbC /= -oA.
case/pred2P=> eqK; [right | left]; apply/eqP.
  by rewrite eqEcard sKH eqK leqnn.
by rewrite eq_sym eqEcard sub1G eqK cards1.
Qed.

Lemma not_simple_Alt_4 (T : finType) : #|T| = 4 -> ~~ simple 'Alt_T.
Proof.
move=> oT; set A := 'Alt_T.
have oA: #|A| = 12 by apply: double_inj; rewrite -mul2n card_Alt oT.
suffices [p]: exists p, [/\ prime p, 1 < #|A|`_p < #|A| & #|'Syl_p(A)| == 1%N].
  case=> p_pr pA_int; rewrite /A; case/normal_sylowP=> P; case/pHallP.
  rewrite /= -/A => sPA pP nPA; apply/simpleP=> [] [_]; rewrite -pP in pA_int.
  by case/(_ P)=> // defP; rewrite defP oA ?cards1 in pA_int.
have: #|'Syl_3(A)| \in filter [pred d | d %% 3 == 1%N] (divisors 12).
  by rewrite mem_filter -dvdn_divisors //= -oA card_Syl_dvd ?card_Syl_mod.
rewrite /= oA mem_seq2 orbC.
case/predU1P=> [oQ3|]; [exists 2 | exists 3]; split; rewrite ?p_part //.
pose A3 := [set x : {perm T} | #[x] == 3]; suffices oA3: #|A :&: A3| = 8.
  have sQ2 P: P \in 'Syl_2(A) -> P :=: A :\: A3.
    rewrite inE pHallE oA p_part -natTrecE /= => /andP[sPA /eqP oP].
    apply/eqP; rewrite eqEcard -(leq_add2l 8) -{1}oA3 cardsID oA oP.
    rewrite andbT subsetD sPA; apply/exists_inP=> -[x] /= Px.
    by rewrite inE => /eqP ox; have:= order_dvdG Px; rewrite oP ox.
  have [/= P sylP] := Sylow_exists 2 [group of A].
  rewrite -(([set P] =P 'Syl_2(A)) _) ?cards1 // eqEsubset sub1set inE sylP.
  by apply/subsetP=> Q sylQ; rewrite inE -val_eqE /= !sQ2 // inE.
rewrite -[8]/(4 * 2)%N -{}oQ3 -sum1_card -sum_nat_const.
rewrite (partition_big (fun x => <[x]>%G) (mem 'Syl_3(A))) => [|x]; last first.
  by case/setIP=> Ax; rewrite /= !inE pHallE p_part cycle_subG Ax oA.
apply: eq_bigr => Q; rewrite inE /= inE pHallE oA p_part -?natTrecE //=.
case/andP=> sQA /eqP oQ; have:= oQ.
rewrite (cardsD1 1) group1 -sum1_card => [[/= <-]]; apply: eq_bigl => x.
rewrite setIC -val_eqE /= 2!inE in_setD1 -andbA -{4}[x]expg1 -order_dvdn dvdn1.
apply/and3P/andP=> [[/eqP-> _ /eqP <-] | [ntx Qx]]; first by rewrite cycle_id.
have:= order_dvdG Qx; rewrite oQ dvdn_divisors // mem_seq2 (negPf ntx) /=.
by rewrite eqEcard cycle_subG Qx (subsetP sQA) // oQ /order => /eqP->.
Qed.

Lemma simple_Alt5_base (T : finType) : #|T| = 5 -> simple 'Alt_T.
Proof.
move=> oT.
have F1: #|'Alt_T| = 60 by apply: double_inj; rewrite -mul2n card_Alt oT.
have FF (H : {group {perm T}}): H <| 'Alt_T -> H :<>: 1 -> 20 %| #|H|.
- move=> Hh1 Hh3.
  have [x _]: exists x, x \in T by apply/existsP/eqP; rewrite oT.
  have F2 := Alt_trans T; rewrite oT /= in F2.
  have F3: [transitive 'Alt_T, on setT | 'P] by apply: ntransitive1 F2.
  have F4: [primitive 'Alt_T, on setT | 'P] by apply: ntransitive_primitive F2.
  case: (prim_trans_norm F4 Hh1) => F5.
    by case: Hh3; apply/trivgP; apply: subset_trans F5 (aperm_faithful _).
  have F6: 5 %| #|H| by rewrite -oT -cardsT (atrans_dvd F5).
  have F7: 4 %| #|H|.
    have F7: #|[set~ x]| = 4 by rewrite cardsC1 oT.
    case: (pickP (mem [set~ x])) => [y Hy | ?]; last by rewrite eq_card0 in F7.
    pose K := 'C_H[x | 'P]%G.
    have F8 : K \subset H by apply: subsetIl.
    pose Gx := 'C_('Alt_T)[x | 'P]%G.
    have F9: [transitive^2 Gx, on [set~ x] | 'P].
      by rewrite -[[set~ x]]setTI -setDE stab_ntransitive ?inE.
    have F10: [transitive Gx, on [set~ x] | 'P].
      exact: ntransitive1 F9.
    have F11: [primitive Gx, on [set~ x] | 'P].
      exact: ntransitive_primitive F9.
    have F12: K \subset Gx by apply: setSI; apply: normal_sub.
    have F13: K <| Gx by rewrite /(K <| _) F12 normsIG // normal_norm.
    case: (prim_trans_norm F11 F13) => Ksub; last first.
      by apply: dvdn_trans (cardSg F8); rewrite -F7; apply: atrans_dvd Ksub.
    have F14: [faithful Gx, on [set~ x] | 'P].
      apply/subsetP=> g; do 2![case/setIP] => Altg cgx cgx'.
      apply: (subsetP (aperm_faithful 'Alt_T)).
      rewrite inE Altg /=; apply/astabP=> z _.
      case: (z =P x) => [->|]; first exact: (astab1P cgx).
      by move/eqP=> nxz; rewrite (astabP cgx') ?inE //.
    have Hreg g (z : T): g \in H -> g z = z -> g = 1.
      have F15 h: h \in H -> h x = x -> h = 1.
        move=> Hh Hhx; have: h \in K by rewrite inE Hh; apply/astab1P.
        by rewrite (trivGP (subset_trans Ksub F14)) => /set1P.
      move=> Hg Hgz; have:= in_setT x; rewrite -(atransP F3 z) ?inE //.
      case/imsetP=> g1 Hg1 Hg2; apply: (conjg_inj g1); rewrite conj1g.
      apply: F15; last by rewrite Hg2 -permM mulKVg permM Hgz.
      by case/normalP: Hh1 => _ nH1; rewrite -(nH1 _ Hg1) memJ_conjg.
    clear K F8 F12 F13 Ksub F14.
    case: (Cauchy _ F6) => // h Hh /eqP Horder.
    have diff_hnx_x n: 0 < n -> n < 5 -> x != (h ^+ n) x.
      move=> Hn1 Hn2; rewrite eq_sym; apply/negP => HH.
      have: #[h ^+ n] = 5.
        rewrite orderXgcd // (eqP Horder).
        by move: Hn1 Hn2 {HH}; do 5 (case: n => [|n] //).
      have Hhd2: h ^+ n \in H by rewrite groupX.
      by rewrite (Hreg _ _ Hhd2 (eqP HH)) order1.
    pose S1 := [tuple x; h x; (h ^+ 3) x].
    have DnS1: S1 \in 3.-dtuple(setT).
      rewrite inE memtE subset_all /= !inE /= !negb_or -!andbA /= andbT.
      rewrite -{1}[h]expg1 !diff_hnx_x // expgSr permM.
      by rewrite (inj_eq perm_inj) diff_hnx_x.
    pose S2 := [tuple x; h x; (h ^+ 2) x].
    have DnS2:  S2 \in 3.-dtuple(setT).
      rewrite inE memtE subset_all /= !inE /= !negb_or -!andbA /= andbT.
      rewrite -{1}[h]expg1 !diff_hnx_x // expgSr permM.
      by rewrite (inj_eq perm_inj) diff_hnx_x.
    case: (atransP2 F2 DnS1 DnS2) => g Hg [/=].
    rewrite /aperm => Hgx Hghx Hgh3x.
    have h_g_com: h * g = g * h.
      suff HH: (g * h * g^-1) * h^-1 = 1 by rewrite -[h * g]mul1g -HH !gnorm.
      apply: (Hreg _ x); last first.
        by rewrite !permM -Hgx Hghx -!permM mulKVg mulgV perm1.
      rewrite groupM // ?groupV // (conjgCV g) mulgK -mem_conjg.
      by case/normalP: Hh1 => _ ->.
    have: (g * (h ^+ 2) * g ^-1) x = (h ^+ 3) x.
      rewrite !permM -Hgx.
      have ->: h (h x) = (h ^+ 2) x by rewrite /= permM.
      by rewrite {1}Hgh3x -!permM /= mulgV mulg1 -expgSr.
    rewrite commuteX // mulgK {1}[expgn]lock expgS permM -lock.
    by move/perm_inj=> eqxhx; case/eqP: (diff_hnx_x 1%N isT isT); rewrite expg1.
  by rewrite (@Gauss_dvd 4 5) // F7.
apply/simpleP; split => [|H Hnorm]; first by rewrite trivg_card1 F1.
case Hcard1: (#|H| == 1%N); move/eqP: Hcard1 => Hcard1.
  by left; apply: card1_trivg; rewrite Hcard1.
right; case Hcard60: (#|H| == 60%N); move/eqP: Hcard60 => Hcard60.
  by apply/eqP; rewrite eqEcard Hcard60 F1 andbT; case/andP: Hnorm.
have Hcard20: #|H| = 20; last clear Hcard1 Hcard60.
  have Hdiv: 20 %| #|H| by apply: FF => // HH; case Hcard1; rewrite HH cards1.
  case H20: (#|H| == 20); first by apply/eqP.
  case: Hcard60; case/andP: Hnorm; move/cardSg; rewrite F1 => Hdiv1 _.
  by case/dvdnP: Hdiv H20 Hdiv1 => n ->; move: n; do 4!case=> //.
have prime_5: prime 5 by [].
have nSyl5: #|'Syl_5(H)| = 1%N.
  move: (card_Syl_dvd 5 H) (card_Syl_mod H prime_5).
  rewrite Hcard20; case: (card _) => // n Hdiv.
  move: (dvdn_leq  (isT: (0 < 20)%N) Hdiv).
  by move: (n) Hdiv; do 20 (case=> //).
case: (Sylow_exists 5 H) => S; case/pHallP=> sSH oS.
have{oS} oS: #|S| = 5 by rewrite oS p_part Hcard20.
suff: 20 %| #|S| by rewrite oS.
apply FF => [|S1]; last by rewrite S1 cards1 in oS.
apply: char_normal_trans Hnorm; apply: lone_subgroup_char => // Q sQH isoQS.
rewrite subEproper; apply/norP=> [[nQS _]]; move: nSyl5.
rewrite (cardsD1 S) (cardsD1 Q) 4!{1}inE nQS !pHallE sQH sSH Hcard20 p_part.
by rewrite (card_isog isoQS) oS.
Qed.

Section Restrict.

Variables (T : finType) (x : T).
Notation T' := {y | y != x}.

Lemma rfd_funP (p : {perm T}) (u : T') :
  let p1 := if p x == x then p else 1 in p1 (val u) != x.
Proof.
case: (p x =P x) => /= [pxx | _]; last by rewrite perm1 (valP u).
by rewrite -[x in _ != x]pxx (inj_eq perm_inj); apply: (valP u).
Qed.

Definition rfd_fun p := [fun u => Sub ((_ : {perm T}) _) (rfd_funP p u) : T'].

Lemma rfdP p : injective (rfd_fun p).
Proof.
apply: can_inj (rfd_fun p^-1) _ => u; apply: val_inj => /=.
rewrite -(can_eq (permK p)) permKV eq_sym.
by case: eqP => _; rewrite !(perm1, permK).
Qed.

Definition rfd p := perm (@rfdP p).

Hypothesis card_T : 2 < #|T|.

Lemma rfd_morph : {in 'C_('Sym_T)[x | 'P] &, {morph rfd : y z / y * z}}.
Proof.
move=> p q; rewrite !setIA !setIid; move/astab1P=> p_x; move/astab1P=> q_x.
apply/permP=> u; apply: val_inj.
by rewrite permE /= !permM !permE /= [p x]p_x [q x]q_x eqxx permM /=.
Qed.

Canonical rfd_morphism := Morphism rfd_morph.

Definition rgd_fun (p : {perm T'}) :=
  [fun x1 => if insub x1 is Some u then sval (p u) else x].

Lemma rgdP p : injective (rgd_fun p).
Proof.
apply: can_inj (rgd_fun p^-1) _ => y /=.
case: (insubP _ y) => [u _ val_u|]; first by rewrite valK permK.
by rewrite negbK; move/eqP->; rewrite insubF //= eqxx.
Qed.

Definition rgd p := perm (@rgdP p).

Lemma rfd_odd (p : {perm T}) : p x = x -> rfd p = p :> bool.
Proof.
have rfd1: rfd 1 = 1.
  by apply/permP => u; apply: val_inj; rewrite permE /= if_same !perm1.
have HP0 (t : {perm T}): #|[set x | t x != x]| = 0 -> rfd t = t :> bool.
- move=> Ht; suff ->: t = 1 by rewrite rfd1 !odd_perm1.
  apply/permP => z; rewrite perm1; apply/eqP/wlog_neg => nonfix_z.
  by rewrite (cardD1 z) inE nonfix_z in Ht.
elim: #|_| {-2}p (leqnn #|[set x | p x != x]|) => {p}[|n Hrec] p Hp Hpx.
  by apply: HP0; move: Hp; case: card.
case Ex: (pred0b (mem [set x | p x != x])); first by apply: HP0; move/eqnP: Ex.
case/pred0Pn: Ex => x1; rewrite /= inE => Hx1.
have nx1x: x1 != x by apply/eqP => HH; rewrite HH Hpx eqxx in Hx1.
have npxx1: p x != x1 by apply/eqP => HH; rewrite -HH !Hpx eqxx in Hx1.
have npx1x: p x1 != x.
  by apply/eqP; rewrite -Hpx; move/perm_inj => HH; case/eqP: nx1x.
pose p1 := p * tperm x1 (p x1).
have Hp1: p1 x = x.
  by rewrite /p1 permM; case tpermP => // [<-|]; [rewrite Hpx | move/perm_inj].
have Hcp1: #|[set x | p1 x != x]| <= n.
  have F1 y: p y = y -> p1 y = y.
    move=> Hy; rewrite /p1 permM Hy.
    by case: tpermP => [<-|/(canLR (permK p))<-|] //; apply/(canLR (permK p)).
  have F2: p1 x1 = x1 by rewrite /p1 permM tpermR.
  have F3: [set x | p1 x != x] \subset [predD1 [set x | p x != x] & x1].
    apply/subsetP => z; rewrite !inE permM.
    case tpermP => HH1 HH2.
    - rewrite eq_sym HH1 andbb; apply/eqP=> dx1.
      by rewrite dx1 HH1 dx1 eqxx in HH2.
    - by rewrite (perm_inj HH1) eqxx in HH2.
    by move->; rewrite andbT; apply/eqP => HH3; rewrite HH3 in HH2.
  apply: (leq_trans (subset_leq_card F3)).
  by move: Hp; rewrite (cardD1 x1) inE Hx1.
have ->: p = p1 * tperm x1 (p x1) by rewrite -mulgA tperm2 mulg1.
rewrite odd_permM odd_tperm eq_sym Hx1 morphM; last 2 first.
- by rewrite 2!inE; apply/astab1P.
- by rewrite 2!inE; apply/astab1P; rewrite -{1}Hpx /= /aperm -permM.
rewrite odd_permM Hrec //=; congr (_ (+) _).
pose x2 : T' := Sub x1 nx1x; pose px2 : T' := Sub (p x1) npx1x.
suff ->: rfd (tperm x1 (p x1)) = tperm x2 px2.
  by rewrite odd_tperm -val_eqE eq_sym.
apply/permP => z; apply/val_eqP; rewrite permE /= tpermD // eqxx.
case: (tpermP x2) => [->|->|HH1 HH2]; rewrite /x2 ?tpermL ?tpermR 1?tpermD //.
  by apply/eqP=> HH3; case: HH1; apply: val_inj.
by apply/eqP => HH3; case: HH2; apply: val_inj.
Qed.

Lemma rfd_iso : 'C_('Alt_T)[x | 'P] \isog 'Alt_T'.
Proof.
have rgd_x p: rgd p x = x by rewrite permE /= insubF //= eqxx.
have rfd_rgd p: rfd (rgd p) = p.
  apply/permP => [[z Hz]]; apply/val_eqP; rewrite !permE.
  rewrite /= [rgd _ _]permE /= insubF eq_refl // permE /=.
  by rewrite (@insubT _ (xpredC1 x) _ _ Hz).
have sSd: 'C_('Alt_T)[x | 'P] \subset 'dom rfd.
  by apply/subsetP=> p; rewrite !inE /=; case/andP.
apply/isogP; exists [morphism of restrm sSd rfd] => /=; last first.
  rewrite morphim_restrm setIid; apply/setP=> z; apply/morphimP/idP=> [[p _]|].
    case/setIP; rewrite Alt_even => Hp; move/astab1P=> Hp1 ->.
    by rewrite Alt_even rfd_odd.
  have dz': rgd z x == x by rewrite rgd_x.
  move=> kz; exists (rgd z); last by rewrite /= rfd_rgd.
    by rewrite 2!inE (sameP astab1P eqP).
  rewrite 4!inE /= (sameP astab1P eqP) dz' -rfd_odd; last exact/eqP.
  by rewrite rfd_rgd mker // ?set11.
apply/injmP=> x1 y1 /=.
case/setIP=> Hax1; move/astab1P; rewrite /= /aperm => Hx1.
case/setIP=> Hay1; move/astab1P; rewrite /= /aperm => Hy1 Hr.
apply/permP => z.
case (z =P x) => [->|]; [by rewrite Hx1 | move/eqP => nzx].
move: (congr1 (fun q : {perm T'} => q (Sub z nzx)) Hr).
by rewrite !permE => [[]]; rewrite Hx1 Hy1 !eqxx.
Qed.

End Restrict.

Lemma simple_Alt5 (T : finType) : #|T| >= 5 -> simple 'Alt_T.
Proof.
suff F1 n: #|T| = n + 5 -> simple 'Alt_T by move/subnK/esym/F1.
elim: n T => [| n Hrec T Hde]; first exact: simple_Alt5_base.
have oT: 5 < #|T| by rewrite Hde addnC.
apply/simpleP; split=> [|H Hnorm]; last have [Hh1 nH] := andP Hnorm.
  rewrite trivg_card1 -[#|_|]half_double -mul2n card_Alt Hde addnC //.
  by rewrite addSn factS mulnC -(prednK (fact_gt0 _)).
case E1: (pred0b T); first by rewrite /pred0b in E1; rewrite (eqP E1) in oT.
case/pred0Pn: E1 => x _; have Hx := in_setT x.
have F2: [transitive^4 'Alt_T, on setT | 'P].
  by apply: ntransitive_weak (Alt_trans T); rewrite -(subnKC oT).
have F3 := ntransitive1 (isT: 0 < 4) F2.
have F4 := ntransitive_primitive (isT: 1 < 4) F2.
case Hcard1: (#|H| == 1%N); move/eqP: Hcard1 => Hcard1.
  by left; apply: card1_trivg; rewrite Hcard1.
right; case: (prim_trans_norm F4 Hnorm) => F5.
  by rewrite (trivGP (subset_trans F5 (aperm_faithful _))) cards1 in Hcard1.
case E1: (pred0b (predD1 T x)).
  rewrite /pred0b in E1; move: oT.
  by rewrite (cardD1 x) (eqP E1); case: (T x).
case/pred0Pn: E1 => y Hdy; case/andP: (Hdy) => diff_x_y Hy.
pose K := 'C_H[x | 'P]%G.
have F8: K \subset H by apply: subsetIl.
pose Gx := 'C_('Alt_T)[x | 'P].
have F9: [transitive^3 Gx, on [set~ x] | 'P].
  by rewrite -[[set~ x]]setTI -setDE stab_ntransitive ?inE.
have F10: [transitive Gx, on [set~ x] | 'P].
  by apply: ntransitive1 F9.
have F11: [primitive Gx, on [set~ x] | 'P].
  by apply: ntransitive_primitive F9.
have F12: K \subset Gx by rewrite setSI // normal_sub.
have F13: K <| Gx by apply/andP; rewrite normsIG.
have:= prim_trans_norm F11; case/(_ K) => //= => Ksub; last first.
  have F14: Gx * H = 'Alt_T by apply/(subgroup_transitiveP _ _ F3).
  have: simple Gx.
    by rewrite (isog_simple (rfd_iso x)) Hrec //= card_sig cardC1 Hde.
  case/simpleP=> _ simGx; case/simGx: F13 => /= HH2.
    case Ez: (pred0b (predD1 (predD1 T x) y)).
      move: oT; rewrite /pred0b in Ez.
      by rewrite (cardD1 x) (cardD1 y) (eqP Ez) inE /= inE /= diff_x_y.
    case/pred0Pn: Ez => z; case/andP => diff_y_z Hdz.
    have [diff_x_z Hz] := andP Hdz.
    have: z \in [set~ x] by rewrite !inE.
    rewrite -(atransP Ksub y) ?inE //; case/imsetP => g.
    rewrite /= HH2 inE; move/eqP=> -> HH4.
    by case/negP: diff_y_z; rewrite HH4 act1.
  by rewrite /= -F14 -[Gx]HH2 (mulSGid F8).
have F14: [faithful Gx, on [set~ x] | 'P].
  apply: subset_trans (aperm_faithful 'Sym_T); rewrite subsetI subsetT.
  apply/subsetP=> g; do 2![case/setIP]=> _ cgx cgx'; apply/astabP=> z _ /=.
  case: (z =P x) => [->|]; first exact: (astab1P cgx).
  by move/eqP=> zx; rewrite [_ g](astabP cgx') ?inE.
have Hreg g z: g \in H -> g z = z -> g = 1.
  have F15 h: h \in H -> h x = x -> h = 1.
    move=> Hh Hhx; have: h \in K by rewrite inE Hh; apply/astab1P.
    by rewrite [K](trivGP (subset_trans Ksub F14)) => /set1P.
  move=> Hg Hgz; have:= in_setT x; rewrite -(atransP F3 z) ?inE //.
  case/imsetP=> g1 Hg1 Hg2; apply: (conjg_inj g1); rewrite conj1g.
  apply: F15; last by rewrite Hg2 -permM mulKVg permM Hgz.
  by rewrite memJ_norm ?(subsetP nH).
clear K F8 F12 F13 Ksub F14.
have Hcard: 5 < #|H|.
  apply: (leq_trans oT); apply dvdn_leq; first by apply: cardG_gt0.
  by rewrite -cardsT (atrans_dvd F5).
case Eh: (pred0b [predD1 H & 1]).
  by move: Hcard; rewrite /pred0b in Eh; rewrite (cardD1 1) group1 (eqP Eh).
case/pred0Pn: Eh => h; case/andP => diff_1_h /= Hh.
case Eg: (pred0b (predD1 (predD1 [predD1 H & 1] h) h^-1)).
  move: Hcard; rewrite ltnNge; case/negP.
  rewrite (cardD1 1) group1 (cardD1 h) (cardD1 h^-1) (eqnP Eg).
  by do 2!case: (_ \in _).
case/pred0Pn: Eg => g; case/andP => diff_h1_g; case/andP => diff_h_g.
case/andP => diff_1_g /= Hg.
case diff_hx_x: (h x == x).
by case/negP: diff_1_h; apply/eqP; apply: (Hreg _ _ Hh (eqP diff_hx_x)).
case diff_gx_x: (g x == x).
  case/negP: diff_1_g; apply/eqP; apply: (Hreg _ _ Hg (eqP diff_gx_x)).
case diff_gx_hx: (g x == h x).
  case/negP: diff_h_g; apply/eqP; symmetry; apply: (mulIg g^-1); rewrite gsimp.
  apply: (Hreg _ x); first by rewrite groupM // groupV.
  by rewrite permM -(eqP diff_gx_hx) -permM mulgV perm1.
case diff_hgx_x: ((h * g) x == x).
  case/negP: diff_h1_g; apply/eqP; apply: (mulgI h); rewrite !gsimp.
  by apply: (Hreg _ x); [apply: groupM | apply/eqP].
case diff_hgx_hx: ((h * g) x == h x).
  case/negP: diff_1_g; apply/eqP.
  by apply: (Hreg _ (h x)) => //; apply/eqP; rewrite -permM.
case diff_hgx_gx: ((h * g) x == g x).
  by case/idP: diff_hx_x; rewrite -(can_eq (permK g)) -permM.
case Ez: (pred0b
            (predD1 (predD1 (predD1 (predD1 T x) (h x)) (g x)) ((h * g) x))).
- move: oT; rewrite /pred0b in Ez.
  rewrite (cardD1 x) (cardD1 (h x)) (cardD1 (g x)) (cardD1 ((h * g) x)).
  by rewrite (eqP Ez) addnC; do 3!case: (_ x \in _).
case/pred0Pn: Ez => z.
case/and5P=> diff_hgx_z diff_gx_z diff_hx_z diff_x_z /= Hz.
pose S1 := [tuple x; h x; g x; z].
have DnS1: S1 \in 4.-dtuple(setT).
  rewrite inE memtE subset_all -!andbA !negb_or /= !inE !andbT.
  rewrite -!(eq_sym z) diff_gx_z diff_x_z diff_hx_z.
  by rewrite !(eq_sym x) diff_hx_x diff_gx_x eq_sym diff_gx_hx.
pose S2 := [tuple x; h x; g x; (h * g) x].
have DnS2: S2 \in 4.-dtuple(setT).
  rewrite inE memtE subset_all -!andbA !negb_or /= !inE !andbT !(eq_sym x).
  rewrite diff_hx_x diff_gx_x diff_hgx_x.
  by rewrite !(eq_sym (h x)) diff_gx_hx diff_hgx_hx eq_sym diff_hgx_gx.
case: (atransP2 F2 DnS1 DnS2) => k Hk [/=].
rewrite /aperm => Hkx Hkhx Hkgx Hkhgx.
have h_k_com: h * k = k * h.
  suff HH: (k * h * k^-1) * h^-1 = 1 by rewrite -[h * k]mul1g -HH !gnorm.
  apply: (Hreg _ x); last first.
    by rewrite !permM -Hkx Hkhx -!permM mulKVg mulgV perm1.
  by rewrite groupM // ?groupV // (conjgCV k) mulgK -mem_conjg (normsP nH).
have g_k_com: g * k = k * g.
  suff HH: (k * g * k^-1) * g^-1 = 1 by rewrite -[g * k]mul1g -HH !gnorm.
  apply: (Hreg _ x); last first.
    by rewrite !permM -Hkx Hkgx -!permM mulKVg mulgV perm1.
  by rewrite groupM // ?groupV // (conjgCV k) mulgK -mem_conjg (normsP nH).
have HH: (k * (h * g) * k ^-1) x = z.
   by rewrite 2!permM -Hkx Hkhgx -permM mulgV perm1.
case/negP: diff_hgx_z.
rewrite -HH !mulgA -h_k_com -!mulgA [k * _]mulgA.
by rewrite -g_k_com -!mulgA mulgV mulg1.
Qed.
