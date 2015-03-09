(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg finset fingroup morphism.
Require Import perm automorphism quotient action zmodp center commutator.
Require Import poly cyclic pgroup nilpotent matrix mxalgebra mxrepresentation.
Require Import vector falgebra fieldext ssrnum algC rat algnum galois.
Require Import classfun character inertia integral_char vcharacter.
Require ssrint.

(******************************************************************************)
(* This file covers Peterfalvi, Section 1: Preliminary results.               *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Local Notation algCF := [fieldType of algC].

Section Main.

Variable gT : finGroupType.

(* This is Peterfalvi (1.1). *)
Lemma odd_eq_conj_irr1 (G : {group gT}) t :
  odd #|G| -> (('chi[G]_t)^*%CF == 'chi_t) = ('chi_t == 1).
Proof.
move=> OG; apply/eqP/eqP=> [Ht | ->]; last exact: cfConjC_cfun1.
pose a := (@Zp1 1).
have Aito:
    is_action <[a]> (fun (t : Iirr G) v => if v == a then conjC_Iirr t else t).
  split=> [[[|[]]] //= _  t1 t2 Hj |j [[|[]]] // HH1 [[|[]]] // HH2 ] //=.
    by apply: (inv_inj (@conjC_IirrK _ _)).
  by rewrite conjC_IirrK.
pose ito := Action Aito.
have Acto:
    is_action <[a]> (fun (c : {set gT}) v => if v == a then c^-1%g else c).
  split=> [[[|[]]] //= _  t1 t2 Hj |j [[|[]]] // HH1 [[|[]]] // HH2 ] //=.
    by rewrite -[t1]invgK Hj invgK.
  by rewrite invgK.
pose cto := Action Acto.
have F1: [acts <[a]>, on (classes G) | cto].
  apply/subsetP=> j Hj.
  rewrite !inE Hj; apply/subsetP=> u.
  case/imsetP=> g GiG ->.
  by rewrite inE /=; case: (_ == _) => //;
     rewrite -?classVg mem_classes // ?groupV.
have F2 u x y: x \in G -> y \in cto (x ^: G) a -> 'chi_u x = 'chi_(ito u a) y.
  rewrite mem_invg -{2}[y]invgK => Gx {y}/imsetP[y Gy ->].
  by rewrite -conjVg cfunJ {y Gy}//= conjC_IirrE cfunE -irr_inv invgK.
have F3: forall c, c \in classes G -> c^-1%g = c -> c = 1%g.
  move=> c; case/imsetP => g GiG ->; rewrite -classVg => Hg.
  move: (class_refl G g^-1); rewrite Hg; case/imsetP=> x XiG Hx.
  have F4: (x ^+ 2)%g \in 'C_G[g].
    apply/subcent1P; split; rewrite ?groupM //.
    apply: (mulgI (x * x * g)^-1)%g.
    rewrite mulVg !invMg Hx conjgE !mulgA mulgK.
    rewrite -[(_ * g * x)%g]mulgA -[(_ * (g * _))%g]mulgA -conjgE.
    by rewrite -Hx mulgK mulVg.
  have F5 : x \in 'C_G[g].
    suff->: (x = (x ^+ 2) ^+ (#|G| %/2).+1)%g by apply: groupX.
    rewrite -expgM -[(_%/_).+1]addn1 mulnDr muln1 -{3}addn1 addnA.
    move: (modn2 #|G|); rewrite {1}OG /= => HH; rewrite -{3}HH.
    rewrite [(2 * _)%N]mulnC -divn_eq expgD expg1.
    by move: (order_dvdG XiG); rewrite order_dvdn; move/eqP->; rewrite mul1g.
  move: Hx; rewrite conjgE; case/subcent1P: F5=> _ ->.
  rewrite mulgA mulVg mul1g => HH.
  have F6: (g ^+ 2 == 1)%g by rewrite expgS -{1}HH expg1 mulVg.
  suff: #[g] == 1%N by rewrite order_eq1; move/eqP->; apply: class1G.
  move: F6 (order_gt0 g) (order_dvdG GiG); rewrite -order_dvdn.
  move/(dvdn_leq (isT : (0 < 2)%N)); case: #[_]=> // [[|[]]] //.
  by rewrite dvdn2 OG.
apply/eqP; case: (boolP (t == 0))=> // Hd.
  by move/eqP: Hd->; rewrite irr0.
have:= card_afix_irr_classes (cycle_id a) F1 F2.
have->: #|'Fix_(classes G | cto)[a]| = 1%N.
  apply: (@eq_card1 _ 1%g)=> c; apply/idP/idP; rewrite !inE.
    case/andP=> GiG HH; apply/eqP; apply: F3=> //; apply/eqP.
    by move/subsetP: HH; move/(_ a); rewrite !inE eqxx; apply.
  move/eqP->; rewrite classes1.
  apply/subsetP=> b; rewrite !inE; move/eqP=> -> /=.
  by rewrite invg1.
rewrite (cardD1 (0 : Iirr _)).
have->: 0 \in 'Fix_ito[a].
  apply/afixP=> b; rewrite !inE; move/eqP->; rewrite /=.
  apply: irr_inj; apply/cfunP=> g.
  by rewrite conjC_IirrE cfConjCE irr0 cfun1E conjC_nat.
rewrite (cardD1 t) //.
suff->: t \in [predD1 'Fix_ito[a] & 0] by [].
rewrite inE /= Hd.
apply/afixP=> b; rewrite !inE; move/eqP->; rewrite /=.
apply: irr_inj; apply/cfunP=> g.
by rewrite conjC_IirrE Ht.
Qed.

Variables G H : {group gT}.

(* This is Peterfalvi (1.2). *)
Lemma not_in_ker_char0 t g : g \in G ->
  H <| G -> ~~ (H \subset cfker 'chi[G]_t) -> 'C_H[g] = 1%g -> 'chi_t g = 0.
Proof.
move=> GiG HnG nHsC CH1.
have: (#|'C_G[g]| <= #|'C_(G/H)[coset H g]|)%N.
  suff->: #|'C_G[g]| = #|'C_G[g] / H|%G.
    by apply: (subset_leq_card (quotient_subcent1 H G g)).
  apply: card_isog.
  apply: isog_trans (second_isog _); last first.
    apply: subset_trans (normal_norm HnG).
    by apply: subcent1_sub.
  suff->: H :&: 'C_G[g] = 1%g by exact: quotient1_isog.
    rewrite -CH1.
    apply/setP=> h; rewrite inE.
    apply/andP/subcent1P; case=> H1 H2; split=> //.
      by move/subcent1P: H2; case.
    apply/subcent1P; split=> //.
    by apply: (subsetP (normal_sub HnG)).
have F1: coset H g \in (G / H)%g by exact: mem_quotient.
rewrite -leC_nat.
have:= second_orthogonality_relation g GiG.
rewrite mulrb class_refl => <-.
have:= second_orthogonality_relation (coset H g) F1.
rewrite mulrb class_refl => <-; rewrite -!(eq_bigr _ (fun _ _ => normCK _)).
rewrite sum_norm_irr_quo // (bigID (fun i => H \subset cfker 'chi_i)) //=.
set S := \sum_(i | ~~ _) _; set S' := \sum_(i | _) _ => HH.
have /eqP F2: S == 0.
  rewrite eqr_le -(ler_add2l S') addr0 HH /=.
  by apply: sumr_ge0 => j _; rewrite mulr_ge0 ?normr_ge0.
apply/eqP; have: `|'chi_t g| ^+ 2 == 0.
  apply/eqP; apply: (psumr_eq0P _ F2) nHsC => j _.
  by rewrite mulr_ge0 ?normr_ge0.
by rewrite mulf_eq0 orbb normr_eq0.
Qed.

(* This is Peterfalvi (1.3)(a). *)
Lemma equiv_restrict_compl A m (Phi : m.-tuple 'CF(H)) (mu : 'CF(G)) d :
    H \subset G -> A <| H -> basis_of 'CF(H, A) Phi ->
  ({in A, mu =1 \sum_i d i *: 'chi_i} <-> 
    (forall j : 'I_m,
        \sum_i '[Phi`_j, 'chi_i] * (d i)^* = '['Ind[G] Phi`_j, mu])).
Proof.
move=> sHG nsAH BPhi; have [sAH nAH] := andP nsAH.
have APhi (i : 'I_m) : Phi`_i \in 'CF(H, A).
  by apply: (basis_mem BPhi _); apply: mem_nth; rewrite size_tuple.
pose D := 'Res[H] mu - \sum_i d i *: 'chi_i.
transitivity (D \in 'CF(H, H :\: A)).
  split=> [A'D | /cfun_onP A'D x Ax].
    apply/cfun_onP=> x; rewrite inE negb_and negbK.
    case/orP=> [Ax | /cfun0-> //]; rewrite !cfunE -A'D //.
    by rewrite cfResE ?subrr ?(subsetP sAH).
  have:= A'D x; rewrite !cfunE !inE Ax => /(_ isT)/(canRL (subrK _)).
  by rewrite add0r cfResE // ?(subsetP sAH).
have F0 (j : 'I_m) : 
   (\sum_i '[Phi`_j, 'chi_i] * (d i)^* == '['Ind Phi`_j, mu])
      = ('[Phi`_j, D] == 0).
  rewrite raddfB raddf_sum /= Frobenius_reciprocity subr_eq0 eq_sym.
  by congr (_ == _); apply: eq_bigr=> i _; rewrite cfdotZr mulrC.
split=> [HH j | HH].
  by apply/eqP; rewrite F0; apply/eqP; apply: cfdot_complement.
have{F0} F1 (j : 'I_m) : '[Phi`_j, D]_H = 0.
  by have/eqP := HH j; rewrite F0 => /eqP.
have: (D \in 'CF(H))%VS by rewrite memvf.
rewrite -(cfun_complement nsAH) => /memv_addP[f Cf [g Cg defD]].
have: '[f, f + g] = 0.
  rewrite -defD (coord_basis BPhi Cf) cfdot_suml.
  by rewrite big1 // => i _; rewrite cfdotZl F1 mulr0.
rewrite raddfD /= {1}(cfdot_complement Cf Cg) addr0 => /eqP.
by rewrite cfnorm_eq0 defD => /eqP->; rewrite add0r.
Qed.

(* This is Peterfalvi (1.3)(b). *)
Lemma equiv_restrict_compl_ortho A m (Phi : m.-tuple 'CF(H)) mu_ :
    H \subset G -> A <| H -> basis_of 'CF(H, A) Phi -> 
     (forall i j, '[mu_ i, mu_ j] = (i == j)%:R) ->
     (forall j : 'I_m, 'Ind[G] Phi`_j = \sum_i '[Phi`_j, 'chi_i] *: mu_ i) ->
   [/\ forall i, {in A, mu_ i =1 'chi_i}
     & forall mu, (forall i, '[mu, mu_ i] = 0) -> {in A, forall x, mu x = 0}].
Proof.
move=> HsG nsAH /equiv_restrict_compl Phi_A Mo IP; split=> [/= i | mu Cmu x Ax].
  have->: 'chi[H]_i = \sum_j (j == i)%:R *: 'chi_j.
    rewrite (bigD1 i) //= eqxx scale1r big1 ?addr0 // => j /negPf->.
    by rewrite scale0r.
  apply/Phi_A=> // j; rewrite IP cfdot_suml.
  by apply: eq_bigr=> k _; rewrite cfdotZl rmorph_nat Mo.
transitivity ((\sum_j 0 *: 'chi[H]_j) x); last first.
  by rewrite sum_cfunE big1 // => j _; rewrite cfunE mul0r.
move: x Ax; apply/Phi_A=> // j.
rewrite -mulr_suml rmorph0 mulr0 IP cfdot_suml big1 // => k _.
by rewrite cfdotZl [d in _ * d]cfdotC Cmu rmorph0 mulr0.
Qed.

Let vchar_isometry_base3 f f' : 
  f \in 'Z[irr G, G^#] -> '[f]_G = 2%:R ->
  f' \in 'Z[irr G, G^#] -> '[f']_G = 2%:R ->
  '[f, f'] = 1 ->
   exists es : _ * bool, let: (i, j, k, epsilon) := es in
     [/\  f = (-1) ^+ epsilon *: ('chi_j - 'chi_i),
          f' = (-1) ^+ epsilon *: ('chi_j - 'chi_k)
        & uniq [:: i; j; k]].
Proof.
move=> Hf H2f Hf1 H2f1.
have [j [i neq_ij ->]] := vchar_norm2 Hf H2f.
have [j' [k neq_kj' ->]] := vchar_norm2 Hf1 H2f1.
rewrite cfdotBl !cfdotBr !cfdot_irr opprB addrAC !addrA.
do 2!move/(canRL (subrK _)); rewrite -(natrD _ 1) -!natrD => /eqP.
rewrite eqr_nat; have [eq_jj' | neq_jj'] := altP (j =P j').
  rewrite (eq_sym j) -eq_jj' {1}eq_jj' (negbTE neq_ij) (negbTE neq_kj').
  rewrite eqSS (can_eq oddb) => /eqP neq_ik; exists (i, j, k, false).
  by rewrite !scaler_sign /= !inE neq_ik orbF neq_ij eq_sym eq_jj' neq_kj'.
case: (i =P k) => // eq_ik; exists (j, i, j', true).
rewrite !scaler_sign !opprB /= !inE eq_sym negb_or neq_ij neq_jj'.
by rewrite eq_ik neq_kj'.
Qed.

Let vchar_isometry_base4 (eps : bool) i j k n m :
    let f1 := 'chi_j - 'chi_i in
    let f2 := 'chi_k - 'chi_i in
    let f3 := 'chi_n - 'chi_m in
    j != k -> '[f3, f1]_G = (-1) ^+ eps -> '[f3, f2] = (-1) ^+ eps -> 
  if eps then n == i else m == i.
Proof.
move=> /= Hjk; wlog ->: eps n m / eps = false.
  case: eps; last exact; move/(_ false m n)=> IH nm_ji nm_ki.
  by apply: IH; rewrite // -opprB cfdotNl (nm_ji, nm_ki) opprK.
rewrite !cfdotBl !cfdotBr !cfdot_irr !opprB addrAC addrA.
do 2!move/(canRL (subrK _)); rewrite -(natrD _ 1) -!natrD.
move/(can_inj natCK); case: (m == i) => //.
case: eqP => // ->; case: (j == i) => // _.
rewrite subr0 add0r => /(canRL (subrK _)); rewrite -(natrD _ 1).
by move/(can_inj natCK); rewrite (negbTE Hjk).
Qed.

(* This is Peterfalvi (1.4). *)
Lemma vchar_isometry_base m L (Chi : m.-tuple 'CF(H)) 
                            (tau : {linear 'CF(H) -> 'CF(G)}) :
    (1 < m)%N -> {subset Chi <= irr H} -> free Chi ->
    (forall chi, chi \in Chi -> chi 1%g = Chi`_0 1%g) ->
    (forall i : 'I_m, (Chi`_i - Chi`_0) \in 'CF(H, L)) ->
    {in 'Z[Chi, L], isometry tau, to 'Z[irr G, G^#]} ->
    exists2 mu : m.-tuple (Iirr G),
      uniq mu
    & exists epsilon : bool, forall i : 'I_m,
      tau (Chi`_i - Chi`_0) = (-1) ^+ epsilon *: ('chi_(mu`_i) - 'chi_(mu`_0)).
Proof. 
case: m Chi => [|[|m]] // Chi _ irrChi Chifree Chi1 ChiCF [iso_tau Ztau].
rewrite -(tnth_nth 0 _ 0); set chi := tnth Chi.
have chiE i: chi i = Chi`_i by rewrite -tnth_nth.
have inChi i: chi i \in Chi by exact: mem_tnth.
have{irrChi} irrChi i: chi i \in irr H by exact: irrChi.
have eq_chi i j: (chi i == chi j) = (i == j).
  by rewrite /chi !(tnth_nth 0) nth_uniq ?size_tuple ?free_uniq.
have dot_chi i j: '[chi i, chi j] = (i == j)%:R.
  rewrite -eq_chi; have [/irrP[{i}i ->] /irrP[{j}j ->]] := (irrChi i,irrChi j).
  by rewrite cfdot_irr inj_eq //; exact: irr_inj.
pose F i j := chi i - chi j.
have DF i j : F i j =  F i 0 - F j 0 by rewrite /F opprB addrA subrK.
have ZF i j: F i j \in 'Z[Chi, L].
  by rewrite zchar_split rpredB ?mem_zchar // DF memvB // /F !chiE.
have htau2 i j: i != j -> '[tau (F i j)] = 2%:R.
  rewrite iso_tau // cfnormB -cfdotC !dot_chi !eqxx eq_sym => /negbTE->.
  by rewrite -!natrD subr0.
have htau1 i j: j != 0 -> j != i -> i != 0 -> '[tau (F i 0), tau (F j 0)] = 1.
  rewrite iso_tau // cfdotBl !cfdotBr opprB !dot_chi !(eq_sym j).
  by do 3!move/negbTE->; rewrite !subr0 add0r.
have [m0 | nz_m] := boolP (m == 0%N).
  rewrite -2!eqSS eq_sym in m0; move: (htau2 1 0 isT).
  case/(vchar_norm2 (Ztau _ (ZF 1 0))) => [k1 [k0 neq_k01 eq_mu]].
  pose mu := @Tuple _ _ [:: k0; k1] m0.
  exists mu; first by rewrite /= andbT inE.
  exists false => i; rewrite scale1r chiE.
  have: (i : nat) \in iota 0 2 by rewrite mem_iota (eqP m0) (valP i).
  rewrite !inE; case/pred2P=> ->; first by rewrite !subrr linear0.
  by rewrite -eq_mu /F !chiE.
have m_gt2: (2 < m.+2)%N by rewrite !ltnS lt0n.
pose i2 := Ordinal m_gt2.
case: (@vchar_isometry_base3 (tau (F 1 0)) (tau (F i2 0))); auto.
case=> [[[k1 k0] k2] e] []; set d := (-1) ^+ e => eq10 eq20.
rewrite /= !inE => /and3P[/norP[nek10 nek12]]; rewrite eq_sym => nek20 _.
have muP i:
  {k | (i == 0) ==> (k == k0) & tau (F i 0) == d *: ('chi_k0 - 'chi_k)}.
- apply: sig2W; have [-> | nei0] := altP (i =P 0).
    by exists k0; rewrite ?eqxx // /F !subrr !linear0.
  have /(vchar_norm2 (Ztau _ (ZF i 0)))[k [k' nekk' eqFkk']] := htau2 i 0 nei0.
  have [-> | neq_i1] := eqVneq i 1; first by exists k1; rewrite // -eq10.
  have [-> | neq_i2] := eqVneq i i2; first by exists k2; rewrite // -eq20.
  have:= @vchar_isometry_base4 (~~ e) k0 k1 k2 k k' nek12.
  have ZdK u v w: '[u, v - w]_G = (-1) ^+ (~~ e) * '[u, d *: (w - v)].
    rewrite cfdotZr rmorph_sign mulrA -signr_addb addNb addbb mulN1r.
    by rewrite -cfdotNr opprB.
  rewrite -eqFkk' ZdK -eq10 {}ZdK -eq20 !htau1 //; try by rewrite eq_sym.
  move/(_ (mulr1 _) (mulr1 _)); rewrite /d eqFkk'.
  by case e => /eqP <-; [exists k | exists k']; rewrite ?scaler_sign ?opprB.
pose mu := [tuple of [seq s2val (muP i) | i <- ord_tuple m.+2]]; exists mu.
  rewrite map_inj_uniq ?enum_uniq // => i j.
  case: (muP i) (muP j) => /= ki _ /eqP eq_i0 [/= kj _ /eqP eq_j0] eq_kij.
  apply/eqP; rewrite -eq_chi -subr_eq0 -cfnorm_eq0 -iso_tau ?ZF //.
  rewrite -[chi i](subrK (chi 0)) -addrA linearD eq_i0 eq_kij -eq_j0.
  by rewrite -linearD -opprB subrr !raddf0.
exists (~~ e) => i; rewrite -addbT signr_addb -/d -scalerA scaleN1r opprB.
rewrite -!tnth_nth -/(F i 0) tnth_map tnth_ord_tuple.
suffices /= ->: mu`_0 = k0 by case: (muP i) => /= k _ /eqP.
rewrite -(tnth_nth 0 _ 0) tnth_map tnth_ord_tuple.
by case: (muP 0) => /= k /(k =P k0).
Qed.

(* This is Peterfalvi (1.5)(a). *)
Lemma cfResInd_sum_cfclass t : H <| G ->
  'Res[H] ('Ind[G] 'chi_t)
     = #|'I_G['chi_t] : H|%:R *: \sum_(xi <- ('chi_t ^: G)%CF) xi.
Proof.
set T := 'I_G['chi_t] => nsHG; have [sHG nHG] := andP nsHG.
apply/cfun_inP=> h Hh; rewrite cfResE ?cfIndE // cfunE sum_cfunE.
apply: (canLR (mulKf (neq0CG H))).
rewrite mulrA -natrM Lagrange ?sub_Inertia //= -/T reindex_cfclass //=.
rewrite mulr_sumr [s in _ = s]big_mkcond /= (reindex_inj invg_inj).
rewrite (partition_big (conjg_Iirr t) xpredT) //=; apply: eq_bigr => i _.
have [[y Gy chi_i] | not_i_t] := cfclassP _ _ _; last first.
  apply: big1 => z; rewrite groupV => /andP[Gz /eqP def_i].
  by case: not_i_t; exists z; rewrite // -def_i conjg_IirrE.
rewrite  -(card_rcoset _ y) mulr_natl -sumr_const; apply: eq_big => z.
  rewrite -(inj_eq irr_inj) conjg_IirrE chi_i mem_rcoset inE groupMr ?groupV //.
  apply: andb_id2l => Gz; rewrite eq_sym (cfConjg_eqE _ nsHG) //.
  by rewrite mem_rcoset inE groupM ?groupV.
rewrite groupV => /andP[Gz /eqP <-].
by rewrite conjg_IirrE cfConjgE ?(subsetP nHG).
Qed.

(* This is Peterfalvi (1.5)(b), main formula. *)
Lemma cfnorm_Ind_irr t :
  H <| G -> '['Ind[G] 'chi[H]_t] = #|'I_G['chi_t] : H|%:R.
Proof.
set r := _%:R => HnG; have HsG := normal_sub HnG.
rewrite -Frobenius_reciprocity cfResInd_sum_cfclass //= cfdotZr rmorph_nat -/r.
rewrite reindex_cfclass // cfdot_sumr (bigD1 t) ?cfclass_refl //= cfnorm_irr.
rewrite big1 ?addr0 ?mulr1 // => j /andP[_ /negbTE].
by rewrite eq_sym cfdot_irr => ->.
Qed.

(* This is Peterfalvi (1.5)(b), irreducibility remark. *)
Lemma inertia_Ind_irr t :
  H <| G -> 'I_G['chi[H]_t] \subset H -> 'Ind[G] 'chi_t \in irr G.
Proof.
rewrite -indexg_eq1 => nsHG /eqP r1.
by rewrite irrEchar cfInd_char ?irr_char //= cfnorm_Ind_irr ?r1.
Qed.

(* This is Peterfalvi (1.5)(c). *)
Lemma cfclass_Ind_cases t1 t2 : H <| G ->
   if 'chi_t2 \in ('chi[H]_t1 ^: G)%CF
   then 'Ind[G] 'chi_t1 = 'Ind[G] 'chi_t2 
   else '['Ind[G] 'chi_t1, 'Ind[G] 'chi_t2] = 0.
Proof.
move=> nsHG; have [/cfclass_Ind-> // | not_ch1Gt2] := ifPn.
rewrite -Frobenius_reciprocity cfResInd_sum_cfclass // cfdotZr rmorph_nat.
rewrite cfdot_sumr reindex_cfclass // big1 ?mulr0 // => j; rewrite cfdot_irr.
case: eqP => // <- /idPn[]; apply: contra not_ch1Gt2 => /cfclassP[y Gy ->].
by apply/cfclassP; exists y^-1%g; rewrite ?groupV ?cfConjgK.
Qed.

(* Useful consequences of (1.5)(c) *)
Lemma not_cfclass_Ind_ortho i j :
    H <| G -> ('chi_i \notin 'chi_j ^: G)%CF ->
  '['Ind[G, H] 'chi_i, 'Ind[G, H] 'chi_j] = 0. 
Proof. by move/(cfclass_Ind_cases i j); rewrite cfclass_sym; case: ifP. Qed.

Lemma cfclass_Ind_irrP i j :
    H <| G ->
  reflect ('Ind[G, H] 'chi_i = 'Ind[G, H] 'chi_j) ('chi_i \in 'chi_j ^: G)%CF.
Proof.
move=> nsHG; have [sHG _] := andP nsHG.
case: ifP (cfclass_Ind_cases j i nsHG) => [|_ Oji]; first by left.
right=> eq_chijG; have /negP[]: 'Ind[G] 'chi_i != 0 by exact: Ind_irr_neq0.
by rewrite -cfnorm_eq0 {1}eq_chijG Oji.
Qed.

Lemma card_imset_Ind_irr (calX : {set Iirr H}) :
    H <| G -> {in calX, forall i, 'Ind 'chi_i \in irr G} ->
    {in calX & G, forall i y, conjg_Iirr i y \in calX} ->
  #|calX| = (#|G : H| * #|[set cfIirr ('Ind[G] 'chi_i) | i in calX]|)%N.
Proof.
move=> nsHG irrIndX sXGX; have [sHG _] := andP nsHG; set f := fun i => cfIirr _.
rewrite -sum1_card (partition_big_imset f) /= mulnC -sum_nat_const.
apply: eq_bigr => _ /imsetP[i Xi ->]; transitivity (size (cfclass 'chi_i G)).
  rewrite -sum1_size reindex_cfclass //; apply: eq_bigl => j.
  case Xj: (j \in calX).
    rewrite -(inj_eq irr_inj) !(cfIirrPE irrIndX) //.
    exact/eqP/cfclass_Ind_irrP.
  apply/esym/(contraFF _ Xj)=> /cfclassP[y Gy Dj].
  by rewrite -conjg_IirrE in Dj; rewrite (irr_inj Dj) sXGX.
rewrite -(Lagrange_index (Inertia_sub G 'chi_i)) ?sub_Inertia //.
rewrite -size_cfclass ((#|_ : _| =P 1)%N _) ?muln1 // -eqC_nat.
by rewrite -cfnorm_Ind_irr // -(cfIirrPE irrIndX) ?cfnorm_irr.
Qed.

(* This is Peterfalvi (1.5)(d). *)
Lemma scaled_cfResInd_sum_cfclass t : H <| G ->
  let chiG := 'Ind[G] 'chi_t in
  (chiG 1%g / '[chiG]) *: 'Res[H] chiG
     = #|G : H|%:R *: (\sum_(xi <- ('chi_t ^: G)%CF) xi 1%g *: xi).
Proof.
move=> nsHG chiG; have [sHG _] := andP nsHG.
rewrite cfResInd_sum_cfclass // cfnorm_Ind_irr // scalerA cfInd1 //.
rewrite divfK ?pnatr_eq0 -?lt0n // -scalerA linear_sum !reindex_cfclass //=.
congr (_ *: _); apply: eq_bigr => _ /cfclassP[y _ ->].
by rewrite cfConjg1.
Qed.

(* This is Peterfalvi (1.5)(e). *)
Lemma odd_induced_orthogonal t :
     H <| G -> odd #|G| -> t != 0 ->
  '['Ind[G, H] 'chi_t, ('Ind[G] 'chi_t)^*] = 0. 
Proof.
move=> nsHG oddG nz_t; have [sHG _] := andP nsHG.
have:= cfclass_Ind_cases t (conjC_Iirr t) nsHG.
rewrite conjC_IirrE conj_cfInd; case: cfclassP => // [[g Gg id_cht]].
have oddH: odd #|H| := pgroup.oddSg sHG oddG.
case/eqP: nz_t; apply: irr_inj; rewrite irr0.
apply/eqP; rewrite -odd_eq_conj_irr1 // id_cht; apply/eqP.
have F1: ('chi_t ^ (g ^+ 2))%CF = 'chi_t.
  rewrite (cfConjgM _ nsHG) // -id_cht -conj_cfConjg -id_cht.
  exact: cfConjCK.
suffices /eqP->: g == ((g ^+ 2) ^+ #|G|./2.+1)%g.
  elim: _./2.+1 => [|n IHn]; first exact: cfConjgJ1.
  by rewrite expgS (cfConjgM _ nsHG) ?groupX // F1.
rewrite eq_mulVg1 expgS -expgM mul2n -mulgA mulKg -expgS -order_dvdn.
by rewrite -add1n -[1%N](congr1 nat_of_bool oddG) odd_double_half order_dvdG.
Qed.

(* This is Peterfalvi (1.6)(a). *)
Lemma sub_cfker_Ind_irr A i :
    H \subset G -> G \subset 'N(A) ->
  (A \subset cfker ('Ind[G, H] 'chi_i)) = (A \subset cfker 'chi_i).
Proof. by move=> sHG nAG; rewrite cfker_Ind_irr ?sub_gcore. Qed.

(* Some consequences and related results. *)
Lemma sub_cfker_Ind (A : {set gT}) chi :
    A \subset H -> H \subset G -> G \subset 'N(A) -> chi \is a character ->
  (A \subset cfker ('Ind[G, H] chi)) = (A \subset cfker chi).
Proof.
move=> sAH sHG nAG Nchi; have [-> | nz_chi] := eqVneq chi 0.
  by rewrite raddf0 !cfker_cfun0 !(subset_trans sAH).
by rewrite cfker_Ind ?sub_gcore.
Qed.

Lemma cfInd_irr_eq1 i :
  H <| G -> ('Ind[G, H] 'chi_i == 'Ind[G, H] 1) = (i == 0).
Proof.
case/andP=> sHG nHG; apply/eqP/idP=> [chi1 | /eqP->]; last by rewrite irr0.
rewrite -subGcfker -(sub_cfker_Ind_irr _ sHG nHG) chi1 -irr0.
by rewrite sub_cfker_Ind_irr ?cfker_irr0.
Qed.

Lemma sub_cfker_constt_Res_irr (A : {set gT}) i j :
    j \in irr_constt ('Res[H, G] 'chi_i) ->
    A \subset H -> H \subset G -> G \subset 'N(A) ->
  (A \subset cfker 'chi_j) = (A \subset cfker 'chi_i).
Proof.
move=> iHj sAH sHG nAG; apply/idP/idP=> kerA.
  have jGi: i \in irr_constt ('Ind 'chi_j) by rewrite constt_Ind_Res.
  rewrite (subset_trans _ (cfker_constt _ jGi)) ?cfInd_char ?irr_char //=.
  by rewrite sub_cfker_Ind_irr.
rewrite (subset_trans _ (cfker_constt _ iHj)) ?cfRes_char ?irr_char //=.
by rewrite cfker_Res ?irr_char // subsetI sAH.
Qed.

Lemma sub_cfker_constt_Ind_irr (A : {set gT}) i j :
    i \in irr_constt ('Ind[G, H] 'chi_j) ->
    A \subset H -> H \subset G -> G \subset 'N(A) ->
  (A \subset cfker 'chi_j) = (A \subset cfker 'chi_i).
Proof. by rewrite constt_Ind_Res; apply: sub_cfker_constt_Res_irr. Qed.

(* This is a stronger version of Peterfalvi (1.6)(b). *)
Lemma cfIndMod (K : {group gT}) (phi : 'CF(H / K)) :
    K \subset H -> H \subset G -> K <| G ->
  'Ind[G] (phi %% K)%CF = ('Ind[G / K] phi %% K)%CF.
Proof. by move=> sKH sHG /andP[_ nKG]; rewrite cfIndMorph ?ker_coset. Qed.

Lemma cfIndQuo (K : {group gT}) (phi : 'CF(H)) :
    K \subset cfker phi -> H \subset G -> K <| G ->
  'Ind[G / K] (phi / K)%CF = ('Ind[G] phi / K)%CF.
Proof.
move=> kerK sHG nsKG; have sKH := subset_trans kerK (cfker_sub phi).
have nsKH := normalS sKH sHG nsKG.
by apply: canRL (cfModK nsKG) _; rewrite -cfIndMod // cfQuoK.
Qed.

Section IndSumInertia.

Variable s : Iirr H.

Let theta := 'chi_s.
Let T := 'I_G[theta].
Let calA := irr_constt ('Ind[T] theta).
Let calB := irr_constt ('Ind[G] theta).
Let AtoB (t : Iirr T) := Ind_Iirr G t.
Let e_ t := '['Ind theta, 'chi[T]_t].

Hypothesis nsHG: H <| G.
(* begin hide *)
Let sHG : H \subset G. Proof. exact: normal_sub. Qed.
Let nHG : G \subset 'N(H). Proof. exact: normal_norm. Qed.
Let nsHT : H <| T. Proof. exact: normal_Inertia. Qed.
Let sHT : H \subset T. Proof. exact: normal_sub. Qed.
Let nHT : T \subset 'N(H). Proof. exact: normal_norm. Qed.
Let sTG : T \subset G. Proof. exact: subsetIl. Qed.
(* end hide *)

(* This is Peterfalvi (1.7)(a). *)
Lemma cfInd_sum_Inertia :
  [/\ {in calA, forall t, 'Ind 'chi_t \in irr G},
      {in calA, forall t, 'chi_(AtoB t) = 'Ind 'chi_t},
      {in calA &, injective AtoB},
      AtoB @: calA =i calB
    & 'Ind[G] theta = \sum_(t in calA) e_ t *: 'Ind 'chi_t].
Proof.
have [AtoBirr AtoBinj defB _ _] := constt_Inertia_bijection s nsHG.
split=> // [i Ai|]; first exact/cfIirrE/AtoBirr.
rewrite -(cfIndInd _ sTG sHT) {1}['Ind theta]cfun_sum_constt linear_sum.
by apply: eq_bigr => i _; rewrite linearZ.
Qed.

Hypothesis abTbar : abelian (T / H).

(* This is Peterfalvi (1.7)(b). *)
Lemma cfInd_central_Inertia :
   exists2 e, [/\ e \in Cnat, e != 0 & {in calA, forall t, e_ t = e}]
           & [/\ 'Ind[G] theta = e *: \sum_(j in calB) 'chi_j,
                 #|calB|%:R = #|T : H|%:R / e ^+ 2
               & {in calB, forall i, 'chi_i 1%g = #|G : T|%:R * e * theta 1%g}].
Proof.
have [t1 At1] := constt_cfInd_irr s sHT; pose psi1 := 'chi_t1.
pose e := '['Ind theta, psi1].
have NthT: 'Ind[T] theta \is a character by rewrite cfInd_char ?irr_char.
have Ne: e \in Cnat by rewrite Cnat_cfdot_char_irr.
have Dpsi1H: 'Res[H] psi1 = e *: theta.
  have psi1Hs: s \in irr_constt ('Res psi1) by rewrite -constt_Ind_Res.
  rewrite (Clifford_Res_sum_cfclass nsHT psi1Hs) cfclass_invariant ?subsetIr //.
  by rewrite big_seq1 cfdot_Res_l cfdotC conj_Cnat.
have linL j: 'chi[T / H]_j \is a linear_char by apply/char_abelianP.
have linLH j: ('chi_j %% H)%CF \is a linear_char := cfMod_lin_char (linL j).
pose LtoT (j : Iirr (T / H)) := mul_mod_Iirr t1 j.
have LtoTE j: 'chi_(LtoT j) = ('chi_j %% H)%CF * psi1.
  by rewrite !(mod_IirrE, cfIirrE) // mul_lin_irr ?mem_irr ?cfMod_lin_char.
have psiHG: 'Ind ('Res[H] psi1) = \sum_j 'chi_(LtoT j).
  transitivity ((cfReg (T / H) %% H)%CF * psi1); last first.
    rewrite cfReg_sum linear_sum /= mulr_suml; apply: eq_bigr => i _.
    by rewrite LtoTE // lin_char1 ?scale1r.
  apply/cfun_inP=> x Tx; rewrite cfunE cfModE // cfRegE mulrnAl mulrb.
  rewrite (sameP eqP (kerP _ (subsetP nHT x Tx))) ker_coset.
  case: ifPn => [Hx | H'x]; last by rewrite (cfun_on0 (cfInd_normal _  _)).
  rewrite card_quotient // -!(cfResE _ sHT) // cfRes_Ind_invariant ?cfunE //.
  by rewrite -subsetIidl (subset_trans _ (sub_inertia_Res _ _)) ?sub_Inertia.
have imLtoT: {subset calA <= codom LtoT}.
  move=> t At; apply/codomP/exists_eqP.
  have{At}: t \in irr_constt ('Ind ('Res[H] 'chi_t1)).
    by rewrite Dpsi1H linearZ irr_consttE cfdotZl mulf_neq0.
  apply: contraR; rewrite negb_exists => /forallP imL't.
  by rewrite psiHG cfdot_suml big1 // => j _; rewrite cfdot_irr mulrb ifN_eqC.
have De_ t: t \in calA -> e_ t = e.
  case/imLtoT/codomP=> j ->; rewrite /e_ LtoTE /e -!cfdot_Res_r rmorphM /=.
  by rewrite cfRes_sub_ker ?cfker_mod // mulr_algl lin_char1 ?scale1r.
have{imLtoT} A_1 t: t \in calA -> 'chi_t 1%g = e * theta 1%g.
  case/imLtoT/codomP=> j ->; rewrite LtoTE //= cfunE.
  by rewrite (lin_char1 (linLH j)) mul1r -(cfRes1 H) Dpsi1H cfunE.
exists e => //; have [_ defAtoB injAtoB imAtoB ->] := cfInd_sum_Inertia.
rewrite -(eq_bigl _ _ imAtoB) -(eq_card imAtoB) big_imset //= scaler_sumr.
split=> [||i]; first by apply: eq_bigr => t2 At2; rewrite De_ ?defAtoB.
  apply: (mulIf (irr1_neq0 s)); rewrite mulrAC -cfInd1 // mulr_natl mulrC invfM.
  rewrite ['Ind _]cfun_sum_constt sum_cfunE mulr_sumr card_in_imset //.
  rewrite -sumr_const; apply: eq_bigr => t At.
  by rewrite -mulrA -/(e_ t) De_ // cfunE A_1 ?mulKf.
by rewrite -imAtoB => /imsetP[t At ->]; rewrite defAtoB ?cfInd1 ?A_1 ?mulrA.
Qed.

(* This is Peterfalvi (1.7)(c). *)
Lemma cfInd_Hall_central_Inertia :
     Hall T H ->
  [/\ 'Ind[G] theta = \sum_(i in calB) 'chi_i, #|calB| = #|T : H| 
    & {in calB, forall i, 'chi_i 1%g = #|G : T|%:R * theta 1%g}].
Proof.
case/andP=> _ hallH; have [e [_ _ De]] := cfInd_central_Inertia.
suffices ->: e = 1.
  by case=> -> /eqP; rewrite scale1r expr1n divr1 mulr1 eqC_nat => /eqP.
suffices{De} [t Dtheta]: exists i, 'Res[H, T] 'chi_i = theta.
  have e_t_1: e_ t = 1 by rewrite /e_ -cfdot_Res_r Dtheta cfnorm_irr.
  by rewrite -(De t) // irr_consttE -/(e_ t) e_t_1 oner_eq0.
have ITtheta: T \subset 'I[theta] := subsetIr _ _.
have solT: solvable (T / H) := abelian_sol abTbar.
have [|t []] := extend_solvable_coprime_irr nsHT solT ITtheta; last by exists t.
rewrite coprime_sym coprime_mull !(coprime_dvdl _ hallH) ?cfDet_order_dvdG //.
by rewrite -dvdC_nat !CdivE truncCK ?Cnat_irr1 // dvd_irr1_cardG.
Qed.
  
End IndSumInertia.

(* This is Peterfalvi (1.8). *)
Lemma irr1_bound_quo (B C D : {group gT}) i :
    B <| C -> B \subset cfker 'chi[G]_i ->
    B \subset D -> D \subset C -> C \subset G -> (D / B \subset 'Z(C / B))%g ->
  'chi_i 1%g <= #|G : C|%:R * sqrtC #|C : D|%:R.
Proof.
move=> BnC BsK BsD DsC CsG QsZ.
case: (boolP ('Res[C] 'chi_i == 0))=> [HH|].
  have: ('Res[C] 'chi_i) 1%g = 0 by rewrite (eqP HH) cfunE.
  by rewrite cfResE // => HH1; case/eqP: (irr1_neq0 i).
have IC := cfRes_char C (irr_char i).
case/neq0_has_constt=> i1 Hi1.
have CIr: i \in irr_constt ('Ind[G] 'chi_i1).
  by rewrite inE /= -Frobenius_reciprocity /= cfdotC conjC_eq0.
have BsKi : B \subset cfker 'chi_i1.
  suff BsKri: B \subset cfker ('Res[C] 'chi_i).
    by apply: (subset_trans BsKri); exact: (cfker_constt _ Hi1).
  apply/subsetP=> g GiG.
  have F: g \in C by rewrite (subsetP (subset_trans BsD _)).
  rewrite cfkerEchar // inE F !cfResE //.
  by move: (subsetP BsK _ GiG); rewrite cfkerEirr inE.
pose i2 := quo_Iirr B i1.
have ZsC: 'Z(C / B)%g \subset 'Z('chi_i2)%CF.
    by rewrite -(cap_cfcenter_irr (C / B)); apply: bigcap_inf.
have CBsH: C :&: B \subset D.
    apply/subsetP=> g; rewrite inE; case/andP=> _ HH.
    by apply: (subsetP (BsD)).
have I1B: 'chi_i1 1%g ^+ 2 <= #|C : D|%:R.
  case: (irr1_bound i2)=> HH _; move: HH.
  have ->: 'chi_i2 1%g = 'chi_i1 1%g.
    by rewrite quo_IirrE // -(coset_id (group1 B)) cfQuoE.
  move/ler_trans; apply.
  rewrite ler_nat // -(index_quotient_eq CBsH) ?normal_norm //.
  rewrite -(@leq_pmul2l #|'Z('chi_i2)%CF|) ?cardG_gt0 ?cfcenter_sub //.
  rewrite  Lagrange ?quotientS ?cfcenter_sub //.
  rewrite -(@leq_pmul2l #|(D / B)%g|) ?cardG_gt0 //.
  rewrite mulnA mulnAC Lagrange ?quotientS //.
  rewrite mulnC leq_pmul2l ?cardG_gt0 // subset_leq_card //.
  exact: subset_trans QsZ ZsC.
have IC': 'Ind[G] 'chi_i1 \is a character := cfInd_char G (irr_char i1).
move: (char1_ge_constt IC' CIr); rewrite cfInd1 //= => /ler_trans-> //.
have chi1_1_ge0: 0 <= 'chi_i1 1%g by rewrite ltrW ?irr1_gt0.
rewrite ler_pmul2l ?gt0CiG //.
by rewrite -(@ler_pexpn2r _ 2) -?topredE /= ?sqrtC_ge0 ?ler0n ?sqrtCK.
Qed.

(* This is Peterfalvi (1.9)(a). *)
Lemma extend_coprime_Qn_aut a b (Qa Qb : fieldExtType rat) w_a w_b
          (QaC : {rmorphism Qa -> algC}) (QbC : {rmorphism Qb -> algC})
          (mu : {rmorphism algC -> algC}) :
    coprime a b ->
    a.-primitive_root w_a /\ <<1; w_a>>%VS = {:Qa}%VS -> 
    b.-primitive_root w_b /\ <<1; w_b>>%VS = {:Qb}%VS ->
  {nu : {rmorphism algC -> algC} | forall x, nu (QaC x) = mu (QaC x)
                                 & forall y, nu (QbC y) = QbC y}.
Proof.
move=> coab [pr_w_a genQa] [pr_w_b genQb].
have [k co_k_a Dmu]: {k | coprime k a & mu (QaC w_a) = QaC (w_a ^+ k)}.
  have prCw: a.-primitive_root (QaC w_a) by rewrite fmorph_primitive_root.
  by have [k coka ->] := aut_prim_rootP mu prCw; rewrite -rmorphX; exists k.
pose k1 := chinese a b k 1; have /Qn_aut_exists[nu Dnu]: coprime k1 (a * b).
  rewrite coprime_mulr -!(coprime_modl k1) chinese_modl ?chinese_modr //.
  by rewrite !coprime_modl co_k_a coprime1n.
exists nu => [x | y].
  have /Fadjoin_polyP[p Qp ->]: x \in <<1; w_a>>%VS by rewrite genQa memvf.
  rewrite -!horner_map -!map_poly_comp !map_Qnum_poly // Dmu Dnu -rmorphX /=.
    by rewrite -(prim_expr_mod pr_w_a) chinese_modl // prim_expr_mod.
  by rewrite exprM (prim_expr_order pr_w_a) expr1n rmorph1.
have /Fadjoin_polyP[p Qp ->]: y \in <<1; w_b>>%VS by rewrite genQb memvf.
rewrite -!horner_map -!map_poly_comp !map_Qnum_poly // Dnu -rmorphX /=.
  by rewrite -(prim_expr_mod pr_w_b) chinese_modr // prim_expr_mod.
by rewrite mulnC exprM (prim_expr_order pr_w_b) expr1n rmorph1.
Qed.

(* This intermediate result in the proof of Peterfalvi (1.9)(b) is used in    *)
(* he proof of (3.9)(c).                                                      *)
Lemma dvd_restrict_cfAut a (v : {rmorphism algC -> algC}) :
  exists2 u : {rmorphism algC -> algC},
    forall gT0 G0 chi x,
      chi \in 'Z[irr (@gval gT0 G0)] -> #[x] %| a -> u (chi x) = v (chi x)
  & forall chi x, chi \in 'Z[irr G] -> coprime #[x] a -> u (chi x) = chi x.
Proof.
have [-> | a_gt0] := posnP a.
  exists v => // chi x Zchi; rewrite /coprime gcdn0 order_eq1 => /eqP->.
  by rewrite aut_Cint ?Cint_vchar1.
pose b := (#|G|`_(\pi(a)^'))%N.
have co_a_b: coprime a b := pnat_coprime (pnat_pi a_gt0) (part_pnat _ _).
have [Qa _ [QaC _ [w_a genQa memQa]]] := group_num_field_exists [group of Zp a].
have [Qb _ [QbC _ [w_b genQb memQb]]] := group_num_field_exists [group of Zp b].
rewrite !card_Zp ?part_gt0 // in Qa QaC w_a genQa memQa Qb QbC w_b genQb memQb.
have [nu nuQa nuQb] := extend_coprime_Qn_aut QaC QbC v co_a_b genQa genQb.
exists nu => [gt0 G0 chi x Zchi x_dv_a | chi x Zchi co_x_a].
  without loss{Zchi} Nchi: chi / chi \is a character.
    move=> IH; case/vcharP: Zchi => [chi1 Nchi1 [chi2 Nchi2 ->]].
    by rewrite !cfunE !rmorphB !IH.
  by have [xa <-] := memQa _ _ _ Nchi x x_dv_a; rewrite nuQa.
without loss{Zchi} Nchi: chi / chi \is a character.
  move=> IH; case/vcharP: Zchi => [chi1 Nchi1 [chi2 Nchi2 ->]].
  by rewrite !cfunE rmorphB !IH.
have [Gx | /cfun0->] := boolP (x \in G); last by rewrite rmorph0.
have{Gx} x_dv_b: (#[x] %| b)%N.
  rewrite coprime_sym coprime_pi' // in co_x_a.
  by rewrite -(part_pnat_id co_x_a) partn_dvd ?order_dvdG.
by have [xb <-] := memQb _ _ _ Nchi x x_dv_b; rewrite nuQb.
Qed.

(* This is Peterfalvi (1.9)(b). *)
(* We have strengthened the statement of this lemma so that it can be used    *)
(* rather than reproved for Peterfalvi (3.9). In particular we corrected a    *)
(* quantifier inversion in the original statement: the automorphism is        *)
(* constructed uniformly for all (virtual) characters. We have also removed   *)
(* the spurrious condition that a be a \pi(a) part of #|G| -- the proof works *)
(* for all a, and indeed the first part holds uniformaly for all groups!      *)
Lemma make_pi_cfAut a k :
    coprime k a ->
  exists2 u : {rmorphism algC -> algC},
    forall (gT0 : finGroupType) (G0 : {group gT0}) chi x,
      chi \in 'Z[irr G0] -> #[x] %| a -> cfAut u chi x = chi (x ^+ k)%g
  & forall chi x, chi \in 'Z[irr G] -> coprime #[x] a -> cfAut u chi x = chi x.
Proof.
move=> co_k_a; have [v Dv] := Qn_aut_exists co_k_a.
have [u Du_a Du_a'] := dvd_restrict_cfAut a v.
exists u => [gt0 G0 | ] chi x Zchi a_x; last by rewrite cfunE Du_a'.
rewrite cfunE {u Du_a'}Du_a //.
without loss{Zchi} Nchi: chi / chi \is a character.
  move=> IH; case/vcharP: Zchi => [chi1 Nchi1 [chi2 Nchi2 ->]].
  by rewrite !cfunE rmorphB !IH.
have [sXG0 | G0'x] := boolP (<[x]> \subset G0); last first.
  have /(<[x]> =P _) gen_xk: generator <[x]> (x ^+ k).
    by rewrite generator_coprime coprime_sym (coprime_dvdr a_x).
  by rewrite !cfun0 ?rmorph0 -?cycle_subG -?gen_xk.
rewrite -!(cfResE chi sXG0) ?cycle_id ?mem_cycle //.
rewrite ['Res _]cfun_sum_cfdot !sum_cfunE rmorph_sum; apply: eq_bigr => i _.
have chiX := lin_charX (char_abelianP _ (cycle_abelian x) i) _ (cycle_id x).
rewrite !cfunE rmorphM aut_Cnat ?Cnat_cfdot_char_irr ?cfRes_char //.
by congr (_ * _); rewrite Dv -chiX // -expg_mod_order (eqnP a_x) chiX.
Qed.

Section ANT.
Import ssrint.

(* This section covers Peterfalvi (1.10). *)
(* We have simplified the statement somewhat by substituting the global ring  *)
(* of algebraic integers for the specific ring Z[eta]. Formally this amounts  *)
(* to strengthening (b) and weakening (a) accordingly, but since actually the *)
(* Z[eta] is equal to the ring of integers of Q[eta] (cf. Theorem 6.4 in J.S. *)
(* Milne's course notes on Algebraic Number Theory), the simplified statement *)
(* is actually equivalent to the textbook one.                                *)
Variable (p : nat) (eps : algC).
Hypothesis (pr_eps : p.-primitive_root eps).
Local Notation e := (1 - eps).

(* This is Peterfalvi (1.10) (a). *)
Lemma vchar_ker_mod_prim : {in G & G & 'Z[irr G], forall x y (chi : 'CF(G)),
  #[x] = p -> y \in 'C[x] -> chi (x * y)%g == chi y %[mod e]}%A.
Proof.
move=> x y chi Gx Gy Zchi ox cxy; pose X := <<[set x; y]>>%G.
have [Xx Xy]: x \in X /\ y \in X by apply/andP; rewrite -!sub1set -join_subG.
have sXG: X \subset G by rewrite join_subG !sub1set Gx.
suffices{chi Zchi} IHiX i: ('chi[X]_i (x * y)%g == 'chi_i y %[mod e])%A.
  rewrite -!(cfResE _ sXG) ?groupM //.
  have irr_free := (free_uniq (basis_free (irr_basis X))).
  have [c Zc ->] := (zchar_expansion irr_free (cfRes_vchar X Zchi)).
  rewrite !sum_cfunE /eqAmod -sumrB big_seq rpred_sum // => _  /irrP[i ->].
  by rewrite !cfunE [(_ %| _)%A]eqAmodMl // rpred_Cint.
have lin_chi: 'chi_i \is a linear_char.
  apply/char_abelianP; rewrite -[gval X]joing_idl -joing_idr abelianY.
  by rewrite !cycle_abelian cycle_subG /= cent_cycle.
rewrite lin_charM // -{2}['chi_i y]mul1r eqAmodMr ?Aint_irr //.
have [|k ->] := (prim_rootP pr_eps) ('chi_i x).
  by rewrite -lin_charX // -ox expg_order lin_char1.
rewrite -[_ ^+ k](subrK 1) subrX1 -[_ - 1]opprB mulNr -mulrN mulrC.
rewrite eqAmod_addl_mul // rpredN rpred_sum // => n _.
by rewrite rpredX ?(Aint_prim_root pr_eps).
Qed.

(* This is Peterfalvi (1.10)(b); the primality condition is only needed here. *)
Lemma int_eqAmod_prime_prim n :
  prime p -> n \in Cint -> (n == 0 %[mod e])%A -> (p %| n)%C.
Proof.
move=> p_pr Zn; rewrite /eqAmod unfold_in subr0.
have p_gt0 := prime_gt0 p_pr.
case: ifPn => [_ /eqP->// | nz_e e_dv_n].
suffices: (n ^+ p.-1 == 0 %[mod p])%A.
  rewrite eqAmod0_rat ?rpredX ?rpred_nat 1?rpred_Cint // !dvdC_int ?rpredX //.
  by rewrite floorCX // abszX Euclid_dvdX // => /andP[].
rewrite /eqAmod subr0 unfold_in pnatr_eq0 eqn0Ngt p_gt0 /=.
pose F := \prod_(1 <= i < p) ('X - (eps ^+ i)%:P).
have defF: F = \sum_(i < p) 'X^i.
  apply: (mulfI (monic_neq0 (monicXsubC 1))); rewrite -subrX1.
  by rewrite -(factor_Xn_sub_1 pr_eps) big_ltn.
have{defF} <-: F.[1] = p :> Algebraics.divisor.
  rewrite -[p]card_ord -[rhs in _ = rhs]sumr_const defF horner_sum.
  by apply: eq_bigr => i _; rewrite hornerXn expr1n.
rewrite -[p.-1]card_ord {F}horner_prod big_add1 big_mkord -prodfV.
rewrite -prodr_const -big_split rpred_prod //= => k _; rewrite !hornerE.
rewrite -[n](divfK nz_e) -[_ * _ / _]mulrA rpredM {e_dv_n}//.
have p'k: ~~ (p %| k.+1)%N by rewrite gtnNdvd // -{2}(prednK p_gt0) ltnS.
have [r {1}->]: exists r, eps = eps ^+ k.+1 ^+ r.
  have [q _ /dvdnP[r Dr]] := Bezoutl p (ltn0Sn k); exists r; apply/esym/eqP.
  rewrite -exprM (eq_prim_root_expr pr_eps _ 1) mulnC -Dr addnC gcdnC.
  by rewrite -prime_coprime // in p'k; rewrite (eqnP p'k) modnMDl.
rewrite -[1 - _]opprB subrX1 -mulNr opprB mulrC.
rewrite mulKf; last by rewrite subr_eq0 eq_sym -(prim_order_dvd pr_eps).
by apply: rpred_sum => // i _; rewrite !rpredX ?(Aint_prim_root pr_eps).
Qed.

End ANT.

End Main.


