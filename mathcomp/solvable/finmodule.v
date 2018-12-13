(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun eqtype ssrnat seq path div choice.
From mathcomp
Require Import fintype bigop ssralg finset fingroup morphism perm.
From mathcomp
Require Import finalg action gproduct commutator cyclic.

(******************************************************************************)
(*  This file regroups constructions and results that are based on the most   *)
(* primitive version of representation theory -- viewing an abelian group as  *)
(* the additive group of a (finite) Z-module. This includes the Gaschutz      *)
(* splitting and transitivity theorem, from which we will later derive the    *)
(* Schur-Zassenhaus theorem and the elementary abelian special case of        *)
(* Maschke's theorem, the coprime abelian centraliser/commutator trivial      *)
(* intersection theorem, which is used to show that p-groups under coprime    *)
(* action factor into special groups, and the construction of the transfer    *)
(* homomorphism and its expansion relative to a cycle, from which we derive   *)
(* the Higman Focal Subgroup and the Burnside Normal Complement theorems.     *)
(*   The definitions and lemmas for the finite Z-module induced by an abelian *)
(* are packaged in an auxiliary FiniteModule submodule: they should not be    *)
(* needed much outside this file, which contains all the results that exploit *)
(* this construction.                                                         *)
(*   FiniteModule defines the Z[N(A)]-module associated with a finite abelian *)
(* abelian group A, given a proof (abelA : abelian A) :                       *)
(*  fmod_of abelA == the type of elements of the module (similar to but       *)
(*                   distinct from [subg A]).                                 *)
(*   fmod abelA x == the injection of x into fmod_of abelA if x \in A, else 0 *)
(*        fmval u == the projection of u : fmod_of abelA onto A               *)
(*         u ^@ x == the action of x \in 'N(A) on u : fmod_of abelA           *)
(* The transfer morphism is be constructed from a morphism f : H >-> rT, and  *)
(* a group G, along with the two assumptions sHG : H \subset G and            *)
(* abfH : abelian (f @* H):                                                   *)
(*  transfer sGH abfH == the function gT -> FiniteModule.fmod_of abfH that    *)
(*                   implements the transfer morphism induced by f on G.      *)
(* The Lemma transfer_indep states that the transfer morphism can be expanded *)
(* using any transversal of the partition HG := rcosets H G of G.             *)
(*   Further, for any g \in G, HG :* <[g]> is also a partition of G (Lemma    *)
(* rcosets_cycle_partition), and for any transversal X of HG :* <[g]> the     *)
(* function r mapping x : gT to rcosets (H :* x) <[g]> is (constructively) a  *)
(* bijection from X to the <[g]>-orbit partition of HG, and Lemma             *)
(* transfer_pcycle_def gives a simplified expansion of the transfer morphism. *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory FinRing.Theory.
Local Open Scope ring_scope.

Module FiniteModule.

Reserved Notation "u ^@ x" (at level 31, left associativity).

Inductive fmod_of (gT : finGroupType) (A : {group gT}) (abelA : abelian A) :=
  Fmod x & x \in A.

Bind Scope ring_scope with fmod_of.

Section OneFinMod.

Let f2sub (gT : finGroupType) (A : {group gT}) (abA : abelian A) :=
  fun u : fmod_of abA => let : Fmod x Ax := u in Subg Ax : FinGroup.arg_sort _.
Local Coercion f2sub : fmod_of >-> FinGroup.arg_sort.

Variables (gT : finGroupType) (A : {group gT}) (abelA : abelian A).
Local Notation fmodA := (fmod_of abelA).
Implicit Types (x y z : gT) (u v w : fmodA).

Let sub2f (s : [subg A]) := Fmod abelA (valP s).

Definition fmval u := val (f2sub u).
Canonical fmod_subType := [subType for fmval].
Local Notation valA := (@val _ _ fmod_subType) (only parsing).
Definition fmod_eqMixin := Eval hnf in [eqMixin of fmodA by <:].
Canonical fmod_eqType := Eval hnf in EqType fmodA fmod_eqMixin.
Definition fmod_choiceMixin := [choiceMixin of fmodA by <:].
Canonical fmod_choiceType := Eval hnf in ChoiceType fmodA fmod_choiceMixin.
Definition fmod_countMixin := [countMixin of fmodA by <:].
Canonical fmod_countType := Eval hnf in CountType fmodA fmod_countMixin.
Canonical fmod_subCountType := Eval hnf in [subCountType of fmodA].
Definition fmod_finMixin := [finMixin of fmodA by <:].
Canonical fmod_finType := Eval hnf in FinType fmodA fmod_finMixin.
Canonical fmod_subFinType := Eval hnf in [subFinType of fmodA].

Definition fmod x := sub2f (subg A x).
Definition actr u x := if x \in 'N(A) then fmod (fmval u ^ x) else u.

Definition fmod_opp u := sub2f u^-1.
Definition fmod_add u v := sub2f (u * v).

Fact fmod_add0r : left_id (sub2f 1) fmod_add.
Proof. by move=> u; apply: val_inj; apply: mul1g. Qed.

Fact fmod_addrA : associative fmod_add.
Proof. by move=> u v w; apply: val_inj; apply: mulgA. Qed.

Fact fmod_addNr : left_inverse (sub2f 1) fmod_opp fmod_add.
Proof. by move=> u; apply: val_inj; apply: mulVg. Qed.

Fact fmod_addrC : commutative fmod_add.
Proof. by case=> x Ax [y Ay]; apply: val_inj; apply: (centsP abelA). Qed.

Definition fmod_zmodMixin := 
  ZmodMixin fmod_addrA fmod_addrC fmod_add0r fmod_addNr.
Canonical fmod_zmodType := Eval hnf in ZmodType fmodA fmod_zmodMixin.
Canonical fmod_finZmodType := Eval hnf in [finZmodType of fmodA].
Canonical fmod_baseFinGroupType :=
  Eval hnf in [baseFinGroupType of fmodA for +%R].
Canonical fmod_finGroupType :=
  Eval hnf in [finGroupType of fmodA for +%R].

Lemma fmodP u : val u \in A. Proof. exact: valP. Qed.
Lemma fmod_inj : injective fmval. Proof. exact: val_inj. Qed.
Lemma congr_fmod u v : u = v -> fmval u = fmval v.
Proof. exact: congr1. Qed.

Lemma fmvalA : {morph valA : x y / x + y >-> (x * y)%g}. Proof. by []. Qed.
Lemma fmvalN : {morph valA : x / - x >-> x^-1%g}. Proof. by []. Qed.
Lemma fmval0 : valA 0 = 1%g. Proof. by []. Qed.
Canonical fmval_morphism := @Morphism _ _ setT fmval (in2W fmvalA).

Definition fmval_sum := big_morph fmval fmvalA fmval0.

Lemma fmvalZ n : {morph valA : x / x *+ n >-> (x ^+ n)%g}.
Proof. by move=> u; rewrite /= morphX ?inE. Qed.

Lemma fmodKcond x : val (fmod x) = if x \in A then x else 1%g.
Proof. by rewrite /= /fmval /= val_insubd. Qed.
Lemma fmodK : {in A, cancel fmod val}. Proof. exact: subgK. Qed.
Lemma fmvalK : cancel val fmod.
Proof. by case=> x Ax; apply: val_inj; rewrite /fmod /= sgvalK. Qed.
Lemma fmod1 : fmod 1 = 0. Proof. by rewrite -fmval0 fmvalK. Qed.
Lemma fmodM : {in A &, {morph fmod : x y / (x * y)%g >-> x + y}}.
Proof. by move=> x y Ax Ay /=; apply: val_inj; rewrite /fmod morphM. Qed.
Canonical fmod_morphism := Morphism fmodM.
Lemma fmodX n : {in A, {morph fmod : x / (x ^+ n)%g >-> x *+ n}}.
Proof. exact: morphX. Qed.
Lemma fmodV : {morph fmod : x / x^-1%g >-> - x}.
Proof.
move=> x; apply: val_inj; rewrite fmvalN !fmodKcond groupV.
by case: (x \in A); rewrite ?invg1.
Qed.

Lemma injm_fmod : 'injm fmod.
Proof.
by apply/injmP=> x y Ax Ay []; move/val_inj; apply: (injmP (injm_subg A)).
Qed.

Notation "u ^@ x" := (actr u x) : ring_scope.

Lemma fmvalJcond u x :
  val (u ^@ x) = if x \in 'N(A) then val u ^ x else val u.
Proof. by case: ifP => Nx; rewrite /actr Nx ?fmodK // memJ_norm ?fmodP. Qed.

Lemma fmvalJ u x : x \in 'N(A) -> val (u ^@ x) = val u ^ x.
Proof. by move=> Nx; rewrite fmvalJcond Nx. Qed.

Lemma fmodJ x y : y \in 'N(A) -> fmod (x ^ y) = fmod x ^@ y.
Proof.
move=> Ny; apply: val_inj; rewrite fmvalJ ?fmodKcond ?memJ_norm //.
by case: ifP => // _; rewrite conj1g.
Qed.

Fact actr_is_action : is_action 'N(A) actr.
Proof.
split=> [a u v eq_uv_a | u a b Na Nb].
  case Na: (a \in 'N(A)); last by rewrite /actr Na in eq_uv_a.
  by apply: val_inj; apply: (conjg_inj a); rewrite -!fmvalJ ?eq_uv_a.
by apply: val_inj; rewrite !fmvalJ ?groupM ?conjgM.
Qed.

Canonical actr_action := Action actr_is_action.
Notation "''M'" := actr_action (at level 8) : action_scope.

Lemma act0r x : 0 ^@ x = 0.
Proof. by rewrite /actr conj1g morph1 if_same. Qed.

Lemma actAr x : {morph actr^~ x : u v / u + v}.
Proof.
by move=> u v; apply: val_inj; rewrite !(fmvalA, fmvalJcond) conjMg; case: ifP.
Qed.

Definition actr_sum x := big_morph _ (actAr x) (act0r x).

Lemma actNr x : {morph actr^~ x : u / - u}.
Proof. by move=> u; apply: (addrI (u ^@ x)); rewrite -actAr !subrr act0r. Qed.

Lemma actZr x n : {morph actr^~ x : u / u *+ n}.
Proof.
by move=> u; elim: n => [|n IHn]; rewrite ?act0r // !mulrS actAr IHn.
Qed.

Fact actr_is_groupAction : is_groupAction setT 'M.
Proof.
move=> a Na /=; rewrite inE; apply/andP; split.
  by apply/subsetP=> u _; rewrite inE.
by apply/morphicP=> u v _ _; rewrite !permE /= actAr.
Qed.

Canonical actr_groupAction := GroupAction actr_is_groupAction.
Notation "''M'" := actr_groupAction (at level 8) : groupAction_scope.

Lemma actr1 u : u ^@ 1 = u.
Proof. exact: act1. Qed.

Lemma actrM : {in 'N(A) &, forall x y u, u ^@ (x * y) = u ^@ x ^@ y}.
Proof.
by move=> x y Nx Ny /= u; apply: val_inj; rewrite !fmvalJ ?conjgM ?groupM.
Qed.

Lemma actrK x : cancel (actr^~ x) (actr^~ x^-1%g).
Proof.
move=> u; apply: val_inj; rewrite !fmvalJcond groupV.
by case: ifP => -> //; rewrite conjgK.
Qed.

Lemma actrKV x : cancel (actr^~ x^-1%g) (actr^~ x).
Proof. by move=> u; rewrite /= -{2}(invgK x) actrK. Qed.

End OneFinMod.

Bind Scope ring_scope with fmod_of.
Prenex Implicits fmval fmod actr.
Notation "u ^@ x" := (actr u x) : ring_scope.
Notation "''M'" := actr_action (at level 8) : action_scope.
Notation "''M'" := actr_groupAction : groupAction_scope.

End FiniteModule.

Canonical FiniteModule.fmod_subType.
Canonical FiniteModule.fmod_eqType.
Canonical FiniteModule.fmod_choiceType.
Canonical FiniteModule.fmod_countType.
Canonical FiniteModule.fmod_finType.
Canonical FiniteModule.fmod_subCountType.
Canonical FiniteModule.fmod_subFinType.
Canonical FiniteModule.fmod_zmodType.
Canonical FiniteModule.fmod_finZmodType.
Canonical FiniteModule.fmod_baseFinGroupType.
Canonical FiniteModule.fmod_finGroupType.

Arguments FiniteModule.fmodK {gT A} abelA [x] Ax.
Arguments FiniteModule.fmvalK {gT A abelA} x.
Arguments FiniteModule.actrK {gT A abelA} x.
Arguments FiniteModule.actrKV {gT A abelA} x.

(* Still allow ring notations, but give priority to groups now. *)
Import FiniteModule GroupScope.

Section Gaschutz.

Variables (gT : finGroupType) (G H P : {group gT}).
Implicit Types K L : {group gT}.

Hypotheses (nsHG : H <| G) (sHP : H \subset P) (sPG : P \subset G).
Hypotheses (abelH : abelian H) (coHiPG : coprime #|H| #|G : P|).

Let sHG := normal_sub nsHG.
Let nHG := subsetP (normal_norm nsHG).

Let m := (expg_invn H #|G : P|).

Implicit Types a b : fmod_of abelH.
Local Notation fmod := (fmod abelH).

Theorem Gaschutz_split : [splits G, over H] = [splits P, over H].
Proof.
apply/splitsP/splitsP=> [[K /complP[tiHK eqHK]] | [Q /complP[tiHQ eqHQ]]].
  exists (K :&: P)%G; rewrite inE setICA (setIidPl sHP) setIC tiHK eqxx.
  by rewrite group_modl // eqHK (sameP eqP setIidPr).
have sQP: Q \subset P by rewrite -eqHQ mulG_subr.
pose rP x := repr (P :* x); pose pP x := x * (rP x)^-1.
have PpP x: pP x \in P by rewrite -mem_rcoset rcoset_repr rcoset_refl.
have rPmul x y: x \in P -> rP (x * y) = rP y.
  by move=> Px; rewrite /rP rcosetM rcoset_id.
pose pQ x := remgr H Q x; pose rH x := pQ (pP x) * rP x.
have pQhq: {in H & Q, forall h q, pQ (h * q) = q} by apply: remgrMid.
have pQmul: {in P &, {morph pQ : x y / x * y}}.
  by apply: remgrM; [apply/complP | apply: normalS (nsHG)].
have HrH x: rH x \in H :* x.
  by rewrite rcoset_sym mem_rcoset invMg mulgA mem_divgr // eqHQ PpP.
have GrH x: x \in G -> rH x \in G.
  move=> Gx; case/rcosetP: (HrH x) => y Hy ->.
  by rewrite groupM // (subsetP sHG).
have rH_Pmul x y: x \in P -> rH (x * y) = pQ x * rH y.
  by move=> Px; rewrite /rH mulgA -pQmul; first by rewrite /pP rPmul ?mulgA.
have rH_Hmul h y: h \in H -> rH (h * y) = rH y.
  by move=> Hh; rewrite rH_Pmul ?(subsetP sHP) // -(mulg1 h) pQhq ?mul1g.
pose mu x y := fmod ((rH x * rH y)^-1 * rH (x * y)).
pose nu y := (\sum_(Px in rcosets P G) mu (repr Px) y)%R.
have rHmul: {in G &, forall x y, rH (x * y) = rH x * rH y * val (mu x y)}.
  move=> x y Gx Gy; rewrite /= fmodK ?mulKVg // -mem_lcoset lcoset_sym.
  rewrite -norm_rlcoset; last by rewrite nHG ?GrH ?groupM.
  by rewrite (rcoset_eqP (HrH _)) -rcoset_mul ?nHG ?GrH // mem_mulg.
have actrH a x: x \in G -> (a ^@ rH x = a ^@ x)%R.
  move=> Gx; apply: val_inj; rewrite /= !fmvalJ ?nHG ?GrH //.
  case/rcosetP: (HrH x) => b /(fmodK abelH) <- ->; rewrite conjgM.
  by congr (_ ^ _); rewrite conjgE -fmvalN -!fmvalA (addrC a) addKr.
have mu_Pmul x y z: x \in P -> mu (x * y) z = mu y z.
  move=> Px; congr fmod; rewrite -mulgA !(rH_Pmul x) ?rPmul //.
  by rewrite -mulgA invMg -mulgA mulKg.
have mu_Hmul x y z: x \in G -> y \in H -> mu x (y * z) = mu x z.
  move=> Gx Hy; congr fmod; rewrite (mulgA x) (conjgCV x) -mulgA 2?rH_Hmul //.
  by rewrite -mem_conjg (normP _) ?nHG.
have{mu_Hmul} nu_Hmul y z: y \in H -> nu (y * z) = nu z.
  move=> Hy; apply: eq_bigr => _ /rcosetsP[x Gx ->]; apply: mu_Hmul y z _ Hy.
  by rewrite -(groupMl _ (subsetP sPG _ (PpP x))) mulgKV.
have cocycle_mu: {in G & &, forall x y z,
  mu (x * y)%g z + mu x y ^@ z = mu y z + mu x (y * z)%g}%R.
- move=> x y z Gx Gy Gz; apply: val_inj.
  apply: (mulgI (rH x * rH y * rH z)).
  rewrite -(actrH _ _ Gz) addrC fmvalA fmvalJ ?nHG ?GrH //.
  rewrite mulgA -(mulgA _ (rH z)) -conjgC mulgA -!rHmul ?groupM //.
  by rewrite mulgA -mulgA -2!(mulgA (rH x)) -!rHmul ?groupM.
move: mu => mu in rHmul mu_Pmul cocycle_mu nu nu_Hmul.
have{cocycle_mu} cocycle_nu: {in G &, forall y z,
  nu z + nu y ^@ z = mu y z *+ #|G : P| + nu (y * z)%g}%R.
- move=> y z Gy Gz; rewrite /= (actr_sum z) /=.
  have ->: (nu z = \sum_(Px in rcosets P G) mu (repr Px * y)%g z)%R.
    rewrite /nu (reindex_acts _ (actsRs_rcosets P G) Gy) /=.
    apply: eq_bigr => _ /rcosetsP[x Gx /= ->].
    rewrite rcosetE -rcosetM.
    case: repr_rcosetP=> p1 Pp1; case: repr_rcosetP=> p2 Pp2.
    by rewrite -mulgA [x * y]lock !mu_Pmul.
  rewrite -sumr_const -!big_split /=; apply: eq_bigr => _ /rcosetsP[x Gx ->].
  rewrite -cocycle_mu //; case: repr_rcosetP => p1 Pp1.
  by rewrite groupMr // (subsetP sPG).
move: nu => nu in nu_Hmul cocycle_nu.
pose f x := rH x * val (nu x *+ m)%R.
have{cocycle_nu} fM: {in G &, {morph f : x y / x * y}}.
  move=> x y Gx Gy; rewrite /f ?rHmul // -3!mulgA; congr (_ * _).
  rewrite (mulgA _ (rH y)) (conjgC _ (rH y)) -mulgA; congr (_ * _).
  rewrite -fmvalJ ?actrH ?nHG ?GrH // -!fmvalA actZr -mulrnDl.
  rewrite -(addrC (nu y)) cocycle_nu // mulrnDl !fmvalA; congr (_ * _).
  by rewrite !fmvalZ expgK ?fmodP.
exists (Morphism fM @* G)%G; apply/complP; split.
  apply/trivgP/subsetP=> x /setIP[Hx /morphimP[y _ Gy eq_x]].
  apply/set1P; move: Hx; rewrite {x}eq_x /= groupMr ?subgP //.
  rewrite -{1}(mulgKV y (rH y)) groupMl -?mem_rcoset // => Hy.
  by rewrite -(mulg1 y) /f nu_Hmul // rH_Hmul //; apply: (morph1 (Morphism fM)).
apply/setP=> x; apply/mulsgP/idP=> [[h y Hh fy ->{x}] | Gx].
  rewrite groupMl; last exact: (subsetP sHG).
  case/morphimP: fy => z _ Gz ->{h Hh y}.
  by rewrite /= /f groupMl ?GrH // (subsetP sHG) ?fmodP.
exists (x * (f x)^-1) (f x); last first; first by rewrite mulgKV.
  by apply/morphimP; exists x.
rewrite -groupV invMg invgK -mulgA (conjgC (val _)) mulgA.
by rewrite groupMl -(mem_rcoset, mem_conjg) // (normP _) ?nHG ?fmodP.
Qed.

Theorem Gaschutz_transitive : {in [complements to H in G] &,
  forall K L,  K :&: P = L :&: P -> exists2 x, x \in H & L :=: K :^ x}.
Proof.
move=> K L /=; set Q := K :&: P => /complP[tiHK eqHK] cpHL QeqLP.
have [trHL eqHL] := complP cpHL.
pose nu x := fmod (divgr H L x^-1).
have sKG: {subset K <= G} by apply/subsetP; rewrite -eqHK mulG_subr.
have sLG: {subset L <= G} by apply/subsetP; rewrite -eqHL mulG_subr.
have val_nu x: x \in G -> val (nu x) = divgr H L x^-1.
  by move=> Gx; rewrite fmodK // mem_divgr // eqHL groupV.
have nu_cocycle: {in G &, forall x y, nu (x * y)%g = nu x ^@ y + nu y}%R.
  move=> x y Gx Gy; apply: val_inj; rewrite fmvalA fmvalJ ?nHG //.
  rewrite !val_nu ?groupM // /divgr conjgE !mulgA mulgK.
  by rewrite !(invMg, remgrM cpHL) ?groupV ?mulgA.
have nuL x: x \in L -> nu x = 0%R.
  move=> Lx; apply: val_inj; rewrite val_nu ?sLG //.
  by rewrite /divgr remgr_id ?groupV ?mulgV.
exists (fmval ((\sum_(X in rcosets Q K) nu (repr X)) *+ m)).
  exact: fmodP.
apply/eqP; rewrite eq_sym eqEcard; apply/andP; split; last first.
  by rewrite cardJg -(leq_pmul2l (cardG_gt0 H)) -!TI_cardMg // eqHL eqHK.
apply/subsetP=> _ /imsetP[x Kx ->]; rewrite conjgE mulgA (conjgC _ x).
have Gx: x \in G by rewrite sKG.
rewrite conjVg -mulgA -fmvalJ ?nHG // -fmvalN -fmvalA (_ : _ + _ = nu x)%R.
  by rewrite val_nu // mulKVg groupV mem_remgr // eqHL groupV.
rewrite actZr -!mulNrn -mulrnDl actr_sum.
rewrite addrC (reindex_acts _ (actsRs_rcosets _ K) Kx) -sumrB /= -/Q.
rewrite (eq_bigr (fun _ => nu x)) => [|_ /imsetP[y Ky ->]]; last first.
  rewrite !rcosetE -rcosetM QeqLP.
  case: repr_rcosetP => z /setIP[Lz _]; case: repr_rcosetP => t /setIP[Lt _].
  rewrite !nu_cocycle ?groupM ?(sKG y) // ?sLG //.
  by rewrite (nuL z) ?(nuL t) // !act0r !add0r addrC addKr.
apply: val_inj; rewrite sumr_const !fmvalZ.
rewrite -{2}(expgK coHiPG (fmodP (nu x))); congr (_ ^+ _ ^+ _).
rewrite -[#|_|]divgS ?subsetIl // -(divnMl (cardG_gt0 H)).
rewrite -!TI_cardMg //; last by rewrite setIA setIAC (setIidPl sHP).
by rewrite group_modl // eqHK (setIidPr sPG) divgS.
Qed.

End Gaschutz.

(* This is the TI part of B & G, Proposition 1.6(d).                          *)
(* We go with B & G rather than Aschbacher and will derive 1.6(e) from (d),   *)
(* rather than the converse, because the derivation of 24.6 from 24.3 in      *)
(* Aschbacher requires a separate reduction to p-groups to yield 1.6(d),      *)
(* making it altogether longer than the direct Gaschutz-style proof.          *)
(* This Lemma is used in maximal.v for the proof of Aschbacher 24.7.          *)
Lemma coprime_abel_cent_TI (gT : finGroupType) (A G : {group gT}) :
  A \subset 'N(G) -> coprime #|G| #|A| -> abelian G -> 'C_[~: G, A](A) = 1.
Proof.
move=> nGA coGA abG; pose f x := val (\sum_(a in A) fmod abG x ^@ a)%R.
have fM: {in G &, {morph f : x y / x * y}}.
  move=> x y Gx Gy /=; rewrite -fmvalA -big_split /=; congr (fmval _).
  by apply: eq_bigr => a Aa; rewrite fmodM // actAr.
have nfA x a: a \in A -> f (x ^ a) = f x.
  move=> Aa; rewrite {2}/f (reindex_inj (mulgI a)) /=; congr (fmval _).
  apply: eq_big => [b | b Ab]; first by rewrite groupMl.
  by rewrite -!fmodJ ?groupM ?(subsetP nGA) // conjgM.
have kerR: [~: G, A] \subset 'ker (Morphism fM).
  rewrite gen_subG; apply/subsetP=> xa; case/imset2P=> x a Gx Aa -> {xa}.
  have Gxa: x ^ a \in G by rewrite memJ_norm ?(subsetP nGA).
  rewrite commgEl; apply/kerP; rewrite (groupM, morphM) ?(groupV, morphV) //=.
  by rewrite nfA ?mulVg.
apply/trivgP; apply/subsetP=> x /setIP[Rx cAx]; apply/set1P.
have Gx: x \in G by apply: subsetP Rx; rewrite commg_subl.
rewrite -(expgK coGA Gx) (_ : x ^+ _ = 1) ?expg1n //.
rewrite -(fmodK abG Gx) -fmvalZ -(mker (subsetP kerR x Rx)); congr fmval.
rewrite -GRing.sumr_const; apply: eq_bigr => a Aa.
by rewrite -fmodJ ?(subsetP nGA) // /conjg (centP cAx) // mulKg.
Qed.

Section Transfer.

Variables (gT aT : finGroupType) (G H : {group gT}).
Variable alpha : {morphism H >-> aT}.

Hypotheses (sHG : H \subset G) (abelA : abelian (alpha @* H)).

Local Notation HG := (rcosets (gval H) (gval G)).

Fact transfer_morph_subproof : H \subset alpha @*^-1 (alpha @* H).
Proof. by rewrite -sub_morphim_pre. Qed.

Let fmalpha := restrm transfer_morph_subproof (fmod abelA \o alpha).

Let V (rX : {set gT} -> gT) g :=
  \sum_(Hx in rcosets H G) fmalpha (rX Hx * g * (rX (Hx :* g))^-1).

Definition transfer g := V repr g.

(* This is Aschbacher (37.2). *)
Lemma transferM : {in G &, {morph transfer : x y / (x * y)%g >-> x + y}}.
Proof.
move=> s t Gs Gt /=.
rewrite [transfer t](reindex_acts 'Rs _ Gs) ?actsRs_rcosets //= -big_split /=.
apply: eq_bigr => _ /rcosetsP[x Gx ->]; rewrite !rcosetE -!rcosetM.
rewrite -zmodMgE -morphM -?mem_rcoset; first by rewrite !mulgA mulgKV rcosetM.
  by rewrite rcoset_repr rcosetM mem_rcoset mulgK mem_repr_rcoset.
by rewrite rcoset_repr (rcosetM _ _ t) mem_rcoset mulgK mem_repr_rcoset.
Qed.

Canonical transfer_morphism := Morphism transferM.

(* This is Aschbacher (37.1). *)
Lemma transfer_indep X (rX := transversal_repr 1 X) :
  is_transversal X HG G -> {in G, transfer =1 V rX}.
Proof.
move=> trX g Gg; have mem_rX := repr_mem_pblock trX 1; rewrite -/rX in mem_rX.
apply: (addrI (\sum_(Hx in HG) fmalpha (repr Hx * (rX Hx)^-1))).
rewrite {1}(reindex_acts 'Rs _ Gg) ?actsRs_rcosets // -!big_split /=.
apply: eq_bigr => _ /rcosetsP[x Gx ->]; rewrite !rcosetE -!rcosetM.
case: repr_rcosetP => h1 Hh1; case: repr_rcosetP => h2 Hh2.
have: H :* (x * g) \in rcosets H G by rewrite -rcosetE mem_imset ?groupM.
have: H :* x \in rcosets H G by rewrite -rcosetE mem_imset.
case/mem_rX/rcosetP=> h3 Hh3 -> /mem_rX/rcosetP[h4 Hh4 ->].
rewrite -!(mulgA h1) -!(mulgA h2) -!(mulgA h3) !(mulKVg, invMg).
by rewrite addrC -!zmodMgE -!morphM ?groupM ?groupV // -!mulgA !mulKg.
Qed.

Section FactorTransfer.

Variable g : gT.
Hypothesis Gg : g \in G.

Let sgG : <[g]> \subset G. Proof. by rewrite cycle_subG. Qed.
Let H_g_rcosets x : {set {set gT}} := rcosets (H :* x) <[g]>.
Let n_ x := #|<[g]> : H :* x|.

Lemma mulg_exp_card_rcosets x : x * (g ^+ n_ x) \in H :* x.
Proof.
rewrite /n_ /indexg -orbitRs -pcycle_actperm ?inE //.
rewrite -{2}(iter_pcycle (actperm 'Rs g) (H :* x)) -permX -morphX ?inE //.
by rewrite actpermE //= rcosetE -rcosetM rcoset_refl.
Qed.

Let HGg : {set {set {set gT}}} := orbit 'Rs <[g]> @: HG.

Let partHG : partition HG G := rcosets_partition sHG.
Let actsgHG : [acts <[g]>, on HG | 'Rs].
Proof. exact: subset_trans sgG (actsRs_rcosets H G). Qed.
Let partHGg : partition HGg HG := orbit_partition actsgHG.

Let injHGg : {in HGg &, injective cover}.
Proof. by have [] := partition_partition partHG partHGg. Qed.

Let defHGg : HG :* <[g]> = cover @: HGg.
Proof.
rewrite -imset_comp [_ :* _]imset2_set1r; apply: eq_imset => Hx /=.
by rewrite cover_imset -curry_imset2r.
Qed.

Lemma rcosets_cycle_partition : partition (HG :* <[g]>) G.
Proof. by rewrite defHGg; have [] := partition_partition partHG partHGg. Qed.

Variable X : {set gT}.
Hypothesis trX : is_transversal X (HG :* <[g]>) G.

Let sXG : {subset X <= G}. Proof. exact/subsetP/(transversal_sub trX). Qed.

Lemma rcosets_cycle_transversal : H_g_rcosets @: X = HGg.
Proof.
have sHXgHGg x: x \in X -> H_g_rcosets x \in HGg.
  by move/sXG=> Gx; apply: mem_imset; rewrite -rcosetE mem_imset.
apply/setP=> Hxg; apply/imsetP/idP=> [[x /sHXgHGg HGgHxg -> //] | HGgHxg].
have [_ /rcosetsP[z Gz ->] ->] := imsetP HGgHxg.
pose Hzg := H :* z * <[g]>; pose x := transversal_repr 1 X Hzg.
have HGgHzg: Hzg \in HG :* <[g]>.
  by rewrite mem_mulg ?set11 // -rcosetE mem_imset.
have Hzg_x: x \in Hzg by rewrite (repr_mem_pblock trX).
exists x; first by rewrite (repr_mem_transversal trX).
case/mulsgP: Hzg_x => y u /rcoset_eqP <- /(orbit_act 'Rs) <- -> /=.
by rewrite rcosetE -rcosetM.
Qed.

Local Notation defHgX := rcosets_cycle_transversal.

Let injHg: {in X &, injective H_g_rcosets}.
Proof.
apply/imset_injP; rewrite defHgX (card_transversal trX) defHGg.
by rewrite (card_in_imset injHGg).
Qed.

Lemma sum_index_rcosets_cycle : (\sum_(x in X) n_ x)%N = #|G : H|.
Proof. by rewrite [#|G : H|](card_partition partHGg) -defHgX big_imset. Qed.

Lemma transfer_cycle_expansion :
   transfer g = \sum_(x in X) fmalpha ((g ^+ n_ x) ^ x^-1).
Proof.
pose Y := \bigcup_(x in X) [set x * g ^+ i | i : 'I_(n_ x)].
pose rY := transversal_repr 1 Y.
pose pcyc x := pcycle (actperm 'Rs g) (H :* x).
pose traj x := traject (actperm 'Rs g) (H :* x) #|pcyc x|.
have Hgr_eq x: H_g_rcosets x = pcyc x.
  by rewrite /H_g_rcosets -orbitRs -pcycle_actperm ?inE.
have pcyc_eq x: pcyc x =i traj x by apply: pcycle_traject.
have uniq_traj x: uniq (traj x) by apply: uniq_traject_pcycle.
have n_eq x: n_ x = #|pcyc x| by rewrite -Hgr_eq.
have size_traj x: size (traj x) = n_ x by rewrite n_eq size_traject.
have nth_traj x j: j < n_ x -> nth (H :* x) (traj x) j = H :* (x * g ^+ j).
  move=> lt_j_x; rewrite nth_traject -?n_eq //.
  by rewrite -permX -morphX ?inE // actpermE //= rcosetE rcosetM.
have sYG: Y \subset G.
  apply/bigcupsP=> x Xx; apply/subsetP=> _ /imsetP[i _ ->].
  by rewrite groupM ?groupX // sXG.
have trY: is_transversal Y HG G.
  apply/and3P; split=> //; apply/forall_inP=> Hy.
  have /and3P[/eqP <- _ _] := partHGg; rewrite -defHgX cover_imset.
  case/bigcupP=> x Xx; rewrite Hgr_eq pcyc_eq => /trajectP[i].
  rewrite -n_eq -permX -morphX ?in_setT // actpermE /= rcosetE -rcosetM => lti.
  set y := x * _ => ->{Hy}; pose oi := Ordinal lti.
  have Yy: y \in Y by apply/bigcupP; exists x => //; apply/imsetP; exists oi.
  apply/cards1P; exists y; apply/esym/eqP.
  rewrite eqEsubset sub1set inE Yy rcoset_refl.
  apply/subsetP=> _ /setIP[/bigcupP[x' Xx' /imsetP[j _ ->]] Hy_x'gj].
  have eq_xx': x = x'.
    apply: (pblock_inj trX) => //; have /andP[/and3P[_ tiX _] _] := trX.
    have HGgHyg: H :* y * <[g]> \in HG :* <[g]>.
      by rewrite mem_mulg ?set11 // -rcosetE mem_imset ?(subsetP sYG).
    rewrite !(def_pblock tiX HGgHyg) //.
      by rewrite -[x'](mulgK (g ^+ j)) mem_mulg // groupV mem_cycle.
    by rewrite -[x](mulgK (g ^+ i)) mem_mulg ?rcoset_refl // groupV mem_cycle.
  apply/set1P; rewrite /y eq_xx'; congr (_ * _ ^+ _) => //; apply/eqP.
  rewrite -(@nth_uniq _ (H :* x) (traj x)) ?size_traj // ?eq_xx' //.
  by rewrite !nth_traj ?(rcoset_eqP Hy_x'gj) // -eq_xx'.
have rYE x i : x \in X -> i < n_ x -> rY (H :* x :* g ^+ i) = x * g ^+ i.
  move=> Xx lt_i_x; rewrite -rcosetM; apply: (canLR_in (pblockK trY 1)).
    by apply/bigcupP; exists x => //; apply/imsetP; exists (Ordinal lt_i_x).
  apply/esym/def_pblock; last exact: rcoset_refl; first by case/and3P: partHG.
  by rewrite -rcosetE mem_imset ?groupM ?groupX // sXG.
rewrite (transfer_indep trY Gg) /V -/rY (set_partition_big _ partHGg) /=.
rewrite -defHgX big_imset /=; last first.
  apply/imset_injP; rewrite defHgX (card_transversal trX) defHGg.
  by rewrite (card_in_imset injHGg).
apply eq_bigr=> x Xx; rewrite Hgr_eq (eq_bigl _ _ (pcyc_eq x)) -big_uniq //=.
have n_gt0: 0 < n_ x by rewrite indexg_gt0.
rewrite /traj -n_eq; case def_n: (n_ x) (n_gt0) => // [n] _.
rewrite conjgE invgK -{1}[H :* x]rcoset1 -{1}(expg0 g).
elim: {1 3}n 0%N (addn0 n) => [|m IHm] i def_i /=.
  rewrite big_seq1 {i}[i]def_i rYE // ?def_n //.
  rewrite -(mulgA _ _ g) -rcosetM -expgSr -[(H :* x) :* _]rcosetE.
  rewrite -actpermE morphX ?inE // permX // -{2}def_n n_eq iter_pcycle mulgA.
  by rewrite -[H :* x]rcoset1 (rYE _ 0%N) ?mulg1.
rewrite big_cons rYE //; last by rewrite def_n -def_i ltnS leq_addl.
rewrite permE /= rcosetE -rcosetM -(mulgA _ _ g) -expgSr.
rewrite addSnnS in def_i; rewrite IHm //.
rewrite rYE //; last by rewrite def_n -def_i ltnS leq_addl.
by rewrite mulgV [fmalpha 1]morph1 add0r.
Qed.

End FactorTransfer.

End Transfer.
