(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq path choice fintype.
From mathcomp
Require Import tuple finfun bigop finset binomial fingroup.

(******************************************************************************)
(* This file contains the definition and properties associated to the group   *)
(* of permutations of an arbitrary finite type.                               *)
(*     {perm T} == the type of permutations of a finite type T, i.e.,         *)
(*                 injective (finite) functions from T to T. Permutations     *)
(*                 coerce to CiC functions.                                   *)
(*         'S_n == the set of all permutations of 'I_n, i.e., of {0,.., n-1}  *)
(*  perm_on A u == u is a permutation with support A, i.e., u only displaces  *)
(*                 elements of A (u x != x implies x \in A).                  *)
(*    tperm x y == the transposition of x, y.                                 *)
(*    aperm x s == the image of x under the action of the permutation s.      *)
(*              := s x                                                        *)
(*   pcycle s x == the set of all elements that are in the same cycle of the  *)
(*                 permutation s as x, i.e., {x, s x, (s ^+ 2) x, ...}.       *)
(*    pcycles s == the set of all the cycles of the permutation s.            *)
(*   (s : bool) == s is an odd permutation (the coercion is called odd_perm). *)
(*      dpair u == u is a pair (x, y) of distinct objects (i.e., x != y).     *)
(* lift_perm i j s == the permutation obtained by lifting s : 'S_n.-1 over    *)
(*                 (i |-> j), that maps i to j and lift i k to lift j (s k).  *)
(* Canonical structures are defined allowing permutations to be an eqType,    *)
(* choiceType, countType, finType, subType, finGroupType; permutations with   *)
(* composition form a group, therefore inherit all generic group notations:   *)
(* 1 == identity permutation, * == composition, ^-1 == inverse permutation.   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Section PermDefSection.

Variable T : finType.

Inductive perm_type : predArgType :=
  Perm (pval : {ffun T -> T}) & injectiveb pval.
Definition pval p := let: Perm f _ := p in f.
Definition perm_of of phant T := perm_type.
Identity Coercion type_of_perm : perm_of >-> perm_type.

Notation pT := (perm_of (Phant T)).

Canonical perm_subType := Eval hnf in [subType for pval].
Definition perm_eqMixin := Eval hnf in [eqMixin of perm_type by <:].
Canonical perm_eqType := Eval hnf in EqType perm_type perm_eqMixin.
Definition perm_choiceMixin := [choiceMixin of perm_type by <:].
Canonical perm_choiceType := Eval hnf in ChoiceType perm_type perm_choiceMixin.
Definition perm_countMixin := [countMixin of perm_type by <:].
Canonical perm_countType := Eval hnf in CountType perm_type perm_countMixin.
Canonical perm_subCountType := Eval hnf in [subCountType of perm_type].
Definition perm_finMixin := [finMixin of perm_type by <:].
Canonical perm_finType := Eval hnf in FinType perm_type perm_finMixin.
Canonical perm_subFinType := Eval hnf in [subFinType of perm_type].

Canonical perm_for_subType := Eval hnf in [subType of pT].
Canonical perm_for_eqType := Eval hnf in [eqType of pT].
Canonical perm_for_choiceType := Eval hnf in [choiceType of pT].
Canonical perm_for_countType := Eval hnf in [countType of pT].
Canonical perm_for_subCountType := Eval hnf in [subCountType of pT].
Canonical perm_for_finType := Eval hnf in [finType of pT].
Canonical perm_for_subFinType := Eval hnf in [subFinType of pT].

Lemma perm_proof (f : T -> T) : injective f -> injectiveb (finfun f).
Proof.
by move=> f_inj; apply/injectiveP; apply: eq_inj f_inj _ => x; rewrite ffunE.
Qed.

End PermDefSection.

Notation "{ 'perm' T }" := (perm_of (Phant T))
  (at level 0, format "{ 'perm'  T }") : type_scope.

Arguments pval _ _%g.

Bind Scope group_scope with perm_type.
Bind Scope group_scope with perm_of.

Notation "''S_' n" := {perm 'I_n}
  (at level 8, n at level 2, format "''S_' n").

Local Notation fun_of_perm_def := (fun T (u : perm_type T) => val u : T -> T).
Local Notation perm_def := (fun T f injf => Perm (@perm_proof T f injf)).

Module Type PermDefSig.
Parameter fun_of_perm : forall T, perm_type T -> T -> T.
Parameter perm : forall (T : finType) (f : T -> T), injective f -> {perm T}.
Axiom fun_of_permE : fun_of_perm = fun_of_perm_def.
Axiom permE : perm = perm_def.
End PermDefSig.

Module PermDef : PermDefSig.
Definition fun_of_perm := fun_of_perm_def.
Definition perm := perm_def.
Lemma fun_of_permE : fun_of_perm = fun_of_perm_def. Proof. by []. Qed.
Lemma permE : perm = perm_def. Proof. by []. Qed.
End PermDef.

Notation fun_of_perm := PermDef.fun_of_perm.
Notation "@ 'perm'" := (@PermDef.perm) (at level 10, format "@ 'perm'").
Notation perm := (@PermDef.perm _ _).
Canonical fun_of_perm_unlock := Unlockable PermDef.fun_of_permE.
Canonical perm_unlock := Unlockable PermDef.permE.
Coercion fun_of_perm : perm_type >-> Funclass.

Section Theory.

Variable T : finType.
Implicit Types (x y : T) (s t : {perm T}) (S : {set T}).

Lemma permP s t : s =1 t <-> s = t.
Proof. by split=> [| -> //]; rewrite unlock => eq_sv; apply/val_inj/ffunP. Qed.

Lemma pvalE s : pval s = s :> (T -> T).
Proof. by rewrite [@fun_of_perm]unlock. Qed.

Lemma permE f f_inj : @perm T f f_inj =1 f.
Proof. by move=> x; rewrite -pvalE [@perm]unlock ffunE. Qed.

Lemma perm_inj {s} : injective s.
Proof. by rewrite -!pvalE; apply: (injectiveP _ (valP s)). Qed.
Hint Resolve perm_inj : core.

Lemma perm_onto s : codom s =i predT.
Proof. by apply/subset_cardP; rewrite ?card_codom ?subset_predT. Qed.

Definition perm_one := perm (@inj_id T).

Lemma perm_invK s : cancel (fun x => iinv (perm_onto s x)) s.
Proof. by move=> x /=; rewrite f_iinv. Qed.

Definition perm_inv s := perm (can_inj (perm_invK s)).

Definition perm_mul s t := perm (inj_comp (@perm_inj t) (@perm_inj s)).

Lemma perm_oneP : left_id perm_one perm_mul.
Proof. by move=> s; apply/permP => x; rewrite permE /= permE. Qed.

Lemma perm_invP : left_inverse perm_one perm_inv perm_mul.
Proof. by move=> s; apply/permP=> x; rewrite !permE /= permE f_iinv. Qed.

Lemma perm_mulP : associative perm_mul.
Proof. by move=> s t u; apply/permP=> x; do !rewrite permE /=. Qed.

Definition perm_of_baseFinGroupMixin : FinGroup.mixin_of (perm_type T) :=
  FinGroup.Mixin perm_mulP perm_oneP perm_invP.
Canonical perm_baseFinGroupType :=
  Eval hnf in BaseFinGroupType (perm_type T) perm_of_baseFinGroupMixin.
Canonical perm_finGroupType := @FinGroupType perm_baseFinGroupType perm_invP.

Canonical perm_of_baseFinGroupType :=
  Eval hnf in [baseFinGroupType of {perm T}].
Canonical perm_of_finGroupType := Eval hnf in [finGroupType of {perm T} ].

Lemma perm1 x : (1 : {perm T}) x = x.
Proof. by rewrite permE. Qed.

Lemma permM s t x : (s * t) x = t (s x).
Proof. by rewrite permE. Qed.

Lemma permK s : cancel s s^-1.
Proof. by move=> x; rewrite -permM mulgV perm1. Qed.

Lemma permKV s : cancel s^-1 s.
Proof. by have:= permK s^-1; rewrite invgK. Qed.

Lemma permJ s t x : (s ^ t) (t x) = t (s x).
Proof. by rewrite !permM permK. Qed.

Lemma permX s x n : (s ^+ n) x = iter n s x.
Proof. by elim: n => [|n /= <-]; rewrite ?perm1 // -permM expgSr. Qed.

Lemma im_permV s S : s^-1 @: S = s @^-1: S.
Proof. exact: can2_imset_pre (permKV s) (permK s). Qed.

Lemma preim_permV s S : s^-1 @^-1: S = s @: S.
Proof. by rewrite -im_permV invgK. Qed.

Definition perm_on S : pred {perm T} := fun s => [pred x | s x != x] \subset S.

Lemma perm_closed S s x : perm_on S s -> (s x \in S) = (x \in S).
Proof.
move/subsetP=> s_on_S; have [-> // | nfix_s_x] := eqVneq (s x) x.
by rewrite !s_on_S // inE /= ?(inj_eq perm_inj).
Qed.

Lemma perm_on1 H : perm_on H 1.
Proof. by apply/subsetP=> x; rewrite inE /= perm1 eqxx. Qed.

Lemma perm_onM H s t : perm_on H s -> perm_on H t -> perm_on H (s * t).
Proof.
move/subsetP=> sH /subsetP tH; apply/subsetP => x; rewrite inE /= permM.
by have [-> /tH | /sH] := eqVneq (s x) x.
Qed.

Lemma out_perm S u x : perm_on S u -> x \notin S -> u x = x.
Proof. by move=> uS; apply: contraNeq (subsetP uS x). Qed.

Lemma im_perm_on u S : perm_on S u -> u @: S = S.
Proof.
move=> Su; rewrite -preim_permV; apply/setP=> x.
by rewrite !inE -(perm_closed _ Su) permKV.
Qed.

Lemma tperm_proof x y : involutive [fun z => z with x |-> y, y |-> x].
Proof.
move=> z /=; case: (z =P x) => [-> | ne_zx]; first by rewrite eqxx; case: eqP.
by case: (z =P y) => [->| ne_zy]; [rewrite eqxx | do 2?case: eqP].
Qed.

Definition tperm x y := perm (can_inj (tperm_proof x y)).

Variant tperm_spec x y z : T -> Type :=
  | TpermFirst of z = x          : tperm_spec x y z y
  | TpermSecond of z = y         : tperm_spec x y z x
  | TpermNone of z <> x & z <> y : tperm_spec x y z z.

Lemma tpermP x y z : tperm_spec x y z (tperm x y z).
Proof. by rewrite permE /=; do 2?[case: eqP => /=]; constructor; auto. Qed.

Lemma tpermL x y : tperm x y x = y.
Proof. by case: tpermP. Qed.

Lemma tpermR x y : tperm x y y = x.
Proof. by case: tpermP. Qed.

Lemma tpermD x y z : x != z -> y != z -> tperm x y z = z.
Proof. by case: tpermP => // ->; rewrite eqxx. Qed.

Lemma tpermC x y : tperm x y = tperm y x.
Proof. by apply/permP => z; do 2![case: tpermP => //] => ->. Qed.

Lemma tperm1 x : tperm x x = 1.
Proof. by apply/permP => z; rewrite perm1; case: tpermP. Qed.

Lemma tpermK x y : involutive (tperm x y).
Proof. by move=> z; rewrite !permE tperm_proof. Qed.

Lemma tpermKg x y : involutive (mulg (tperm x y)).
Proof. by move=> s; apply/permP=> z; rewrite !permM tpermK. Qed.

Lemma tpermV x y : (tperm x y)^-1 = tperm x y.
Proof. by set t := tperm x y; rewrite -{2}(mulgK t t) -mulgA tpermKg. Qed.

Lemma tperm2 x y : tperm x y * tperm x y = 1.
Proof. by rewrite -{1}tpermV mulVg. Qed.

Lemma card_perm A : #|perm_on A| = (#|A|)`!.
Proof.
pose ffA := {ffun {x | x \in A} -> T}.
rewrite -ffactnn -{2}(card_sig (mem A)) /= -card_inj_ffuns_on.
pose fT (f : ffA) := [ffun x => oapp f x (insub x)].
pose pfT f := insubd (1 : {perm T}) (fT f).
pose fA s : ffA := [ffun u => s (val u)].
rewrite -!sum1dep_card -sum1_card (reindex_onto fA pfT) => [|f].
  apply: eq_bigl => p; rewrite andbC; apply/idP/and3P=> [onA | []]; first split.
  - apply/eqP; suffices fTAp: fT (fA p) = pval p.
      by apply/permP=> x; rewrite -!pvalE insubdK fTAp //; apply: (valP p).
    apply/ffunP=> x; rewrite ffunE pvalE.
    by case: insubP => [u _ <- | /out_perm->] //=; rewrite ffunE.
  - by apply/forallP=> [[x Ax]]; rewrite ffunE /= perm_closed.
  - by apply/injectiveP=> u v; rewrite !ffunE => /perm_inj; apply: val_inj.
  move/eqP=> <- _ _; apply/subsetP=> x; rewrite !inE -pvalE val_insubd fun_if.
  by rewrite if_arg ffunE; case: insubP; rewrite // pvalE perm1 if_same eqxx.
case/andP=> /forallP-onA /injectiveP-f_inj.
apply/ffunP=> u; rewrite ffunE -pvalE insubdK; first by rewrite ffunE valK.
apply/injectiveP=> {u} x y; rewrite !ffunE.
case: insubP => [u _ <-|]; case: insubP => [v _ <-|] //=; first by move/f_inj->.
  by move=> Ay' def_y; rewrite -def_y [_ \in A]onA in Ay'.
by move=> Ax' def_x; rewrite def_x [_ \in A]onA in Ax'.
Qed.

End Theory.

Prenex Implicits tperm permK permKV tpermK.
Arguments perm_inj {T s} [x1 x2] eq_sx12.

(* Shorthand for using a permutation to reindex a bigop. *)
Notation reindex_perm s := (reindex_inj (@perm_inj _ s)).

Lemma inj_tperm (T T' : finType) (f : T -> T') x y z :
  injective f -> f (tperm x y z) = tperm (f x) (f y) (f z).
Proof. by move=> injf; rewrite !permE /= !(inj_eq injf) !(fun_if f). Qed.

Lemma tpermJ (T : finType) x y (s : {perm T}) :
  (tperm x y) ^ s = tperm (s x) (s y).
Proof.
by apply/permP => z; rewrite -(permKV s z) permJ; apply/inj_tperm/perm_inj.
Qed.

Lemma tuple_perm_eqP {T : eqType} {n} {s : seq T} {t : n.-tuple T} :
  reflect (exists p : 'S_n, s = [tuple tnth t (p i) | i < n]) (perm_eq s t).
Proof.
apply: (iffP idP) => [|[p ->]]; last first.
  rewrite /= (map_comp (tnth t)) -{1}(map_tnth_enum t) perm_map //.
  apply: uniq_perm_eq => [||i]; rewrite ?enum_uniq //.
    by apply/injectiveP; apply: perm_inj.
  by rewrite mem_enum -[i](permKV p) image_f.
case: n => [|n] in t *; last have x0 := tnth t ord0.
  rewrite tuple0 => /perm_eq_small-> //.
  by exists 1; rewrite [mktuple _]tuple0.
case/(perm_eq_iotaP x0); rewrite size_tuple => Is eqIst ->{s}.
have uniqIs: uniq Is by rewrite (perm_eq_uniq eqIst) iota_uniq.
have szIs: size Is == n.+1 by rewrite (perm_eq_size eqIst) !size_tuple.
have pP i : tnth (Tuple szIs) i < n.+1.
  by rewrite -[_ < _](mem_iota 0) -(perm_eq_mem eqIst) mem_tnth.
have inj_p: injective (fun i => Ordinal (pP i)).
  by apply/injectiveP/(@map_uniq _ _ val); rewrite -map_comp map_tnth_enum.
exists (perm inj_p); rewrite -[Is]/(tval (Tuple szIs)); congr (tval _).
by apply: eq_from_tnth => i; rewrite tnth_map tnth_mktuple permE (tnth_nth x0).
Qed.

Section PermutationParity.

Variable T : finType.

Implicit Types (s t u v : {perm T}) (x y z a b : T).

(* Note that pcycle s x is the orbit of x by <[s]> under the action aperm. *)
(* Hence, the pcycle lemmas below are special cases of more general lemmas *)
(* on orbits that will be stated in action.v.                              *)
(*   Defining pcycle directly here avoids a dependency of matrix.v on      *)
(* action.v and hence morphism.v.                                          *)

Definition aperm x s := s x.
Definition pcycle s x := aperm x @: <[s]>.
Definition pcycles s := pcycle s @: T.
Definition odd_perm (s : perm_type T) := odd #|T| (+) odd #|pcycles s|.

Lemma apermE x s : aperm x s = s x. Proof. by []. Qed.

Lemma mem_pcycle s i x : (s ^+ i) x \in pcycle s x.
Proof. by rewrite (mem_imset (aperm x)) ?mem_cycle. Qed.

Lemma pcycle_id s x : x \in pcycle s x.
Proof. by rewrite -{1}[x]perm1 (mem_pcycle s 0). Qed.

Lemma uniq_traject_pcycle s x : uniq (traject s x #|pcycle s x|).
Proof.
case def_n: #|_| => // [n]; rewrite looping_uniq.
apply: contraL (card_size (traject s x n)) => /loopingP t_sx.
rewrite -ltnNge size_traject -def_n ?subset_leq_card //.
by apply/subsetP=> _ /imsetP[_ /cycleP[i ->] ->]; rewrite /aperm permX t_sx.
Qed.

Lemma pcycle_traject s x : pcycle s x =i traject s x #|pcycle s x|.
Proof.
apply: fsym; apply/subset_cardP.
  by rewrite (card_uniqP _) ?size_traject ?uniq_traject_pcycle.
by apply/subsetP=> _ /trajectP[i _ ->]; rewrite -permX mem_pcycle.
Qed.

Lemma iter_pcycle s x : iter #|pcycle s x| s x = x.
Proof.
case def_n: #|_| (uniq_traject_pcycle s x) => [//|n] Ut.
have: looping s x n.+1.
  by rewrite -def_n -[looping _ _ _]pcycle_traject -permX mem_pcycle.
rewrite /looping => /trajectP[[|i] //= lt_i_n /perm_inj eq_i_n_sx].
move: lt_i_n; rewrite ltnS ltn_neqAle andbC => /andP[le_i_n /negP[]].
by rewrite -(nth_uniq x _ _ Ut) ?size_traject ?nth_traject // eq_i_n_sx.
Qed.

Lemma eq_pcycle_mem s x y : (pcycle s x == pcycle s y) = (x \in pcycle s y).
Proof.
apply/eqP/idP=> [<- | /imsetP[si s_si ->]]; first exact: pcycle_id.
apply/setP => z; apply/imsetP/imsetP=> [] [sj s_sj ->].
  by exists (si * sj); rewrite ?groupM /aperm ?permM.
exists (si^-1 * sj); first by rewrite groupM ?groupV.
by rewrite /aperm permM permK.
Qed.

Lemma pcycle_sym s x y : (x \in pcycle s y) = (y \in pcycle s x).
Proof. by rewrite -!eq_pcycle_mem eq_sym. Qed.

Lemma pcycle_perm s i x : pcycle s ((s ^+ i) x) = pcycle s x.
Proof. by apply/eqP; rewrite eq_pcycle_mem mem_pcycle. Qed.

Lemma ncycles_mul_tperm s x y : let t := tperm x y in
  #|pcycles (t * s)| + (x \notin pcycle s y).*2 = #|pcycles s| + (x != y).
Proof.
pose xf a b u := find (pred2 a b) (traject u (u a) #|pcycle u a|).
have xf_size a b u: xf a b u <= #|pcycle u a|.
  by rewrite (leq_trans (find_size _ _)) ?size_traject.
have lt_xf a b u n : n < xf a b u -> ~~ pred2 a b ((u ^+ n.+1) a).
  move=> lt_n; apply: contraFN (before_find (u a) lt_n).
  by rewrite permX iterSr nth_traject // (leq_trans lt_n).
pose t a b u := tperm a b * u.
have tC a b u : t a b u = t b a u by rewrite /t tpermC.
have tK a b: involutive (t a b) by move=> u; apply: tpermKg.
have tXC a b u n: n <= xf a b u -> (t a b u ^+ n.+1) b = (u ^+ n.+1) a.
  elim: n => [|n IHn] lt_n_f; first by rewrite permM tpermR.
  rewrite !(expgSr _ n.+1) !permM {}IHn 1?ltnW //; congr (u _).
  by case/lt_xf/norP: lt_n_f => ne_a ne_b; rewrite tpermD // eq_sym.
have eq_xf a b u: pred2 a b ((u ^+ (xf a b u).+1) a).
  have ua_a: a \in pcycle u (u a) by rewrite pcycle_sym (mem_pcycle _ 1).
  have has_f: has (pred2 a b) (traject u (u a) #|pcycle u (u a)|).
    by apply/hasP; exists a; rewrite /= ?eqxx -?pcycle_traject.
  have:= nth_find (u a) has_f; rewrite has_find size_traject in has_f.
  rewrite -eq_pcycle_mem in ua_a.
  by rewrite nth_traject // -iterSr -permX -(eqP ua_a).
have xfC a b u: xf b a (t a b u) = xf a b u.
  without loss lt_a: a b u / xf b a (t a b u) < xf a b u.
    move=> IHab; set m := xf b a _; set n := xf a b u.
    by case: (ltngtP m n) => // ltx; [apply: IHab | rewrite -[m]IHab tC tK].
  by move/lt_xf: (lt_a); rewrite -(tXC a b) 1?ltnW //= orbC [_ || _]eq_xf.
pose ts := t x y s; rewrite /= -[_ * s]/ts.
pose dp u := #|pcycles u :\ pcycle u y :\ pcycle u x|.
rewrite !(addnC #|_|) (cardsD1 (pcycle ts y)) mem_imset ?inE //.
rewrite (cardsD1 (pcycle ts x)) inE mem_imset ?inE //= -/(dp ts) {}/ts.
rewrite (cardsD1 (pcycle s y)) (cardsD1 (pcycle s x)) !(mem_imset, inE) //.
rewrite -/(dp s) !addnA !eq_pcycle_mem andbT; congr (_ + _); last first.
  wlog suffices: s / dp s <= dp (t x y s).
    by move=> IHs; apply/eqP; rewrite eqn_leq -{2}(tK x y s) !IHs.
  apply/subset_leq_card/subsetP=> {dp} C.
  rewrite !inE andbA andbC !(eq_sym C) => /and3P[/imsetP[z _ ->{C}]].
  rewrite 2!eq_pcycle_mem => sxz syz.
  suffices ts_z: pcycle (t x y s) z = pcycle s z.
    by rewrite -ts_z !eq_pcycle_mem {1 2}ts_z sxz syz mem_imset ?inE.
  suffices exp_id n: ((t x y s) ^+ n) z = (s ^+ n) z.
    apply/setP=> u; apply/idP/idP=> /imsetP[_ /cycleP[i ->] ->].
      by rewrite /aperm exp_id mem_pcycle.
    by rewrite /aperm -exp_id mem_pcycle.
  elim: n => // n IHn; rewrite !expgSr !permM {}IHn tpermD //.
    by apply: contraNneq sxz => ->; apply: mem_pcycle.
  by apply: contraNneq syz => ->; apply: mem_pcycle.
case: eqP {dp} => [<- | ne_xy]; first by rewrite /t tperm1 mul1g pcycle_id.
suff ->: (x \in pcycle (t x y s) y) = (x \notin pcycle s y) by case: (x \in _).
without loss xf_x: s x y ne_xy / (s ^+ (xf x y s).+1) x = x.
  move=> IHs; have ne_yx := nesym ne_xy; have:= eq_xf x y s; set n := xf x y s.
  case/pred2P=> [|snx]; first exact: IHs.
  by rewrite -[x \in _]negbK ![x \in _]pcycle_sym -{}IHs ?xfC ?tXC // tC tK.
rewrite -{1}xf_x -(tXC _ _ _ _ (leqnn _)) mem_pcycle; symmetry.
rewrite -eq_pcycle_mem eq_sym eq_pcycle_mem pcycle_traject.
apply/trajectP=> [[n _ snx]].
have: looping s x (xf x y s).+1 by rewrite /looping -permX xf_x inE eqxx.
move/loopingP/(_ n); rewrite -{n}snx.
case/trajectP=> [[_|i]]; first exact: nesym; rewrite ltnS -permX => lt_i def_y.
by move/lt_xf: lt_i; rewrite def_y /= eqxx orbT.
Qed.

Lemma odd_perm1 : odd_perm 1 = false.
Proof.
rewrite /odd_perm card_imset ?addbb // => x y; move/eqP.
by rewrite eq_pcycle_mem /pcycle cycle1 imset_set1 /aperm perm1; move/set1P.
Qed.

Lemma odd_mul_tperm x y s : odd_perm (tperm x y * s) = (x != y) (+) odd_perm s.
Proof.
rewrite addbC -addbA -[~~ _]oddb -odd_add -ncycles_mul_tperm.
by rewrite odd_add odd_double addbF.
Qed.

Lemma odd_tperm x y : odd_perm (tperm x y) = (x != y).
Proof. by rewrite -[_ y]mulg1 odd_mul_tperm odd_perm1 addbF. Qed.

Definition dpair (eT : eqType) := [pred t | t.1 != t.2 :> eT].
Arguments dpair {eT}.

Lemma prod_tpermP s :
  {ts : seq (T * T) | s = \prod_(t <- ts) tperm t.1 t.2 & all dpair ts}.
Proof.
elim: {s}_.+1 {-2}s (ltnSn #|[pred x | s x != x]|) => // n IHn s.
rewrite ltnS => le_s_n; case: (pickP (fun x => s x != x)) => [x s_x | s_id].
  have [|ts def_s ne_ts] := IHn (tperm x (s^-1 x) * s).
    rewrite (cardD1 x) !inE s_x in le_s_n; apply: leq_ltn_trans le_s_n.
    apply: subset_leq_card; apply/subsetP=> y.
    rewrite !inE permM permE /= -(canF_eq (permK _)).
    have [-> | ne_yx] := altP (y =P x); first by rewrite permKV eqxx.
    by case: (s y =P x) => // -> _; rewrite eq_sym.
  exists ((x, s^-1 x) :: ts); last by rewrite /= -(canF_eq (permK _)) s_x.
  by rewrite big_cons -def_s mulgA tperm2 mul1g.
exists nil; rewrite // big_nil; apply/permP=> x.
by apply/eqP/idPn; rewrite perm1 s_id.
Qed.

Lemma odd_perm_prod ts :
  all dpair ts -> odd_perm (\prod_(t <- ts) tperm t.1 t.2) = odd (size ts).
Proof.
elim: ts => [_|t ts IHts] /=; first by rewrite big_nil odd_perm1.
by case/andP=> dt12 dts; rewrite big_cons odd_mul_tperm dt12 IHts.
Qed.

Lemma odd_permM : {morph odd_perm : s1 s2 / s1 * s2 >-> s1 (+) s2}.
Proof.
move=> s1 s2; case: (prod_tpermP s1) => ts1 ->{s1} dts1.
case: (prod_tpermP s2) => ts2 ->{s2} dts2.
by rewrite -big_cat !odd_perm_prod ?all_cat ?dts1 // size_cat odd_add.
Qed.

Lemma odd_permV s : odd_perm s^-1 = odd_perm s.
Proof. by rewrite -{2}(mulgK s s) !odd_permM -addbA addKb. Qed.

Lemma odd_permJ s1 s2 : odd_perm (s1 ^ s2) = odd_perm s1.
Proof. by rewrite !odd_permM odd_permV addbC addbK. Qed.

End PermutationParity.

Coercion odd_perm : perm_type >-> bool.
Arguments dpair {eT}.
Prenex Implicits pcycle dpair pcycles aperm.

Section LiftPerm.
(* Somewhat more specialised constructs for permutations on ordinals. *)

Variable n : nat.
Implicit Types i j : 'I_n.+1.
Implicit Types s t : 'S_n.

Definition lift_perm_fun i j s k :=
  if unlift i k is Some k' then lift j (s k') else j.

Lemma lift_permK i j s :
  cancel (lift_perm_fun i j s) (lift_perm_fun j i s^-1).
Proof.
rewrite /lift_perm_fun => k.
by case: (unliftP i k) => [j'|] ->; rewrite (liftK, unlift_none) ?permK.
Qed.

Definition lift_perm i j s := perm (can_inj (lift_permK i j s)).

Lemma lift_perm_id i j s : lift_perm i j s i = j.
Proof. by rewrite permE /lift_perm_fun unlift_none. Qed.

Lemma lift_perm_lift i j s k' :
  lift_perm i j s (lift i k') = lift j (s k') :> 'I_n.+1.
Proof. by rewrite permE /lift_perm_fun liftK. Qed.

Lemma lift_permM i j k s t :
  lift_perm i j s * lift_perm j k t = lift_perm i k (s * t).
Proof.
apply/permP=> i1; case: (unliftP i i1) => [i2|] ->{i1}.
  by rewrite !(permM, lift_perm_lift).
by rewrite permM !lift_perm_id.
Qed.

Lemma lift_perm1 i : lift_perm i i 1 = 1.
Proof. by apply: (mulgI (lift_perm i i 1)); rewrite lift_permM !mulg1. Qed.

Lemma lift_permV i j s : (lift_perm i j s)^-1 = lift_perm j i s^-1.
Proof. by apply/eqP; rewrite eq_invg_mul lift_permM mulgV lift_perm1. Qed.

Lemma odd_lift_perm i j s : lift_perm i j s = odd i (+) odd j (+) s :> bool.
Proof.
rewrite -{1}(mul1g s) -(lift_permM _ j) odd_permM.
congr (_ (+) _); last first.
  case: (prod_tpermP s) => ts ->{s} _.
  elim: ts => [|t ts IHts] /=; first by rewrite big_nil lift_perm1 !odd_perm1.
  rewrite big_cons odd_mul_tperm -(lift_permM _ j) odd_permM {}IHts //.
  congr (_ (+) _); transitivity (tperm (lift j t.1) (lift j t.2)); last first.
     by rewrite odd_tperm (inj_eq (pcan_inj (liftK j))).
  congr odd_perm; apply/permP=> k; case: (unliftP j k) => [k'|] ->.
    by rewrite lift_perm_lift inj_tperm //; apply: lift_inj.
  by rewrite lift_perm_id tpermD // eq_sym neq_lift.
suff{i j s} odd_lift0 (k : 'I_n.+1): lift_perm ord0 k 1 = odd k :> bool.
  rewrite -!odd_lift0 -{2}invg1 -lift_permV odd_permV -odd_permM.
  by rewrite lift_permM mulg1.
elim: {k}(k : nat) {1 3}k (erefl (k : nat)) => [|m IHm] k def_k.
  by rewrite (_ : k = ord0) ?lift_perm1 ?odd_perm1 //; apply: val_inj.
have le_mn: m < n.+1 by [rewrite -def_k ltnW]; pose j := Ordinal le_mn.
rewrite -(mulg1 1)%g -(lift_permM _ j) odd_permM {}IHm // addbC.
rewrite (_ : _ 1 = tperm j k); first by rewrite odd_tperm neq_ltn def_k leqnn.
apply/permP=> i; case: (unliftP j i) => [i'|] ->; last first.
  by rewrite lift_perm_id tpermL.
apply: ord_inj; rewrite lift_perm_lift !permE /= eq_sym -if_neg neq_lift.
rewrite fun_if -val_eqE /= def_k /bump ltn_neqAle andbC.
case: leqP => [_ | lt_i'm] /=; last by rewrite -if_neg neq_ltn leqW.
by rewrite add1n eqSS eq_sym; case: eqP.
Qed.

End LiftPerm.

Prenex Implicits lift_perm lift_permK.



