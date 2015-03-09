(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import tuple finfun bigop ssralg poly generic_quotient bigenough.

(* We build the ring of multinomials with an arbitrary (countable) *)
(* number of indeterminates. We show it is a ring when the base field *)
(* is a ring, and a commutative ring when the base field is commutative *)

(* TODO:
  - when the base field is an integral domain, so are multinomials (WIP)
  - replace the countable type of indeterminates by an arbitrary choice type
  - do the theory of symmetric polynomials
*)



Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope quotient_scope.

Import GRing.Theory BigEnough.

Module Multinomial.

Section Multinomial.

Variable X : countType.

Section MultinomialRing.

Variable R : ringType.

(* Definining the free algebra of multinomial terms *)
Inductive multi_term :=
| Coef of R
| Var of X
| Oper of bool & multi_term & multi_term.

Notation Sum := (Oper false).
Notation Prod := (Oper true).

(* Encoding to a tree structure in order to recover equality and choice *)
Fixpoint to_tree m : GenTree.tree (X + R) :=
match m with
| Coef x => GenTree.Node 0 [:: GenTree.Leaf (inr _ x)]
| Var x => GenTree.Node 0 [:: GenTree.Leaf (inl _ x)]
| Oper b m1 m2 => GenTree.Node (b.+1)  [:: to_tree m1; to_tree m2]
end.

Fixpoint from_tree t :=
match t with
| GenTree.Node 0 [:: GenTree.Leaf (inr x)] => Some (Coef x)
| GenTree.Node 0 [:: GenTree.Leaf (inl x)] => Some (Var x)
| GenTree.Node n.+1 [:: t1; t2] => 
  if (from_tree t1, from_tree t2) is (Some m1, Some m2)
  then Some (Oper (n == 1)%N m1 m2) else None
| _ => None
end.

Lemma to_treeK : pcancel to_tree from_tree.
Proof. by elim=> //=; case=> ? -> ? ->. Qed.

Definition multi_term_eqMixin := PcanEqMixin to_treeK.
Canonical multi_term_eqType := EqType multi_term multi_term_eqMixin.
Definition multi_term_choiceMixin := PcanChoiceMixin to_treeK.
Canonical multi_term_choiceType := ChoiceType multi_term multi_term_choiceMixin.

(* counting the variables, in order to know how to interpret multi_term *)
Fixpoint nbvar_term t :=
  match t with
    | Coef _ => 0%N
    | Var x => (pickle x).+1
    | Sum u v => maxn (nbvar_term u) (nbvar_term v)
    | Prod u v => maxn (nbvar_term u) (nbvar_term v)
  end.

(* Iterated polynomials over a ring *)
Fixpoint multi n := if n is n.+1 then [ringType of {poly multi n}] else R.

Fixpoint inject n m (p : multi n) {struct m} : multi (m + n) :=
  if m is m'.+1 return multi (m + n) then (inject m' p)%:P else p.

Lemma inject_inj : forall i m, injective (@inject i m).
Proof. by move=> i; elim=> //= m IHm p q; move/polyC_inj; move/IHm. Qed.

Lemma inject0 : forall i m, @inject i m 0 = 0.
Proof. by move=> i; elim=> //= m ->. Qed.

Lemma inject_eq0 : forall i m p, (@inject i m p == 0) = (p == 0).
Proof. by move=> i m p; rewrite -(inj_eq (@inject_inj i m)) inject0. Qed.

Lemma size_inject : forall i m p, size (@inject i m.+1 p) = (p != 0 : nat).
Proof. by move=> i m p; rewrite size_polyC inject_eq0. Qed.

Definition cast_multi i m n Emn : multi i -> multi n :=
  let: erefl in _ = n' := Emn return _ -> multi n' in inject m.

Definition multi_var n (i : 'I_n) := cast_multi (subnK (valP i)) 'X.

Notation "'X_ i" := (multi_var i).

Lemma inject_is_rmorphism : forall m n, rmorphism (@inject n m).
Proof. 
elim=> // m ihm n /=; have ->: inject m = RMorphism (ihm n) by [].
by rewrite -/(_ \o _); apply: rmorphismP.
Qed.
Canonical inject_rmorphism m n := RMorphism (inject_is_rmorphism m n).
Canonical inject_additive m n := Additive (inject_is_rmorphism m n).

Lemma cast_multi_is_rmorphism i m n Enm : rmorphism (@cast_multi i m n Enm).
Proof. by case: n / Enm; apply: rmorphismP. Qed.
Canonical cast_multi_rmorphism i m n e := 
  RMorphism (@cast_multi_is_rmorphism i m n e).
Canonical cast_multi_additive i m n e := 
  Additive (@cast_multi_is_rmorphism i m n e).

Definition multiC n : R -> multi n := cast_multi (addn0 n).
Lemma multiC_is_rmorphism n : rmorphism (multiC n).
Proof. by rewrite /multiC -[R]/(multi 0); apply: rmorphismP. Qed.
Canonical multiC_rmorphism n := RMorphism (multiC_is_rmorphism n).
Canonical multiC_additive n := Additive (multiC_is_rmorphism n).

Lemma cast_multi_inj n i i' n' (m1 m2 : multi n)
  (p1: (i + n)%N=n') (p2: (i' + n)%N=n') :
  cast_multi p1 m1 == cast_multi p2 m2 = (m1 == m2).
Proof.
have := p2; rewrite -{1}[n']p1; move/eqP; rewrite eqn_add2r.
move=> /eqP /= Eii; move:p2; rewrite Eii=> p2 {Eii}.
have <-: p1 = p2; first exact: nat_irrelevance.
apply/idP/idP; last by move/eqP->.
move => Hm {p2}.
have : inject i m1 = inject i m2; last first.
   by move/eqP; rewrite (inj_eq (@inject_inj _ _)).
move: Hm; move:(p1); rewrite -p1 => p2. 
rewrite (_ : p2 = erefl (i+n)%N); last exact: nat_irrelevance. 
by move/eqP.
Qed.

Lemma Emj_Enk i j k m n :
  forall (Emj : (m + i)%N = j) (Enk : (n + j)%N = k), (n + m + i)%N = k.
Proof. by move<-; rewrite addnA. Qed.

Lemma cast_multi_id n (e : (0 + n)%N = n) m : cast_multi e m = m.
Proof. by rewrite (_ : e = erefl _) //; apply: nat_irrelevance. Qed.

Lemma cast_multiS n i n' (m : multi n)
  (p: (i + n)%N = n') (pS: ((i.+1) + n)%N = n'.+1) :
  (cast_multi pS m) = (cast_multi p m)%:P.
Proof. by case: _ / p  in pS *; rewrite [pS](nat_irrelevance _ (erefl _)). Qed.

Lemma injectnm_cast_multi i m n p : 
  inject (n + m)%N p = 
  ((@cast_multi (m + i)%N n ((n + m) + i)%N (addnA _ _ _)) \o (inject m)) p.
Proof.
elim: n => [|n /= -> /=].
  by rewrite [addnA 0%N m i](nat_irrelevance _ (erefl _)).
by rewrite cast_multiS; congr (cast_multi _ _)%:P; apply: nat_irrelevance.
Qed.

Lemma cast_multi_add i j k m n Emj Enk p :
  @cast_multi j n k Enk (@cast_multi i m j Emj p) =
  @cast_multi i (n + m)%N k (Emj_Enk Emj Enk) p.
Proof.
move: (Emj) (Enk) (Emj_Enk Emj Enk); rewrite -Enk -Emj.
change (addn_rec n (addn_rec m i)) with (n+m+i)%N.
rewrite {-1}[(n+(m+i))%N]addnA=> Emj0 Enk0 Enmi.
have ->: (Emj0 = erefl (m+i)%N); first exact: nat_irrelevance.
have ->: (Enmi = erefl (n+m+i)%N); first exact: nat_irrelevance.
rewrite /= injectnm_cast_multi /=.
by apply/eqP; rewrite cast_multi_inj.
Qed.

(* Interpretation of a multi_term in iterated polynomials,
  for a given number of variables n *)
Fixpoint interp n m : multi n :=
  match m with
    | Coef x => multiC n x
    | Var x => let i := pickle x in
      (if i < n as b return (i < n) = b -> multi n
        then fun iltn => cast_multi (subnK iltn) 'X_(Ordinal (leqnn i.+1))
        else fun _ => 0)   (refl_equal (i < n))
    | Sum p q => interp n p + interp n q
    | Prod p q => interp n p * interp n q
end.

Lemma interp_cast_multi n n' m (nltn' : n <= n') :
  nbvar_term m <= n -> interp n' m = cast_multi (subnK nltn') (interp n m).
Proof.
move=> dmltn; have dmltn' := (leq_trans dmltn nltn').
elim: m nltn' dmltn dmltn'.
+ move=> a /= nltn' dmltn dmltn'. 
  apply/eqP; rewrite /multiC. 
  by rewrite cast_multi_add /= cast_multi_inj.
+  move=> N /= nltn' dmltn dmltn'.
  move: (refl_equal (_ N < n')) (refl_equal (_ N < n)).
  rewrite {2 3}[_ N < n]dmltn {2 3}[_ N < n']dmltn' => Nn' Nn.
  by apply/eqP; rewrite cast_multi_add cast_multi_inj.
move=> [] m1 Hm1 m2 Hm2 nltn' /=;
rewrite !geq_max => /andP [dm1n dm1n'] /andP [dm2n dm2n'];
by rewrite (Hm1 nltn') // (Hm2 nltn') // (rmorphM, rmorphD).
Qed.

(* identification of to multi_terms modulo equality of iterated polynomials *)
Definition equivm m1 m2 := let n := maxn (nbvar_term m1) (nbvar_term m2) in
                             interp n m1 == interp n m2.

(* it works even for a bigger n *)
Lemma interp_gtn n m1 m2 : maxn (nbvar_term m1) (nbvar_term m2) <= n -> 
                           equivm m1 m2 = (interp n m1 == interp n m2).
Proof.
move=> hn; rewrite !(interp_cast_multi hn) ?leq_max ?leqnn ?orbT //.
by rewrite cast_multi_inj.
Qed.

Lemma equivm_refl : reflexive equivm. Proof. by move=> x; rewrite /equivm. Qed.

Lemma equivm_sym : symmetric equivm.
Proof. by move=> x y; rewrite /equivm eq_sym maxnC. Qed.

Lemma equivm_trans : transitive equivm.
Proof.
move=> x y z; pose_big_enough n.
  by rewrite !(@interp_gtn n) => // /eqP-> /eqP->.
by close.
Qed.

(* equivm is an equivalence *)
Canonical equivm_equivRel := EquivRel equivm
  equivm_refl equivm_sym equivm_trans.

(* we quotient by the equivalence *)
Definition multinom := {eq_quot equivm}.
Definition multinom_of of phant X & phant R := multinom.

Local Notation "{ 'multinom' R }" := (multinom_of (Phant X) (Phant R))
   (at level 0, format "{ 'multinom'  R }").
(* We recover a lot of structure *)
Canonical multinom_quotType := [quotType of multinom].
Canonical multinom_eqType := [eqType of multinom].
Canonical multinom_eqQuotType := [eqQuotType equivm of multinom].
Canonical multinom_choiceType := [choiceType of multinom].
Canonical multinom_of_quotType := [quotType of {multinom R}].
Canonical multinom_of_eqType := [eqType of {multinom R}].
Canonical multinom_of_eqQuotType := [eqQuotType equivm of {multinom R}].
Canonical multinom_of_choiceType := [choiceType of {multinom R}].

Lemma eqm_interp n m1 m2 : maxn (nbvar_term m1) (nbvar_term m2) <= n -> 
         (interp n m1 == interp n m2) = (m1 == m2 %[mod {multinom R}]).
Proof. by move=> hn; rewrite eqmodE /= -interp_gtn. Qed.

Definition cstm := lift_embed {multinom R} Coef.
Notation "c %:M" := (cstm c) (at level 2, format "c %:M").
Canonical pi_cstm_morph := PiEmbed cstm.

Definition varm := lift_embed {multinom R} Var.
Notation "n %:X" := (varm n) (at level 2, format "n %:X").
Canonical pi_varm_morph := PiEmbed varm.

(* addition is defined by lifting Sum *)
Definition addm := lift_op2 {multinom R} Sum.
Lemma pi_addm : {morph \pi : x y / Sum x y >-> addm x y}.
Proof.
move=> x y /=; unlock addm; apply/eqmodP => /=.
pose_big_enough n.
  rewrite (@interp_gtn n) //=; apply/eqP; congr (_ + _);
  by apply/eqP; rewrite eqm_interp // reprK.
by close.
Qed.
Canonical pi_addm_morph := PiMorph2 pi_addm.

Definition Opp := Prod (Coef (-1)).
Definition oppm := lift_op1 {multinom R} Opp.
Lemma pi_oppm : {morph \pi : x / Opp x >-> oppm x}.
Proof.
move=> x; unlock oppm; apply/eqmodP => /=.
rewrite /equivm /= !max0n; apply/eqP; congr (_ * _).
by apply/eqP; rewrite eqm_interp ?reprK.
Qed.
Canonical pi_oppm_morph := PiMorph1 pi_oppm.

(* addition is defined by lifting Prod *)
Definition mulm := lift_op2 {multinom R} Prod.
Lemma pi_mulm : {morph \pi : x y / Prod x y >-> mulm x y}.
Proof.
move=> x y; unlock mulm; apply/eqP; set x' := repr _; set y' := repr _.
rewrite -(@eqm_interp (nbvar_term (Sum (Sum x y) (Sum x' y')))) /=.
  apply/eqP; congr (_ * _); apply/eqP;
  by rewrite eqm_interp ?reprK // !(geq_max, leq_max, leqnn, orbT).
by rewrite maxnC.
Qed.
Canonical pi_mulm_morph := PiMorph2 pi_mulm.

(* Ring properties are obtained from iterated polynomials *)
Lemma addmA : associative addm.
Proof.
elim/quotW=> x; elim/quotW=> y; elim/quotW=> z; apply/eqP.
by rewrite !piE /equivm /= addrA.
Qed.

Lemma addmC : commutative addm.
Proof.
by elim/quotW=> x; elim/quotW=> y; apply/eqP; rewrite !piE /equivm /= addrC.
Qed.

Lemma add0m : left_id 0%:M addm.
Proof. by elim/quotW=> x; apply/eqP; rewrite piE /equivm /= rmorph0 add0r. Qed.

Lemma addmN : left_inverse 0%:M oppm addm.
Proof.
elim/quotW=> x; apply/eqP; rewrite piE /equivm /=.
by rewrite !rmorph0 rmorphN rmorph1 mulN1r addNr.
Qed.

Definition multinom_zmodMixin :=  ZmodMixin addmA addmC add0m addmN.
Canonical multinom_zmodType := ZmodType multinom multinom_zmodMixin.
Canonical multinom_of_zmodType := ZmodType {multinom R} multinom_zmodMixin.

Lemma mulmA : associative mulm.
Proof.
elim/quotW=> x; elim/quotW=> y; elim/quotW=> z; apply/eqP.
by rewrite piE /equivm /= mulrA.
Qed.

Lemma mul1m : left_id 1%:M mulm.
Proof. by elim/quotW=> x; apply/eqP; rewrite piE /equivm /= rmorph1 mul1r. Qed.

Lemma mulm1 : right_id 1%:M mulm.
Proof.
elim/quotW=> x; rewrite !piE /=; apply/eqmodP; rewrite /= /equivm /=.
by rewrite rmorph1 mulr1.
Qed.

Lemma mulm_addl : left_distributive mulm addm.
Proof.
elim/quotW=> x; elim/quotW=> y; elim/quotW=> z; apply/eqP.
by rewrite !piE /equivm /= mulrDl.
Qed.

Lemma mulm_addr : right_distributive mulm addm.
Proof.
elim/quotW=> x; elim/quotW=> y; elim/quotW=> z; apply/eqP.
by rewrite !piE /equivm /= mulrDr.
Qed.

Lemma nonzero1m : 1%:M != 0%:M.
Proof. by rewrite piE /equivm /= rmorph1 rmorph0 oner_neq0. Qed.

Definition multinom_ringMixin := RingMixin mulmA mul1m mulm1 mulm_addl mulm_addr nonzero1m.
Canonical multinom_ringType := RingType multinom multinom_ringMixin.
Canonical multinom_of_ringType := RingType {multinom R} multinom_ringMixin.

End MultinomialRing.

Notation "{ 'multinom' R }" := (@multinom_of _ (Phant X) (Phant R))
   (at level 0, format "{ 'multinom'  R }").

Notation "c %:M" := (cstm c) (at level 2, format "c %:M").
Notation "n %:X" := (varm n) (at level 2, format "n %:X").

Section MultinomialComRing.

Variable R : comRingType.

Lemma mul_multiC n : commutative (@GRing.mul (multi R n)).
Proof.
suff [M IH_CR] : {CR : comRingType | [ringType of CR] = multi R n}.
  by case: _ / IH_CR => x y; rewrite mulrC.
elim: n => [|n [CR IH_CR]] //=; first by exists R.
by exists [comRingType of {poly CR}]; rewrite -IH_CR.
Qed.

Lemma mulmC : commutative (@mulm R).
Proof.
elim/quotW=> x; elim/quotW=> y; apply/eqP.
by rewrite piE /equivm /= mul_multiC.
Qed.

(* if R is commutative, so is {multinom R} *)
Canonical multinom_comRing := Eval hnf in ComRingType (@multinom R) mulmC.
Canonical multinom_of_comRing := Eval hnf in ComRingType {multinom R} mulmC.

End MultinomialComRing.

Section MultinomialIdomain.

Variable R : idomainType.

(* if R is an integral domain, {multinom R} should also be one,
  but the developpment is unfinished *)
Lemma multi_unitClass n : GRing.UnitRing.class_of (multi R n).
Proof.
suff [D IH_D] : {D : idomainType | [ringType of D] = multi R n}.
  by case: _ / IH_D; case: D => [sort [[[rc /= _ um _ _]]]]; exists rc.
elim: n => [|n [D IH_D]] //=; first by exists R.
by exists [idomainType of {poly D}]; case: _ / IH_D.
Qed.

Canonical multi_unitRing n := GRing.UnitRing.Pack
                                (multi_unitClass n) (multi R n).

(* Definition Unit (m : multi_term R) := *)
(*   let n := nbvar_term m in interp n m \in GRing.unit. *)
(* Definition unitm := lift_fun1 {multinom R} Unit. *)
(* Lemma pi_unitm : {mono \pi : x / Unit x >-> unitm x}. *)
(* Proof. *)
(* move=> x; unlock unitm; rewrite /Unit /=. *)
(* Admitted. *)
(* Canonical pi_unitm_morph := PiMono1 pi_unitm. *)

Lemma multi_idomain n : GRing.IntegralDomain.axiom (multi R n).
Proof.
suff [D IH_D] : {D : idomainType | [ringType of D] = multi R n}.
  by case: _ / IH_D => x y /eqP; rewrite mulf_eq0.
elim: n => [|n [D IH_D]] //=; first by exists R.
by exists [idomainType of {poly D}]; rewrite -IH_D.
Qed.

Lemma multinom_idomain : GRing.IntegralDomain.axiom [ringType of multinom R].
Proof.
elim/quotW=> x; elim/quotW=> y /eqP; rewrite -[_ * _]pi_mulm !piE.
pose_big_enough n.
  by rewrite !(@interp_gtn _ n) //= !rmorph0 => /eqP /multi_idomain.
by close.
Qed.

(* Work in progress *)

End MultinomialIdomain.

End Multinomial.
End Multinomial.




