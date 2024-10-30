From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div choice fintype.
From mathcomp
Require Import tuple bigop ssralg finset fingroup zmodp poly order ssrnum.
From mathcomp
Require Import matrix mxalgebra vector.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory Order.Theory Num.Theory.

Reserved Notation "'[ u , v ]"
  (at level 2, format "'[hv' ''[' u , '/ '  v ] ']'").
Reserved Notation "'[ u , v ]_ M"
         (at level 2, format "'[hv' ''[' u , '/ '  v ]_ M ']'").
Reserved Notation "'[ u ]_ M" (at level 2, format "''[' u ]_ M").
Reserved Notation "'[ u ]" (at level 2, format "''[' u ]").
Reserved Notation "u '``_' i"
    (at level 3, i at level 2, left associativity, format "u '``_' i").
Reserved Notation "A ^!"    (at level 2, format "A ^!").
Reserved Notation "A _|_ B" (at level 69, format "A  _|_  B").

Module InvolutiveMorphism.

Section ClassDef.

Variables (R : ringType).

Record class_of (f : R -> R) : Type :=
  Class {base : rmorphism f; mixin : involutive f}.
Local Coercion base : class_of >-> rmorphism.

Structure map (phR : phant R) := Pack {apply; _ : class_of apply}.
Local Coercion apply : map >-> Funclass.

Variables (phR : phant R) (f g : R -> R) (cF : map phR).

Definition class := let: Pack _ c as cF' := cF return class_of cF' in c.

Definition clone fM of phant_id g (apply cF) & phant_id fM class :=
  @Pack phR f fM.

Definition pack (fM : involutive f) :=
  fun (phRR : phant (R -> R)) (bF : GRing.RMorphism.map phRR) fA
      of phant_id (GRing.RMorphism.class bF) fA =>
  Pack phR (Class fA fM).

Canonical additive := GRing.Additive.Pack (Phant (R -> R)) class.
Canonical rmorphism := GRing.RMorphism.Pack (Phant (R -> R)) class.

End ClassDef.

Module Exports.
Notation involutive_rmorphism f := (class_of f).
Coercion base : involutive_rmorphism >-> GRing.RMorphism.class_of.
Coercion mixin : involutive_rmorphism >-> involutive.
Coercion apply : map >-> Funclass.
Notation InvolutiveRMorphism fM := (pack (Phant _) fM id).
Notation "{ 'involutive_rmorphism' fRS }" := (map (Phant fRS))
  (at level 0, format "{ 'involutive_rmorphism'  fRS }") : ring_scope.
Notation "[ 'involutive_rmorphism' 'of' f 'as' g ]" := (@clone _ _ f g _ _ idfun id)
  (at level 0, format "[ 'involutive_rmorphism'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'involutive_rmorphism' 'of' f ]" := (@clone _ _ f f _ _ id id)
  (at level 0, format "[ 'involutive_rmorphism'  'of'  f ]") : form_scope.
Coercion additive : map >-> GRing.Additive.map.
Canonical additive.
Coercion rmorphism : map >-> GRing.RMorphism.map.
Canonical rmorphism.
End Exports.

End InvolutiveMorphism.
Include InvolutiveMorphism.Exports.

Section InvolutiveTheory.

Variable (R : ringType).

Lemma idfunK : involutive (@idfun R). Proof. by []. Qed.
Canonical idfun_involutive := InvolutiveRMorphism idfunK.

Variable (f : {involutive_rmorphism R}).
Lemma rmorphK : involutive f. Proof. by case: f => [? []]. Qed.

End InvolutiveTheory.

(** Contents *)

Structure revop X Y Z (f : Y -> X -> Z) := RevOp {
  fun_of_revop :> X -> Y -> Z;
  _ : forall x, f x =1 fun_of_revop^~ x
}.
Notation "[ 'revop' revop 'of' op ]" :=
  (@RevOp _ _ _ revop op (fun _ _ => erefl))
  (at level 0, format "[ 'revop'  revop  'of'  op ]") : form_scope.

(* Fact applyr_key : unit. Proof. exact. Qed. *)
Definition applyr_head U U' V t (f : U -> U' -> V) u v := let: tt := t in f v u.
Notation applyr := (@applyr_head _ _ _ tt).

Module Bilinear.

Section ClassDef.

Variables (R : ringType) (U U' : lmodType R) (V : zmodType) (s s' : R -> V -> V).
Implicit Type phUU'V : phant (U -> U' -> V).

Local Coercion GRing.Scale.op : GRing.Scale.law >-> Funclass.
Definition axiom (f : U -> U' -> V) (s_law : GRing.Scale.law s) (eqs : s = s_law)
                                    (s'_law : GRing.Scale.law s') (eqs' : s' = s'_law) :=
  ((forall u', GRing.Linear.axiom (f^~ u') eqs)
  * (forall u, GRing.Linear.axiom (f u) eqs'))%type.

Record class_of (f : U -> U' -> V) : Prop := Class {
  basel : forall u', GRing.Linear.class_of s (f^~ u');
  baser : forall u, GRing.Linear.class_of s' (f u)
}.

Lemma class_of_axiom f s_law s'_law Ds Ds' :
   @axiom f s_law Ds s'_law Ds' -> class_of f.
Proof.
by pose coa := GRing.Linear.class_of_axiom; move=> [/(_ _) /coa ? /(_ _) /coa].
Qed.

Structure map phUU'V := Pack {apply; _ : class_of apply}.
Local Coercion apply : map >-> Funclass.

Definition class (phUU'V : _)  (cF : map phUU'V) :=
   let: Pack _ c as cF' := cF return class_of cF' in c.

Canonical additiver phU'V phUU'V (u : U) cF := GRing.Additive.Pack phU'V
  (baser (@class phUU'V cF) u).
Canonical linearr phU'V  phUU'V (u : U) cF := GRing.Linear.Pack phU'V
  (baser (@class phUU'V cF) u).

Canonical additivel phUV phUU'V (u' : U') (cF : map _) :=
  @GRing.Additive.Pack _ _ phUV (applyr cF u') (basel (@class phUU'V cF) u').
Canonical linearl phUV phUU'V  (u' : U') (cF : map _) :=
  @GRing.Linear.Pack _ _ _ _ phUV (applyr cF u') (basel (@class phUU'V cF) u').

Definition pack (phUV : phant (U -> V)) (phU'V : phant (U' -> V))
           (revf : U' -> U -> V) (rf : revop revf) f (g : U -> U' -> V) of (g = fun_of_revop rf) :=
  fun (bFl : U' -> GRing.Linear.map s phUV) flc of (forall u', revf u' = bFl u') &
      (forall u', phant_id (GRing.Linear.class (bFl u')) (flc u')) =>
  fun (bFr : U -> GRing.Linear.map s' phU'V) frc of (forall u, g u = bFr u) &
      (forall u, phant_id (GRing.Linear.class (bFr u)) (frc u)) =>
  @Pack (Phant _) f (Class flc frc).


(* Support for right-to-left rewriting with the generic linearZ rule. *)
Notation mapUUV := (map (Phant (U -> U' -> V))).
Definition map_class := mapUUV.
Definition map_at_left (a : R) := mapUUV.
Definition map_at_right (b : R) := mapUUV.
Definition map_at_both (a b : R) := mapUUV.
Structure map_for_left a s_a := MapForLeft {map_for_left_map : mapUUV; _ : s a = s_a }.
Structure map_for_right b s'_b := MapForRight {map_for_right_map : mapUUV; _ : s' b = s'_b }.
Structure map_for_both a b s_a s'_b :=
  MapForBoth {map_for_both_map : mapUUV; _ : s a = s_a ; _ : s' b = s'_b }.
Definition unify_map_at_left a (f : map_at_left a) := MapForLeft f (erefl (s a)).
Definition unify_map_at_right b (f : map_at_right b) := MapForRight f (erefl (s' b)).
Definition unify_map_at_both a b (f : map_at_both a b) :=
   MapForBoth f (erefl (s a)) (erefl (s' b)).
Structure wrapped := Wrap {unwrap : mapUUV}.
Definition wrap (f : map_class) := Wrap f.

End ClassDef.

Module Exports.
Notation bilinear_for s s' f := (axiom f (erefl s) (erefl s')).
Notation bilinear f := (bilinear_for *:%R *:%R f).
Notation biscalar f := (bilinear_for *%R *%R f).
Notation bilmorphism_for s s' f := (class_of s s' f).
Notation bilmorphism f := (bilmorphism_for *:%R *:%R f).
Coercion baser : bilmorphism_for >-> Funclass.
Coercion apply : map >-> Funclass.
Notation "{ 'bilinear' fUV | s & s' }" := (map s s' (Phant fUV))
  (at level 0, format "{ 'bilinear'  fUV  |  s  &  s' }") : ring_scope.
Notation "{ 'bilinear' fUV | s }" := (map s.1 s.2 (Phant fUV))
  (at level 0, format "{ 'bilinear'  fUV  |  s }") : ring_scope.
Notation "{ 'bilinear' fUV }" := {bilinear fUV | *:%R & *:%R}
  (at level 0, format "{ 'bilinear'  fUV }") : ring_scope.
Notation "{ 'biscalar' U }" := {bilinear U -> U -> _ | *%R & *%R}
  (at level 0, format "{ 'biscalar'  U }") : ring_scope.
Notation "[ 'bilinear' 'of' f 'as' g ]" :=
  (@pack  _ _ _ _ _ _ _ _ _ _ f g erefl _ _
         (fun=> erefl) (fun=> idfun) _ _ (fun=> erefl) (fun=> idfun)).
Notation "[ 'bilinear' 'of' f ]" :=  [bilinear of f as f]
  (at level 0, format "[ 'bilinear'  'of'  f ]") : form_scope.
Canonical additiver.
Canonical linearr.
Canonical additivel.
Canonical linearl.
Notation biapplyr := (@applyr_head _ _ _ _ tt).

Coercion map_for_left_map : map_for_left >-> map.
Coercion map_for_right_map : map_for_right >-> map.
Coercion map_for_both_map : map_for_both >-> map.
Coercion unify_map_at_left : map_at_left >-> map_for_left.
Coercion unify_map_at_right : map_at_right >-> map_for_right.
Coercion unify_map_at_both : map_at_both >-> map_for_both.
Canonical unify_map_at_left.
Canonical unify_map_at_right.
Canonical unify_map_at_both.
Coercion unwrap : wrapped >-> map.
Coercion wrap : map_class >-> wrapped.
Canonical wrap.
End Exports.

End Bilinear.
Include Bilinear.Exports.

Section BilinearTheory.

Variable R : ringType.

Section GenericProperties.

Variables (U U' : lmodType R) (V : zmodType) (s : R -> V -> V) (s' : R -> V -> V).
Variable f : {bilinear U -> U' -> V | s & s'}.

Lemma linear0r z : f z 0 = 0. Proof. by rewrite linear0. Qed.
Lemma linearNr z : {morph f z : x / - x}. Proof. exact: raddfN. Qed.
Lemma linearDr z : {morph f z : x y / x + y}. Proof. exact: raddfD. Qed.
Lemma linearBr z : {morph f z : x y / x - y}. Proof. exact: raddfB. Qed.
Lemma linearMnr z n : {morph f z : x / x *+ n}. Proof. exact: raddfMn. Qed.
Lemma linearMNnr z n : {morph f z : x / x *- n}. Proof. exact: raddfMNn. Qed.
Lemma linear_sumr z I r (P : pred I) E :
  f z (\sum_(i <- r | P i) E i) = \sum_(i <- r | P i) f z (E i).
Proof. exact: raddf_sum. Qed.

Lemma linearZr_LR z : scalable_for s' (f z). Proof. exact: linearZ_LR. Qed.
Lemma linearPr z a : {morph f z : u v / a *: u + v >-> s' a u + v}.
Proof. exact: linearP. Qed.

Lemma applyrE x : applyr f x =1 f^~ x. Proof. by []. Qed.

Lemma linear0l z : f 0 z = 0. Proof. by rewrite -applyrE raddf0. Qed.
Lemma linearNl z : {morph f^~ z : x / - x}.
Proof. by move=> ?; rewrite -applyrE raddfN. Qed.
Lemma linearDl z : {morph f^~ z : x y / x + y}.
Proof. by move=> ??; rewrite -applyrE raddfD. Qed.
Lemma linearBl z : {morph f^~ z : x y / x - y}.
Proof. by move=> ??; rewrite -applyrE raddfB. Qed.
Lemma linearMnl z n : {morph f^~ z : x / x *+ n}.
Proof. by move=> ?; rewrite -applyrE raddfMn. Qed.
Lemma linearMNnl z n : {morph f^~ z : x / x *- n}.
Proof. by move=> ?; rewrite -applyrE raddfMNn. Qed.
Lemma linear_suml z I r (P : pred I) E :
  f (\sum_(i <- r | P i) E i) z = \sum_(i <- r | P i) f (E i) z.
Proof. by rewrite -applyrE raddf_sum. Qed.

Lemma linearZl_LR z : scalable_for s (f^~ z).
Proof. by move=> ??; rewrite -applyrE linearZ_LR. Qed.
Lemma linearPl z a : {morph f^~ z : u v / a *: u + v >-> s a u + v}.
Proof. by move=> ??; rewrite -applyrE linearP. Qed.

End GenericProperties.

Section BidirectionalLinearZ.

Variables (U U' : lmodType R) (V : zmodType) (s s' : R -> V -> V).
Variables (S : ringType) (h h' : S -> V -> V).
Variables (h_law : GRing.Scale.law h) (h'_law : GRing.Scale.law h').

Lemma linearZl z c a (h_c := GRing.Scale.op h_law c)
    (f : Bilinear.map_for_left U U' s s' a h_c) u :
  f (a *: u) z = h_c (Bilinear.wrap f u z).
Proof. by rewrite linearZl_LR; case: f => f /= ->. Qed.

Lemma linearZr z c' b (h'_c' := GRing.Scale.op h'_law c')
    (f : Bilinear.map_for_right U U' s s' b h'_c') u :
  f z (b *: u) = h'_c' (Bilinear.wrap f z u).
Proof. by rewrite linearZ_LR; case: f => f /= ->. Qed.

Lemma linearZlr c c' a b (h_c := GRing.Scale.op h_law c) (h'_c' := GRing.Scale.op h'_law c')
    (f : Bilinear.map_for_both U U' s s' a b h_c h'_c') u v :
  f (a *: u) (b *: v) = h_c (h'_c' (Bilinear.wrap f u v)).
Proof. by rewrite linearZl_LR linearZ_LR; case: f => f /= -> ->. Qed.

Lemma linearZrl c c' a b (h_c := GRing.Scale.op h_law c) (h'_c' := GRing.Scale.op h'_law c')
    (f : Bilinear.map_for_both U U' s s' a b h_c h'_c') u v :
  f (a *: u) (b *: v) = h'_c' (h_c (Bilinear.wrap f u v)).
Proof. by rewrite linearZ_LR/= linearZl_LR; case: f => f /= -> ->. Qed.

End BidirectionalLinearZ.

End BilinearTheory.

Canonical rev_mulmx (R : ringType) m n p := [revop mulmxr of @mulmx R m n p].
Canonical mulmx_bilinear (R : comRingType) m n p := [bilinear of @mulmx R m n p].

Module Hermitian.

Section ClassDef.

Variables (R : ringType) (U : lmodType R) (eps : bool) (theta : R -> R).
Implicit Types phU : phant U.

Local Coercion GRing.Scale.op : GRing.Scale.law >-> Funclass.
Definition axiom (f : U -> U -> R) :=
  forall x y : U, f x y = (-1) ^+ eps * theta (f y x).

Record class_of (f : U -> U -> R) : Prop := Class {
  base : Bilinear.class_of ( *%R) (theta \; *%R) f;
  mixin : axiom f
}.

Structure map phU := Pack {apply; _ : class_of apply}.
Local Coercion apply : map >-> Funclass.

Variables (phU : phant U) (cF : map phU).

Definition class := let: Pack _ c as cF' := cF return class_of cF' in c.

Canonical additiver (u : U) := Additive (base class u).
Canonical linearr (u : U) := Linear (base class u).
Canonical additivel (u' : U) := @GRing.Additive.Pack _ _ (Phant (U -> R))
  (applyr cF u') (Bilinear.basel (base class) u').
Canonical linearl (u' : U) := @GRing.Linear.Pack _ _ _ _ (Phant (U -> R))
  (applyr cF u') (Bilinear.basel (base class) u').
Canonical bilinear := @Bilinear.Pack _ _ _ _ _ _ (Phant (U -> U -> R)) cF (base class).

Definition clone (f g : U -> U -> R) :=
 fun fM of phant_id g (apply cF) & phant_id fM class => @Pack phU f fM.

Definition pack f fM :=
  fun b s s' (phUUR : phant (U -> U -> R)) (bF : Bilinear.map s s' phUUR)
      of phant_id (Bilinear.class bF) b =>
  @Pack phU f (Class b fM).

End ClassDef.

Module Exports.
Notation "{ 'hermitian' U 'for' eps & theta }" := (map eps theta (Phant U))
  (at level 0, format "{ 'hermitian'  U  'for'  eps  &  theta }") : ring_scope.
Coercion base : class_of >-> bilmorphism_for.
Coercion apply : map >-> Funclass.
Notation "[ 'hermitian' 'of' f 'as' g ]" := (@clone _ _ _ _ _ _ f g _ idfun idfun)
  (at level 0, format "[ 'hermitian'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'hermitian' 'of' f ]" := (@clone _ _ _ _ _ _ f f _ idfun idfun)
  (at level 0, format "[ 'hermitian'  'of'  f ]") : form_scope.
Notation hermitian_for := Hermitian.axiom.
Notation Hermitian fM := (pack (Phant _) fM idfun).
Canonical additiver.
Canonical linearr.
Canonical additivel.
Canonical linearl.
Canonical bilinear.
Notation hermapplyr := (@applyr_head _ _ _ _ tt).
End Exports.

End Hermitian.
Include Hermitian.Exports.

Module Dot.

Section ClassDef.

Variables (R : numDomainType) (U : lmodType R) (theta : R -> R).
Implicit Types phU : phant U.

Local Coercion GRing.Scale.op : GRing.Scale.law >-> Funclass.
Definition axiom (f : U -> U -> R) := forall u, u != 0 -> 0 < f u u.

Record class_of (f : U -> U -> R) : Prop := Class {
  base : Hermitian.class_of false theta f;
  mixin : axiom f
}.

Structure map phU := Pack {apply; _ : class_of apply}.
Local Coercion apply : map >-> Funclass.

Variables (phU : phant U) (cF : map phU).

Definition class := let: Pack _ c as cF' := cF return class_of cF' in c.

Canonical additiver (u : U) := Additive (base class u).
Canonical linearr (u : U) := Linear (base class u).
Canonical additivel (u' : U) := @GRing.Additive.Pack _ _ (Phant (U -> R))
  (applyr cF u') (Bilinear.basel (base class) u').
Canonical linearl (u' : U) := @GRing.Linear.Pack _ _ _ _ (Phant (U -> R))
  (applyr cF u') (Bilinear.basel (base class) u').
Canonical bilinear := @Bilinear.Pack _ _ _ _ _ _ (Phant (U -> U -> R)) cF (base class).
Canonical hermitian := @Hermitian.Pack _ _ _ _ (Phant U) cF (base class).

Definition clone (f g : U -> U -> R) :=
 fun fM of phant_id g (apply cF) & phant_id fM class => @Pack phU f fM.


Definition pack f fM :=
  fun b s s' (bF : Hermitian.map s s' phU) of phant_id (Hermitian.class bF) b =>
  @Pack phU f (Class b fM).

End ClassDef.


Module Exports.
Notation "{ 'dot' U 'for' theta }" := (map theta (Phant U))
  (at level 0, format "{ 'dot'  U  'for'  theta }") : ring_scope.
Coercion base : class_of >-> Hermitian.class_of.
Coercion apply : map >-> Funclass.
Notation "[ 'dot' 'of' f 'as' g ]" := (@clone _ _ _ _ _ f g _ idfun idfun)
  (at level 0, format "[ 'dot'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'dot' 'of' f ]" := (@clone _ _ _ _ _ f f _ idfun idfun)
  (at level 0, format "[ 'dot'  'of'  f ]") : form_scope.
Notation Dot fM := (pack fM idfun).
Notation is_dot := Dot.axiom.
Canonical additiver.
Canonical linearr.
Canonical additivel.
Canonical linearl.
Canonical bilinear.
Canonical hermitian.
Coercion hermitian: map >-> Hermitian.map.
Coercion bilinear: map >-> Bilinear.map.
End Exports.

End Dot.
Include Dot.Exports.

Definition symmetric_map (R : ringType) (U : lmodType R) (phU : phant U) :=
  Eval simpl in Hermitian.map false idfun phU.
Notation "{ 'symmetric' U }" := (symmetric_map (Phant U))
  (at level 0, format "{ 'symmetric'  U }") : ring_scope.

Definition skew_symmetric_map (R : ringType) (U : lmodType R) (phU : phant U) :=
  Eval simpl in Hermitian.map true idfun phU.
Notation "{ 'skew_symmetric' U }" := (skew_symmetric_map (Phant U))
  (at level 0, format "{ 'skew_symmetric'  U }") : ring_scope.

Definition hermitian_sym_map (R : ringType) (U : lmodType R)
  theta (phU : phant U) :=
  Eval simpl in Hermitian.map false theta phU.
Notation "{ 'hermitian_sym' U 'for' theta }" := (hermitian_sym_map theta (Phant U))
  (at level 0, format "{ 'hermitian_sym'  U  'for'  theta }") : ring_scope.

Definition is_skew (R : ringType) (eps : bool) (theta : R -> R)
  (U : lmodType R) (form : {hermitian U for eps & theta}) :=
  (eps = true) /\ (theta =1 id).
Definition is_sym (R : ringType) (eps : bool) (theta : R -> R)
  (U : lmodType R) (form : {hermitian U for eps & theta}) :=
  (eps = false) /\ (theta =1 id).
Definition is_hermsym  (R : ringType) (eps : bool) (theta : R -> R)
  (U : lmodType R) (form : {hermitian U for eps & theta}) :=
  (eps = false).

Section HermitianModuleTheory.

Variables (R : ringType) (eps : bool) (theta : {rmorphism R -> R}).
Variable (U : lmodType R) (form : {hermitian U for eps & theta}).

Local Notation "''[' u , v ]" := (form u%R v%R) : ring_scope.
Local Notation "''[' u ]" := '[u, u]%R : ring_scope.

Lemma hermC u v : '[u, v] = (-1) ^+ eps * theta '[v, u].
Proof. by case: form => [? []]. Qed.

Lemma hnormN u : '[- u] = '[u].
Proof. by rewrite linearNl raddfN opprK. Qed.

Lemma hnorm_sign n u : '[(-1) ^+ n *: u] = '[u].
Proof. by rewrite -signr_odd scaler_sign; case: (odd n); rewrite ?hnormN. Qed.

Lemma hnormD u v :
  let d := '[u, v] in '[u + v] = '[u] + '[v] + (d + (-1) ^+ eps * theta d).
Proof. by rewrite /= addrAC -hermC linearDl /= !linearD !addrA. Qed.

Lemma hnormB u v :
  let d := '[u, v] in '[u - v] = '[u] + '[v] - (d + (-1) ^+ eps * theta d).
Proof. by rewrite /= hnormD hnormN linearN rmorphN /= mulrN -opprD. Qed.

Lemma hnormDd u v : '[u, v] = 0 -> '[u + v] = '[u] + '[v].
Proof. by move=> ouv; rewrite hnormD ouv rmorph0 mulr0 !addr0. Qed.

Lemma hnormBd u v : '[u, v] = 0 -> '[u - v] = '[u] + '[v].
Proof. by move=> ouv; rewrite hnormDd ?hnormN // linearN /= ouv oppr0. Qed.

Local Notation "u _|_ v" := ('[u, v] == 0) : ring_scope.

Definition ortho_rec S1 S2 :=
  all [pred u | all [pred v | u _|_ v] S2] S1.

Fixpoint pair_ortho_rec S :=
  if S is v :: S' then ortho_rec [:: v] S' && pair_ortho_rec S' else true.

(* We exclude 0 from pairwise orthogonal sets. *)
Definition pairwise_orthogonal S := (0 \notin S) && pair_ortho_rec S.

Definition orthonormal S := all [pred v | '[v] == 1] S && pair_ortho_rec S.

Definition orthogonal S1 S2 := nosimpl (@ortho_rec S1 S2).

Lemma orthogonal_cons u us vs :
  orthogonal (u :: us) vs = orthogonal [:: u] vs && orthogonal us vs.
Proof. by rewrite /orthogonal /= andbT. Qed.

Lemma orthonormal_not0 S : orthonormal S -> 0 \notin S.
Proof.
by case/andP=> /allP S1 _; rewrite (contra (S1 _)) //= linear0r eq_sym oner_eq0.
Qed.

Lemma orthonormalE S :
  orthonormal S = all [pred phi | '[phi] == 1] S && pairwise_orthogonal S.
Proof. by rewrite -(andb_idl (@orthonormal_not0 S)) andbCA. Qed.

Lemma orthonormal_orthogonal S : orthonormal S -> pairwise_orthogonal S.
Proof. by rewrite orthonormalE => /andP[_]. Qed.


End HermitianModuleTheory.
Arguments orthogonal {R eps theta U} form S1 S2.
Arguments pairwise_orthogonal {R eps theta U} form S.
Arguments orthonormal {R eps theta U} form S.

Section HermitianIsometry.

Variables (R : ringType) (eps : bool) (theta : {rmorphism R -> R}).
Variables (U1 U2: lmodType R) (form1 : {hermitian U1 for eps & theta})
          (form2 : {hermitian U2 for eps & theta}).

Local Notation "''[' u , v ]_1" := (form1 u%R v%R) : ring_scope.
Local Notation "''[' u , v ]_2" := (form2 u%R v%R) : ring_scope.
Local Notation "''[' u ]_1" := (form1 u%R u%R)  : ring_scope.
Local Notation "''[' u ]_2" := (form2 u%R u%R): ring_scope.
Definition isometry tau := forall u v, (form1 (tau u) (tau v))= (form2 u%R v%R).


Definition isometry_from_to mD tau mR :=
   prop_in2 mD (inPhantom (isometry tau))
  /\ prop_in1 mD (inPhantom (forall u, in_mem (tau u) mR)).

Notation "{ 'in' D , 'isometry' tau , 'to' R }" :=
    (isometry_from_to (mem D) tau (mem R))
  (at level 0, format "{ 'in'  D ,  'isometry'  tau ,  'to'  R }")
     : type_scope.

End  HermitianIsometry.

Section HermitianVectTheory.

Variables (R : fieldType) (eps : bool) (theta : {rmorphism R -> R}).
Variable (U : lmodType R) (form : {hermitian U for eps & theta}).

Local Notation "''[' u , v ]" := (form u%R v%R) : ring_scope.
Local Notation "''[' u ]" := '[u, u]%R : ring_scope.

Lemma herm_eq0C u v : ('[u, v] == 0) = ('[v, u] == 0).
Proof. by rewrite hermC mulf_eq0 signr_eq0 /= fmorph_eq0. Qed.

End HermitianVectTheory.

Section HermitianFinVectTheory.

Variables (F : fieldType) (eps : bool) (theta : {rmorphism F -> F}).
Variable (vT : vectType F) (form : {hermitian vT for eps & theta}).
Let n := \dim {:vT}.
Implicit Types (u v : vT) (U V : {vspace vT}).

Local Notation "''[' u , v ]" := (form u%R v%R) : ring_scope.
Local Notation "''[' u ]" := '[u, u]%R : ring_scope.

Let alpha v := (linfun (applyr form v : vT -> F^o)).

Definition orthov V := (\bigcap_(i < \dim V) lker (alpha (vbasis V)`_i))%VS.

Local Notation "U _|_ V" := (U <= orthov V)%VS : vspace_scope.

Lemma mem_orthovPn V u : reflect (exists2 v, v \in V & '[u, v] != 0) (u \notin orthov V).
Proof.
apply: (iffP idP) => [u_orthovV|[v /coord_vbasis-> uvNorthov]]; last first.
  apply/subv_bigcapP => uP; rewrite linear_sum big1 ?eqxx //= in uvNorthov.
  move=> i _; have := uP i isT.
  by rewrite -memvE memv_ker lfunE linearZ => /eqP/=->; rewrite mulr0.
suff /existsP [i ui_neq0] : [exists i : 'I_(\dim V), '[u, (vbasis V)`_i] != 0].
  by exists (vbasis V)`_i => //; rewrite vbasis_mem ?mem_nth ?size_tuple.
apply: contraNT u_orthovV; rewrite negb_exists => /forallP ui_eq0.
by apply/subv_bigcapP => i _; rewrite -memvE memv_ker lfunE /= -[_ == _]negbK.
Qed.

Lemma mem_orthovP V u : reflect {in V, forall v, '[u, v] = 0} (u \in orthov V).
Proof.
apply: (iffP idP) => [/mem_orthovPn orthovNu v vV|/(_ _ _)/eqP orthov_u].
  by apply/eqP/negP=> /negP Northov_uv; apply: orthovNu; exists v.
by apply/mem_orthovPn => -[v /orthov_u->].
Qed.

Lemma orthov1E u : orthov <[u]> = lker (alpha u).
Proof.
apply/eqP; rewrite eqEsubv; apply/andP.
split; apply/subvP=> v; rewrite memv_ker lfunE /=.
   by move=> /mem_orthovP-> //; rewrite ?memv_line.
move=> vu_eq0; apply/mem_orthovP => w /vlineP[k->].
by apply/eqP; rewrite linearZ mulf_eq0 vu_eq0 orbT.
Qed.

Lemma orthovP U V : reflect {in U & V, forall u v, '[u, v] = 0} (U _|_ V)%VS.
Proof.
apply: (iffP subvP); last by move=> H ??; apply/mem_orthovP=> ??; apply: H.
by move=> /(_ _ _)/mem_orthovP; move=> H ????; apply: H.
Qed.

Lemma orthov_sym U V : (U _|_ V)%VS = (V _|_ U)%VS.
Proof. by apply/orthovP/orthovP => eq0 ????; apply/eqP; rewrite herm_eq0C eq0. Qed.

Lemma mem_orthov1 v u : (u \in orthov <[v]>) = ('[u, v] == 0).
Proof. by rewrite orthov1E memv_ker lfunE. Qed.

Lemma orthov11 u v : (<[u]> _|_ <[v]>)%VS = ('[u, v] == 0).
Proof. exact: mem_orthov1. Qed.

Lemma mem_orthov1_sym v u : (u \in orthov <[v]>) = (v \in orthov <[u]>).
Proof. exact: orthov_sym. Qed.

Lemma orthov0 : orthov 0 = fullv.
Proof.
apply/eqP; rewrite eqEsubv subvf.
by apply/subvP => x _; rewrite mem_orthov1 linear0.
Qed.

Lemma mem_orthov_sym V u : (u \in orthov V) = (V <= orthov <[u]>)%VS.
Proof. exact: orthov_sym. Qed.

Lemma leq_dim_orthov1 u V : ((\dim V).-1 <= \dim (V :&: orthov <[u]>))%N.
Proof.
rewrite -(limg_ker_dim (alpha u) V) -orthov1E.
have := dimvS (subvf (alpha u @: V)); rewrite dimvf addnC.
by case: (\dim _) => [|[]] // _; rewrite leq_pred.
Qed.

Lemma dim_img_form_eq1 u V : u \notin orthov V -> \dim (alpha u @: V)%VS = 1%N.
Proof.
move=> /mem_orthovPn [v vV Northov_uv]; apply/eqP; rewrite eqn_leq /=.
rewrite -[1%N as X in (_ <= X)%N](dimvf [vectType F of F^o]) dimvS ?subvf//=.
have := @dimvS _ _ <['[v, u] : F^o]> (alpha u @: V).
rewrite -memvE dim_vline herm_eq0C Northov_uv; apply.
by apply/memv_imgP; exists v; rewrite ?memvf// !lfunE /=.
Qed.

Lemma eq_dim_orthov1 u V : u \notin orthov V -> (\dim V).-1 = \dim (V :&: orthov <[u]>).
Proof.
rewrite -(limg_ker_dim (alpha u) V) => /dim_img_form_eq1->.
by rewrite -orthov1E addn1.
Qed.

Lemma dim_img_form_eq0 u V : u \in orthov V -> \dim (alpha u @: V)%VS = 0%N.
Proof. by move=> uV; apply/eqP; rewrite dimv_eq0 -lkerE -orthov1E orthov_sym. Qed.

Lemma neq_dim_orthov1 u V : (\dim V > 0)%N ->
  u \in orthov V -> ((\dim V).-1 < \dim (V :&: orthov <[u]>))%N.
Proof.
move=> V_gt0; rewrite -(limg_ker_dim (alpha u) V) -orthov1E => u_in.
rewrite dim_img_form_eq0 // addn0 (capv_idPl _) 1?orthov_sym //.
by case: (\dim _) V_gt0.
Qed.

Lemma leqif_dim_orthov1 u V : (\dim V > 0)%N ->
   ((\dim V).-1 <= \dim (V :&: orthov <[u]>) ?= iff (u \notin orthov V))%N.
Proof.
move=> Vr_gt0; apply/leqifP.
by case: (boolP (u \in _)) => /= [/neq_dim_orthov1->|/eq_dim_orthov1->].
Qed.

Lemma leqif_dim_orthov1_full u : (n > 0)%N ->
   ((\dim {:vT}).-1 <= \dim (orthov <[u]>) ?= iff (u \notin orthov fullv))%N.
Proof.
by move=> n_gt0; have := @leqif_dim_orthov1 u fullv; rewrite capfv; apply.
Qed.

(* Link between orthov and orthovgonality of sequences *)
Lemma orthogonal1P u v : reflect ('[u, v] = 0) (orthogonal form [:: u] [:: v]).
Proof. by rewrite /orthogonal /= !andbT; apply: eqP. Qed.

Lemma orthogonalP us vs :
  reflect {in us & vs, forall u v, '[u, v] = 0} (orthogonal form us vs).
Proof.
apply: (iffP allP) => ousvs u => [v /ousvs/allP opus /opus/eqP // | /ousvs opus].
by apply/allP=> v /= /opus->.
Qed.

Lemma orthogonal_oppr S R : orthogonal form S (map -%R R) = orthogonal form S R.
Proof.
wlog suffices IH: S R / orthogonal form S R -> orthogonal form S (map -%R R).
  by apply/idP/idP=> /IH; rewrite ?mapK //; apply: opprK.
move/orthogonalP=> oSR; apply/orthogonalP=> xi1 _ Sxi1 /mapP[xi2 Rxi2 ->].
by rewrite linearNr /= oSR ?oppr0.
Qed.

Lemma orthogonalE us vs : (orthogonal form us vs) = (<<us>> _|_ <<vs>>)%VS.
Proof.
apply/orthogonalP/orthovP => uvsP u v; last first.
  by move=> uus vvs; rewrite uvsP // memv_span.
rewrite -[us]in_tupleE -[vs]in_tupleE => /coord_span-> /coord_span->.
rewrite linear_sum big1 //= => i _; rewrite linear_suml big1 //= => j _.
by rewrite linearZlr/= uvsP ?mulr0// mem_nth.
Qed.

Lemma orthovE U V : (U _|_ V)%VS = orthogonal form (vbasis U) (vbasis V).
Proof. by rewrite orthogonalE !(span_basis (vbasisP _)). Qed.

Notation radv := (orthov fullv).

Lemma orthoDv U V W : (U + V _|_ W)%VS = (U _|_ W)%VS && (V _|_ W)%VS.
Proof. by rewrite subv_add. Qed.

Lemma orthovD U V W : (U _|_ V + W)%VS = (U _|_ V)%VS && (U _|_ W)%VS.
Proof. by rewrite ![(U _|_ _)%VS]orthov_sym orthoDv. Qed.

Definition nondegenerate := radv == 0%VS.
Definition is_symplectic := [/\ nondegenerate, is_skew form &
                                2 \in [char F] -> forall u, '[u, u] = 0].
Definition is_orthogonal := [/\ nondegenerate, is_sym form &
                                2 \in [char F] -> forall u, '[u, u] = 0].
Definition is_unitary := nondegenerate /\ (is_hermsym form).

End HermitianFinVectTheory.

Arguments orthogonalP {F eps theta vT form us vs}.
Arguments orthovP {F eps theta vT form U V}.
Arguments mem_orthovPn {F eps theta vT form V u}.
Arguments mem_orthovP {F eps theta vT form V u}.

Section DotVectTheory.

Variables (C : numClosedFieldType).
Variable (U : lmodType C) (form : {dot U for conjC}).

Local Notation "''[' u , v ]" := (form u%R v%R) : ring_scope.
Local Notation "''[' u ]" := '[u, u]%R : ring_scope.

Let neq0_dnorm_gt0 u : u != 0 -> 0 < '[u].
Proof. by case: form => [?[?]] /=; apply. Qed.

Lemma dnorm_geiff0 u : 0 <= '[u] ?= iff (u == 0).
Proof.
by apply/leifP; have [->|uN0] := altP eqP; rewrite ?linear0 ?neq0_dnorm_gt0.
Qed.

Lemma dnorm_ge0 u : 0 <= '[u]. Proof. by rewrite dnorm_geiff0. Qed.

Lemma dnorm_eq0 u : ('[u] == 0) = (u == 0).
Proof. by rewrite -dnorm_geiff0 eq_sym. Qed.

Lemma dnorm_gt0 u : (0 < '[u]) = (u != 0).
Proof. by rewrite lt_def dnorm_eq0 dnorm_ge0 andbT. Qed.

Lemma sqrt_dnorm_ge0 u : 0 <= sqrtC '[u].
Proof. by rewrite sqrtC_ge0 dnorm_ge0. Qed.

Lemma sqrt_dnorm_eq0 u : (sqrtC '[u] == 0) = (u == 0).
Proof. by rewrite sqrtC_eq0 dnorm_eq0. Qed.

Lemma sqrt_dnorm_gt0 u : (sqrtC '[u] > 0) = (u != 0).
Proof. by rewrite sqrtC_gt0 dnorm_gt0. Qed.

Lemma dnormZ a u : '[a *: u]= `|a| ^+ 2 * '[u].
Proof. by rewrite linearZlr/= mulrA normCK. Qed.

Lemma dnormD u v : let d := '[u, v] in '[u + v] = '[u] + '[v] + (d + d^*).
Proof. by rewrite hnormD mul1r. Qed.

Lemma dnormB u v : let d := '[u, v] in '[u - v] = '[u] + '[v] - (d + d^*).
Proof. by rewrite hnormB mul1r. Qed.

End DotVectTheory.

Section HermitianTheory.

Variables (C : numClosedFieldType) (eps : bool) (theta : {rmorphism C -> C}).
(* Variable (U : lmodType C) (form : {hermitian U for eps & theta}). *)
Variable (U : lmodType C)  (form : {dot U for conjC}).
Local Notation "''[' u , v ]" := (form u%R v%R) : ring_scope.
Local Notation "''[' u ]" := '[u, u]%R : ring_scope.

Lemma pairwise_orthogonalP  S :
  reflect (uniq (0 :: S)
             /\ {in S &, forall phi psi, phi != psi -> '[phi, psi] = 0})
          (pairwise_orthogonal form S).
Proof.
rewrite /pairwise_orthogonal /=; case notS0: (~~ _); last by right; case.
elim: S notS0 => [|phi S IH] /=; first by left.
rewrite inE eq_sym andbT => /norP[nz_phi {}/IH IH].
have [opS | not_opS] := allP; last first.
  right=> [[/andP[notSp _] opS]]; case: not_opS => psi Spsi /=.
  by rewrite opS ?mem_head 1?mem_behead // (memPnC notSp).
rewrite (contra (opS _)) /= ?dnorm_eq0 //.
apply: (iffP IH) => [] [uniqS oSS]; last first.
  by split=> //; apply: sub_in2 oSS => psi Spsi; apply: mem_behead.
split=> // psi xi; rewrite !inE => /predU1P[-> // | Spsi].
  by case/predU1P=> [-> | /opS] /eqP.
case/predU1P=> [-> _ | Sxi /oSS-> //].
 apply/eqP; rewrite hermC.
by move:(opS psi   Spsi) => /= /eqP ->; rewrite rmorph0 mulr0.
Qed.

Lemma pairwise_orthogonal_cat R S :
  pairwise_orthogonal form (R ++ S) =
    [&& pairwise_orthogonal form R, pairwise_orthogonal form  S & orthogonal form R S].
Proof.
rewrite /pairwise_orthogonal mem_cat negb_or -!andbA; do !bool_congr.
elim: R => [|phi R /= ->]; rewrite ?andbT // orthogonal_cons all_cat -!andbA /=.
by do !bool_congr.
Qed.



Lemma orthonormal_cat R S :
  orthonormal form (R ++ S) = [&& orthonormal form R, orthonormal form S & orthogonal form R S].
Proof.
rewrite !orthonormalE pairwise_orthogonal_cat all_cat -!andbA.
by do !bool_congr.
Qed.



Lemma orthonormalP S :
  reflect (uniq S /\ {in S &, forall phi psi, '[phi, psi] = (phi == psi)%:R})
          (orthonormal form S).
Proof.
rewrite orthonormalE; have [/= normS | not_normS] := allP; last first.
  by right=> [[_ o1S]]; case: not_normS => phi Sphi; rewrite /= o1S ?eqxx.
apply: (iffP (pairwise_orthogonalP S)) => [] [uniqS oSS].
  split=> // [|phi psi]; first by case/andP: uniqS.
  by have [-> _ /normS/eqP | /oSS] := altP eqP.
split=> // [|phi psi Sphi Spsi /negbTE]; last by rewrite oSS // => ->.
by rewrite /= (contra (normS _)) // linear0r  eq_sym oner_eq0.
Qed.



Lemma sub_orthonormal S1 S2 :
  {subset S1 <= S2} -> uniq S1 -> orthonormal form S2 -> orthonormal form S1.
Proof.
move=> sS12 uniqS1 /orthonormalP[_ oS1].
by apply/orthonormalP; split; last apply: sub_in2 sS12 _ _.
Qed.


Lemma orthonormal2P phi psi :
  reflect [/\ '[phi, psi] = 0, '[phi] = 1 & '[psi] = 1]
          (orthonormal form [:: phi; psi]).
Proof.
rewrite /orthonormal /= !andbT andbC.
by apply: (iffP and3P) => [] []; do 3!move/eqP->.
Qed.

End HermitianTheory.

Section DotFinVectTheory.

Variables (C : numClosedFieldType).
Variable (U : vectType C) (form : {dot U for conjC}).

Local Notation "''[' u , v ]" := (form u%R v%R) : ring_scope.
Local Notation "''[' u ]" := '[u, u]%R : ring_scope.

Lemma sub_pairwise_orthogonal S1 S2 :
    {subset S1 <= S2} ->  uniq S1 ->
  pairwise_orthogonal form S2 -> pairwise_orthogonal form S1.
Proof.
move=> sS12 uniqS1 /pairwise_orthogonalP[/andP[notS2_0 _] oS2].
apply/pairwise_orthogonalP; rewrite /= (contra (sS12 0)) //.
by split=> //; apply: sub_in2 oS2.
Qed.

Lemma orthogonal_free S : pairwise_orthogonal form S -> free  S.
Proof.
case/pairwise_orthogonalP=> [/=/andP[notS0 uniqS] oSS].
rewrite -(in_tupleE S); apply/freeP => a aS0 i.
have S_i: S`_i \in S by apply: mem_nth.
have /eqP: '[S`_i, 0] = 0 := linear0r _ _.
rewrite -{2}aS0 raddf_sum /= (bigD1 i) //= big1 => [|j neq_ji]; last 1 first.
  by rewrite linearZ /= oSS ?mulr0 ?mem_nth // eq_sym nth_uniq.
rewrite addr0 linearZ mulf_eq0 conjC_eq0 dnorm_eq0.
by case/pred2P=> // Si0; rewrite -Si0 S_i in notS0.
Qed.

Lemma filter_pairwise_orthogonal S p :
  pairwise_orthogonal form S -> pairwise_orthogonal form (filter p S).
Proof.
move=> orthoS; apply: sub_pairwise_orthogonal (orthoS).
  exact: mem_subseq (filter_subseq p S).
exact/filter_uniq/free_uniq/orthogonal_free.
Qed.

Lemma orthonormal_free S : orthonormal form  S -> free S.
Proof. by move/orthonormal_orthogonal/orthogonal_free. Qed.

Theorem CauchySchwarz (u v : U) :
  `|'[u, v]| ^+ 2 <= '[u] * '[v] ?= iff ~~ free [:: u; v].
Proof.
rewrite free_cons span_seq1 seq1_free -negb_or negbK orbC.
have [-> | nz_v] /= := altP (v =P 0).
  by apply/leifP; rewrite /= !linear0 normCK mul0r mulr0.
without loss ou: u / '[u, v] = 0.
  move=> IHo; pose a := '[u, v] / '[v]; pose u1 := u - a *: v.
  have ou: '[u1, v] = 0.
    by rewrite linearBl/= linearZl/= divfK ?dnorm_eq0 ?subrr.
  rewrite (canRL (subrK _) (erefl u1)) rpredDr ?rpredZ ?memv_line //.
  rewrite linearDl /= ou add0r linearZl/= normrM (ger0_norm (dnorm_ge0 _ _)).
  rewrite exprMn mulrA -dnormZ hnormDd/=; last by rewrite linearZ/= ou mulr0.
  by have:= IHo _ ou; rewrite mulrDl -leif_subLR subrr ou normCK mul0r.
rewrite ou normCK mul0r; split; first by rewrite mulr_ge0 ?dnorm_ge0.
rewrite eq_sym mulf_eq0 orbC dnorm_eq0 (negPf nz_v) /=.
apply/idP/idP=> [|/vlineP[a {2}->]]; last by rewrite linearZ/= ou mulr0.
by rewrite dnorm_eq0 => /eqP->; apply: rpred0.
Qed.

Lemma CauchySchwarz_sqrt u v :
  `|'[u, v]| <= sqrtC '[u] * sqrtC '[v] ?= iff ~~ free [:: u; v].
Proof.
rewrite -(sqrCK (normr_ge0 _)) -sqrtCM ?qualifE ?dnorm_ge0 //.
rewrite (mono_in_leif (@ler_sqrtC _)) 1?rpredM ?qualifE;
by rewrite ?normr_ge0 ?dnorm_ge0 //; apply: CauchySchwarz.
Qed.

Lemma orthoP phi psi : reflect ('[phi, psi] = 0) (orthogonal form  [:: phi] [:: psi]).
Proof. by rewrite /orthogonal /= !andbT; apply: eqP. Qed.

Lemma orthoPl phi S :
  reflect {in S, forall psi, '[phi, psi] = 0} (orthogonal form [:: phi] S).
Proof.
by rewrite [orthogonal form _ S]andbT /=; apply: (iffP allP) => ophiS ? /ophiS/eqP.
Qed.
Arguments orthoPl {phi S}.

Lemma orthogonal_sym : symmetric (orthogonal form).
Proof.
apply: symmetric_from_pre => R S /orthogonalP oRS.
by apply/orthogonalP=> phi psi Rpsi Sphi; rewrite hermC /= oRS  ?rmorph0 ?mulr0.
Qed.

Lemma orthoPr S psi :
  reflect {in S, forall phi, '[phi, psi] = 0} (orthogonal form S [:: psi]).
Proof.
rewrite orthogonal_sym.
by apply: (iffP orthoPl) => oSpsi phi Sphi; rewrite hermC /= oSpsi //= conjC0 mulr0.
Qed.

Lemma orthogonal_catl R1 R2 S :
  orthogonal form (R1 ++ R2) S = orthogonal form R1 S && orthogonal form R2 S.
Proof. exact: all_cat. Qed.

Lemma orthogonal_catr R S1 S2 :
  orthogonal form R (S1 ++ S2) = orthogonal form R S1 && orthogonal form R S2.
Proof. by rewrite !(orthogonal_sym R) orthogonal_catl. Qed.

Lemma eq_pairwise_orthogonal R S :
  perm_eq R S -> pairwise_orthogonal form R = pairwise_orthogonal form  S.
Proof.
apply: catCA_perm_subst R S => R S S'.
rewrite !pairwise_orthogonal_cat !orthogonal_catr (orthogonal_sym R S) -!andbA.
by do !bool_congr.
Qed.


Lemma eq_orthonormal S0 S : perm_eq S0 S -> orthonormal form S0 = orthonormal form S.
Proof.
move=> eqRS; rewrite !orthonormalE (eq_all_r (perm_mem eqRS)).
by rewrite (eq_pairwise_orthogonal eqRS).
Qed.


Lemma orthogonal_oppl S R : orthogonal form  (map -%R S) R = orthogonal form S R.
Proof. by rewrite -!(orthogonal_sym R) orthogonal_oppr. Qed.


Lemma triangle_lerif u v :
  sqrtC '[u + v] <= sqrtC '[u] + sqrtC '[v]
           ?= iff ~~ free [:: u; v] && (0 <= coord [tuple v] 0 u).
Proof.
rewrite -(mono_in_leif ler_sqr) ?rpredD ?qualifE ?sqrtC_ge0 ?dnorm_ge0 //.
rewrite andbC sqrrD !sqrtCK addrAC dnormD (mono_leif (ler_add2l _))/=.
rewrite -mulr_natr -[_ + _](divfK (negbT (pnatr_eq0 C 2))) -/('Re _).
rewrite (mono_leif (ler_pmul2r _)) ?ltr0n //.
have:= leif_trans (leif_Re_Creal '[u, v]) (CauchySchwarz_sqrt u v).
congr (_ <= _ ?= iff _); apply: andb_id2r.
rewrite free_cons span_seq1 seq1_free -negb_or negbK orbC.
have [-> | nz_v] := altP (v =P 0); first by rewrite linear0 coord0.
case/vlineP=> [x ->]; rewrite linearZl linearZ/= pmulr_lge0 ?dnorm_gt0 //=.
by rewrite (coord_free 0) ?seq1_free // eqxx mulr1.
Qed.

Lemma span_orthogonal S1 S2 phi1 phi2 :
    orthogonal form S1 S2 -> phi1 \in <<S1>>%VS -> phi2 \in <<S2>>%VS ->
 '[phi1, phi2] = 0.
Proof.
move/orthogonalP=> oS12; do 2!move/(@coord_span _ _ _ (in_tuple _))->.
rewrite linear_suml big1 // => i _; rewrite linear_sumr big1 // => j _.
by rewrite linearZlr/= oS12 ?mem_nth ?mulr0.
Qed.

Lemma orthogonal_split S beta :
  {X: U  & X \in <<S>>%VS &
      {Y:U | [/\ beta = X + Y, '[X, Y] = 0 & orthogonal form  [:: Y]  S]}}.
Proof.
suffices [X S_X [Y -> oYS]]:
  {X : _ & X \in <<S>>%VS & {Y | beta = X + Y & orthogonal form [:: Y] S}}.
- exists X => //; exists Y.
  by rewrite hermC /= (span_orthogonal oYS) ?memv_span1 ?conjC0 // mulr0.
elim: S beta => [|phi S IHS] beta.
  by exists 0; last exists beta; rewrite ?mem0v ?add0r.
have [[UU S_U [V -> oVS]] [X S_X [Y -> oYS]]] := (IHS phi, IHS beta).
pose Z := '[Y, V] / '[V] *: V; exists (X + Z).
  rewrite /Z -{4}(addKr UU V) scalerDr scalerN addrA addrC span_cons.
  by rewrite memv_add ?memvB ?memvZ ?memv_line.
exists (Y - Z); first by rewrite addrCA !addrA addrK addrC.
apply/orthoPl=> psi; rewrite !inE => /predU1P[-> | Spsi]; last first.
  by rewrite linearBl linearZl /= (orthoPl oVS _ Spsi) mulr0 subr0 (orthoPl oYS).
rewrite linearBl !linearDr /= (span_orthogonal oYS) // ?memv_span ?mem_head //.
rewrite !linearZl /= (span_orthogonal oVS _ S_U) ?mulr0 ?memv_span ?mem_head //.
have [-> | nzV] := eqVneq V 0; first by rewrite linear0r !mul0r subrr.
by rewrite divfK ?dnorm_eq0 ?subrr.
Qed.

End DotFinVectTheory.

Arguments orthoP {C U form phi psi}.
Arguments pairwise_orthogonalP {C U form S}.
Arguments orthonormalP {C U form S}.
Arguments orthoPl {C U form phi S}.
Arguments orthoPr {C U form S psi}.

Local Notation "u '``_' i" := (u (GRing.zero (Zp_zmodType O)) i) : ring_scope.
Local Notation "''e_' i" := (delta_mx 0 i)
 (format "''e_' i", at level 3) : ring_scope.

Local Notation "M ^ phi" := (map_mx phi M).
Local Notation "M ^t phi" := (map_mx phi (M ^T)) (phi at level 30, at level 30).

Section  BuildIsometries.

Variables (C : numClosedFieldType).
Variables (U U1 U2: vectType C).
Variables (form : {dot U for conjC}) (form1 : {dot U1 for conjC}) (form2 : {dot U2 for conjC}).

Definition normf1 := fun u => form1 u u.
Definition normf2 := fun u => form2 u u.

Lemma isometry_of_dnorm S tauS :
    pairwise_orthogonal form1 S -> pairwise_orthogonal form2 tauS ->
    map normf2 tauS = map normf1 S ->
  {tau : {linear U1 -> U2} | map tau S = tauS
                                   & {in <<S>>%VS &, isometry form2 form1 tau}}.
Proof.
move=> oS oT eq_nST; have freeS := orthogonal_free oS.
have eq_sz: size tauS = size S by have:= congr1 size eq_nST; rewrite !size_map.
have [tau defT] := linear_of_free S tauS; rewrite -[S]/(tval (in_tuple S)).
exists tau => [|u v /coord_span-> /coord_span->]; rewrite ?raddf_sum ?defT //=.
apply: eq_bigr => i _ /=; rewrite !linearZ/= !linear_suml; congr (_ * _).
apply: eq_bigr => j _ /=; rewrite linearZ !linearZl; congr (_ * _).
rewrite -!(nth_map 0 0 tau) ?{}defT //; have [-> | neq_ji] := eqVneq j i.
  by rewrite /=  -[RHS](nth_map 0 0 normf1) -?[LHS](nth_map 0 0 normf2) ?eq_sz // eq_nST.
have{oS} [/=/andP[_ uS] oS] := pairwise_orthogonalP oS.
have{oT} [/=/andP[_ uT] oT] := pairwise_orthogonalP oT.
by rewrite oS ?oT ?mem_nth ?nth_uniq ?eq_sz.
Qed.


Lemma isometry_of_free S f :
    free S -> {in S &, isometry form2 form1 f} ->
  {tau : {linear U1 -> U2} |
    {in S, tau =1 f} & {in <<S>>%VS &, isometry form2 form1 tau}}.
Proof.
move=> freeS If; have defS := free_span freeS.
have [tau /(_ freeS (size_map f S))Dtau] := linear_of_free S (map f S).
have {}Dtau: {in S, tau =1 f}.
  by move=> _ /(nthP 0)[i ltiS <-]; rewrite -!(nth_map 0 0) ?Dtau.
exists tau => // _ _ /defS[a -> _] /defS[b -> _] /=.
rewrite  2!{1}linear_sum /= !{1}linear_suml /=;  apply/eq_big_seq=> xi1 Sxi1.
rewrite !{1}linear_sumr; apply/eq_big_seq=> xi2 Sxi2 /=.
by rewrite !linearZ /= !linearZl !Dtau //= If.
Qed.


Lemma isometry_raddf_inj  (tau : {additive U1 -> U2}) :
    {in U1 &, isometry form2 form1 tau} ->
    {in U1 &, forall u v, u - v \in U1} ->
  {in U1 &, injective tau}.
Proof.
move=> Itau linU phi psi Uphi Upsi /eqP; rewrite -subr_eq0 -raddfB.
by rewrite -(dnorm_eq0 form2)  Itau ?linU // dnorm_eq0 subr_eq0 => /eqP.
Qed.


End BuildIsometries.

Section MatrixForms.

Variables (R : fieldType) (n : nat).
Implicit Types (a b : R) (u v : 'rV[R]_n).
Implicit Types (M N P Q : 'M[R]_n).

Section Def.
Variable (theta : R -> R).

Definition form_of_matrix m M (U  V : 'M_(m, n)) := \tr (U *m M *m (V ^t theta)).
Definition matrix_of_form (form : 'rV[R]_n -> 'rV[R]_n -> R) : 'M[R]_n :=
  \matrix_(i, j) form 'e_i 'e_j.
Definition orthomx m M (B : 'M_(m,n)) : 'M_n := (kermx (M *m (B ^t theta))).

Implicit Type form : {bilinear 'rV[R]_n -> 'rV[R]_n -> R | *%R & theta \; *%R}.

Lemma matrix_of_formE form i j : matrix_of_form form i j = form 'e_i 'e_j.
Proof. by rewrite mxE. Qed.
End Def.

Section FormOfMatrix.
Variables (m : nat) (M : 'M[R]_n).
Implicit Types (U V : 'M[R]_(m, n)).
Variables (theta : {rmorphism R -> R}).

Local Notation "''[' U , V ]" := (form_of_matrix theta M U%R V%R) : ring_scope.
Local Notation "''[' U ]" := '[U, U]%R : ring_scope.

Lemma form_of_matrix_is_linear U :
  linear_for (theta \; *%R) (form_of_matrix theta M U).
Proof.
rewrite /form_of_matrix => k v w; rewrite -linearP/=.
by rewrite linearP map_mxD map_mxZ !mulmxDr !scalemxAr.
Qed.
Canonical form_of_matrix_additive U := Additive (form_of_matrix_is_linear U).
Canonical form_of_matrix_linear U := Linear (form_of_matrix_is_linear U).

Definition form_of_matrixr U := (form_of_matrix theta M)^~U.
Lemma form_of_matrixr_is_linear U : linear_for *%R (form_of_matrixr U).
Proof.
rewrite /form_of_matrixr /form_of_matrix => k v w.
by rewrite -linearP /= !mulmxDl -!scalemxAl.
Qed.
Canonical form_of_matrixr_additive U := Additive (form_of_matrixr_is_linear U).
Canonical form_of_matrixr_linear U := Linear (form_of_matrixr_is_linear U).
Canonical form_of_matrixr_rev :=
  [revop form_of_matrixr of form_of_matrix theta M].
Canonical form_of_matrix_is_bilinear := [bilinear of form_of_matrix theta M].

End FormOfMatrix.

Section FormOfMatrix1.
Variables (M : 'M[R]_n).
Variables (theta : {rmorphism R -> R}).

Local Notation "''[' u , v ]" := (form_of_matrix theta M u%R v%R) : ring_scope.
Local Notation "''[' u ]" := '[u, u]%R : ring_scope.

Lemma formee i j : '['e_i :'rV__, 'e_j] = M i j.
Proof.
rewrite /form_of_matrix -rowE -map_trmx map_delta_mx -[M in LHS]trmxK.
by rewrite -tr_col -trmx_mul -rowE trace_mx11 !mxE.
Qed.

Lemma form_of_matrixK : matrix_of_form (form_of_matrix theta M) = M.
Proof. by apply/matrixP => i j; rewrite !mxE formee. Qed.

Lemma form0_eq0 : M = 0 -> forall u v, '[u, v] = 0.
Proof.
by rewrite /form_of_matrix => -> u v; rewrite mulmx0 mul0mx trace_mx11 mxE.
Qed.

End FormOfMatrix1.

Section MatrixOfForm.
Variable (theta : {rmorphism R -> R}).
Variable (form : {bilinear 'rV[R]_n -> 'rV[R]_n -> R | *%R & theta \; *%R}).

Lemma matrix_of_formK : form_of_matrix theta (matrix_of_form form) =2 form.
Proof.
set f := (X in X =2 _); have f_eq i j : f 'e_i 'e_j = form 'e_i 'e_j.
  by rewrite /f formee mxE.
move=> u v; rewrite [u]row_sum_delta [v]row_sum_delta /f.
rewrite !linear_sum/=; apply: eq_bigr => j _.
rewrite !linear_suml/=; apply: eq_bigr => i _.
by rewrite !linearZlr/= -f_eq.
Qed.

End MatrixOfForm.

Section HermitianMx.
Variable (eps : bool).

Section HermitianMxDef.
Variable (theta : R -> R).

Definition hermitianmx :=
  [qualify M : 'M_n | M == ((-1) ^+ eps) *: M ^t theta].
Fact hermitianmx_key : pred_key hermitianmx. Proof. by []. Qed.
Canonical hermitianmx_keyed := KeyedQualifier hermitianmx_key.

Structure hermitian_matrix := HermitianMx {
  mx_of_hermitian :> 'M[R]_n;
  _ : mx_of_hermitian \is hermitianmx
}.

Lemma is_hermitianmxE M :
  (M \is hermitianmx) = (M == (-1) ^+ eps *: M ^t theta).
Proof. by rewrite qualifE. Qed.

Lemma is_hermitianmxP M :
   reflect (M = (-1) ^+ eps *: M ^t theta) (M \is hermitianmx).
Proof. by rewrite is_hermitianmxE; apply/eqP. Qed.

Lemma hermitianmxE (M : hermitian_matrix) :
  M = ((-1) ^+ eps) *: M ^t theta :> 'M__.
Proof. by apply/eqP; case: M. Qed.

Lemma trmx_hermitian (M : hermitian_matrix) :
  M^T = ((-1) ^+ eps) *: M ^ theta :> 'M__.
Proof. by rewrite {1}hermitianmxE linearZ /= map_trmx trmxK. Qed.

End HermitianMxDef.

Section HermitianMxTheory.
Variables (theta : {involutive_rmorphism R}) (M : hermitian_matrix theta).

Lemma maptrmx_hermitian : M^t theta = (-1) ^+ eps *: (M : 'M__).
Proof.
rewrite trmx_hermitian map_mxZ rmorph_sign -map_mx_comp.
by rewrite (map_mx_id (rmorphK _)).
Qed.

Lemma form_of_matrix_is_hermitian m :
  hermitian_for eps theta (@form_of_matrix theta m M).
Proof.
move=> /= u v; rewrite {1}hermitianmxE /form_of_matrix.
rewrite -!(scalemxAr, scalemxAl) linearZ/=; congr (_ * _).
rewrite -mxtrace_tr -trace_map_mx !(trmx_mul, map_mxM, map_trmx, trmxK).
by rewrite -mulmxA -!map_mx_comp !(map_mx_id (rmorphK _)).
Qed.

Canonical form_of_matrix_hermitian m :=
 (Hermitian (@form_of_matrix_is_hermitian m)).

Local Notation "''[' u , v ]" := (form_of_matrix theta M u%R v%R) : ring_scope.
Local Notation "''[' u ]" := '[u, u]%R : ring_scope.
Local Notation "B ^!" := (orthomx theta M B) : matrix_set_scope.
Local Notation "A _|_ B" := (A%MS <= B%MS^!)%MS : matrix_set_scope.

Lemma orthomxE u v : (u _|_ v)%MS = ('[u, v] == 0).
Proof.
rewrite (sameP sub_kermxP eqP) mulmxA.
by rewrite [_ *m _^t _]mx11_scalar -trace_mx11 fmorph_eq0.
Qed.

Lemma hermmx_eq0P {u v} : reflect ('[u, v] = 0) (u _|_ v)%MS.
Proof. by rewrite orthomxE; apply/eqP. Qed.

Lemma orthomxP p q (A : 'M_(p, n)) (B :'M_(q, n)) :
  reflect (forall (u v : 'rV_n), u <= A -> v <= B -> u _|_ v)%MS
          (A _|_ B)%MS.
Proof.
apply: (iffP idP) => AnB.
  move=> u v uA vB; rewrite (submx_trans uA) // (submx_trans AnB) //.
  apply/sub_kermxP; have /submxP [w ->] := vB.
  rewrite trmx_mul map_mxM !mulmxA -[kermx _ *m _ *m _]mulmxA.
  by rewrite [kermx _ *m _](sub_kermxP _) // mul0mx.
apply/rV_subP => u /AnB /(_ _) /sub_kermxP uMv; apply/sub_kermxP.
suff: forall m (v : 'rV[R]_m),
  (forall i, v *m 'e_i ^t theta = 0 :> 'M_1) -> v = 0.
  apply => i; rewrite !mulmxA -!mulmxA -map_mxM -trmx_mul uMv //.
  by apply/submxP; exists 'e_i.
move=> /= m v Hv; apply: (can_inj (@trmxK _ _ _)).
rewrite trmx0; apply/row_matrixP=> i; rewrite row0 rowE.
apply: (can_inj (@trmxK _ _ _)); rewrite trmx0 trmx_mul trmxK.
by rewrite -(map_delta_mx theta) map_trmx Hv.
Qed.

Lemma orthomx_sym p q (A : 'M_(p, n)) (B :'M_(q, n)) :
  (A _|_ B)%MS = (B _|_ A)%MS.
Proof.
gen have nC : p q A B / (A _|_ B -> B _|_ A)%MS; last by apply/idP/idP; apply/nC.
move=> AnB; apply/orthomxP => u v ? ?; rewrite orthomxE.
rewrite hermC mulf_eq0 ?fmorph_eq0 ?signr_eq0 /=.
by rewrite -orthomxE (orthomxP _ _ AnB).
Qed.

Lemma ortho_ortho_mx p (A : 'M_(p, n)) : (A^! _|_ A)%MS.
Proof. by []. Qed.

Lemma ortho_mx_ortho p (A : 'M_(p, n)) : (A _|_ A^!)%MS.
Proof. by rewrite orthomx_sym. Qed.

Lemma rank_orthomx u : (\rank (u ^!) >= n.-1)%N.
Proof.
rewrite mxrank_ker -subn1 leq_sub2l //.
by rewrite (leq_trans (mxrankM_maxr  _ _)) // rank_leq_col.
Qed.

Notation radmx := (1%:M^!)%MS.

Lemma radmxE : radmx = kermx M.
Proof. by rewrite /orthomx /orthomx trmx1 map_mx1 mulmx1. Qed.

Lemma orthoNmx k m (A : 'M[R]_(k, n)) (B : 'M[R]_(m, n)) :
  ((- A) _|_ B)%MS = (A _|_ B)%MS.
Proof. by rewrite eqmx_opp. Qed.

Lemma orthomxN k m (A : 'M[R]_(k, n)) (B : 'M[R]_(m, n)) :
  (A _|_ (- B))%MS = (A _|_ B)%MS.
Proof. by rewrite ![(A _|_ _)%MS]orthomx_sym orthoNmx. Qed.

Lemma orthoDmx k m p (A : 'M[R]_(k, n)) (B : 'M[R]_(m, n)) (C : 'M[R]_(p, n)) :
  (A + B _|_ C)%MS = (A _|_ C)%MS && (B _|_ C)%MS.
Proof. by rewrite addsmxE !(sameP sub_kermxP eqP) mul_col_mx col_mx_eq0. Qed.

Lemma orthomxD  k m p (A : 'M[R]_(k, n)) (B : 'M[R]_(m, n)) (C : 'M[R]_(p, n)) :
  (A _|_ B + C)%MS = (A _|_ B)%MS && (A _|_ C)%MS.
Proof. by rewrite ![(A _|_ _)%MS]orthomx_sym orthoDmx. Qed.

Lemma orthoZmx p m a (A : 'M[R]_(p, n)) (B : 'M[R]_(m, n)) : a != 0 ->
  (a *: A _|_ B)%MS = (A _|_ B)%MS.
Proof. by move=> a_neq0; rewrite eqmx_scale. Qed.

Lemma orthomxZ p m a (A : 'M[R]_(p, n)) (B : 'M[R]_(m, n)) : a != 0 ->
  (A _|_ (a *: B))%MS = (A _|_ B)%MS.
Proof. by move=> a_neq0; rewrite ![(A _|_ _)%MS]orthomx_sym orthoZmx. Qed.

Lemma eqmx_ortho p m (A : 'M[R]_(p, n)) (B : 'M[R]_(m, n)) :
  (A :=: B)%MS -> (A^! :=: B^!)%MS.
Proof.
move=> eqAB; apply/eqmxP.
by rewrite orthomx_sym -eqAB ortho_mx_ortho orthomx_sym eqAB ortho_mx_ortho.
Qed.

Lemma genmx_ortho p (A : 'M[R]_(p, n)) : (<<A>>^! :=: A^!)%MS.
Proof. exact: (eqmx_ortho (genmxE _)). Qed.

End HermitianMxTheory.
End HermitianMx.
End MatrixForms.

Notation symmetricmx := (hermitianmx _ false idfun).
Notation skewmx := (hermitianmx _ true idfun).
Notation hermsymmx := (hermitianmx _ false (@conjC _)).
