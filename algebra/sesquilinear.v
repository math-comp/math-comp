From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div.
From mathcomp Require Import choice fintype tuple bigop ssralg finset fingroup.
From mathcomp Require Import zmodp poly order ssrnum matrix mxalgebra vector.

(******************************************************************************)
(*                            Sesquilinear forms                              *)
(*                                                                            *)
(*                u ``_ i := u 0 i                                            *)
(*                   e_ j := the row matrix with a 1 in column j              *)
(*                M ^ phi := map_mx phi M                                     *)
(*                           Notation in scope sesquilinear_scope.            *)
(*               M ^t phi := (M ^T) ^ phi                                     *)
(*                           Notation in scope sesquilinear_scope.            *)
(* involutive_rmorphism R == the type of involutive functions                 *)
(*                           R has type nzRingType.                           *)
(*                           The HB class is InvolutiveRMorphism.             *)
(*                                                                            *)
(* {bilinear U -> U' -> V | s & s'} == the type of bilinear forms which are   *)
(*                           essentially functions of type U -> U' -> V       *)
(*                           U and U' are lmodType's, V is a zmodType, s and  *)
(*                           s' are scaling operations of type R -> V -> V.   *)
(*                           The HB class is Bilinear.                        *)
(*                           The factory bilinear_isBilinear provides a way   *)
(*                           to instantiate a bilinear form from two          *)
(*                           GRing.linear_for proofs.                         *)
(* {bilinear U -> V -> W | s } := {bilinear U -> V -> W | s.1 & s.2}          *)
(* {bilinear U -> V -> W} := {bilinear U -> V -> W | *:%R & *:%R }            *)
(*           {biscalar U} := {bilinear U -> U -> _ | *%R & *%R }              *)
(*                                                                            *)
(*             applyr f x := f ^~ x with f : U -> U' -> V                     *)
(*       form theta M u v == form defined from a matrix M                     *)
(*                        := (u *m M *m (v ^t theta)) 0 0                     *)
(*                           u and v are row vectors, M is a square matrix,   *)
(*                           coefficients have type R : fieldType,            *)
(*                           theta is a morphism                              *)
(*                                                                            *)
(* {hermitian U for eps & theta} == hermitian/skew-hermitian form             *)
(*                           eps is a boolean flag,                           *)
(*                           (false -> hermitian, true -> skew-hermitian),    *)
(*                           theta is a function R -> R (R : nzRingType).     *)
(*                           The HB class is Hermitian.                       *)
(*                           *%R is used as a the first scaling operator.     *)
(*                           theta \; *R is used as the second scaling        *)
(*                           operation of the bilinear form.                  *)
(*                           The archetypal case is theta being the complex   *)
(*                           conjugate.                                       *)
(*                                                                            *)
(* M \is (eps, theta).-sesqui == M is a sesquilinear form                     *)
(*                                                                            *)
(*      orthomx theta M B == M-orthogonal completement of B                   *)
(*                        := kermx (M *m B ^t theta)                          *)
(*                           M is a square matrix representing a sesquilinear *)
(*                           form, B is a rectangle matrix representing a     *)
(*                           subspace                                         *)
(*                           (local notation: B ^_|_)                         *)
(*        ortho theta M B == orthomx theta M B with theta a morphism          *)
(*               A '_|_ B := (A%MS <= B^_|_)%MS                               *)
(*                           This is a local notation.                        *)
(*            rad theta M := ortho theta M 1%:M                               *)
(*                           (local notation: 1%:M^_|_)                       *)
(*                                                                            *)
(*          {symmetric U} == symmetric form                                   *)
(*                        := {hermitian U for false & idfun}                  *)
(*     {skew_symmetric U} == skew-symmetric form                              *)
(*                        := {hermitian U for true & idfun}                   *)
(* {hermitian_sym U for theta} := hermitian form using theta (eps = false)    *)
(*      {dot U for theta} == type of positive definite forms                  *)
(*                           The HB class is Dot.                             *)
(*                                                                            *)
(*    is_skew eps theta form := eps = true /\ theta = idfun                   *)
(*     is_sym eps theta form := eps = false /\ theta = idfun                  *)
(* is_hermsym eps theta form := eps = false                                   *)
(*                                                                            *)
(*        ortho_rec s1 s2 := elements of s1 and s2 are pairwise orthogonal    *)
(*  pairwise_orthogonal s == elements of s are pairwise orthogonal and        *)
(*                           s does not contain 0                             *)
(*       orthogonal s1 s2 == the inner product of an element of S1 and        *)
(*                           an element of S2 is 0                            *)
(*                        := ortho_rec s1 s2                                  *)
(*          orthonormal s == s is an orthonormal set of unit vectors          *)
(*                                                                            *)
(*  isometry form1 form2 tau == tau is an isometry from form1 to form2        *)
(*                              form1 and form2 are hermitian forms.          *)
(*  {in D, isometry tau, to R} == local notation for now                      *)
(*                                                                            *)
(*  orthov (V : {vspace vT}) == the space orthogonal to V                     *)
(*                                                                            *)
(* In the following definitions, we have f : {hermitian vT for eps & theta}   *)
(* with vT : vectType F (F : fieldType):                                      *)
(*        nondegenerate f == f is non-degenerated                             *)
(*        is_symplectic f == f is a symplectic bilinear form                  *)
(*        is_orthogonal f == f is an orthogonal form                          *)
(*           is_unitary f == f is a unitary form                              *)
(*                                                                            *)
(* form_of_matrix theta M U V := \tr (U *m M *m (V ^t theta))                 *)
(*       matrix_of_form f := \matrix_(i, j) form 'e_i 'e_j                    *)
(* M \is hermitianmx eps theta == same as M \is (eps, theta).-sesqui          *)
(*                           without the constraint that theta is a morphism  *)
(*                                                                            *)
(*            symmetricmx := hermitianmx _ false idfun                        *)
(*                 skewmx := hermitianmx _ true idfun                         *)
(*              hermsymmx := hermitianmx _ false conjC                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "u '``_' i"
  (at level 3, i at level 2, left associativity, format "u '``_' i").
Reserved Notation "M ^t phi"
  (at level 39, left associativity, format "M  ^t  phi").
Reserved Notation "A ^!" (at level 2, format "A ^!").
Reserved Notation "A ^_|_" (at level 8, format "A ^_|_").
Reserved Notation "A ''_|_' B" (at level 69, format "A  ''_|_'  B").
Reserved Notation "eps_theta .-sesqui"
  (at level 2, format "eps_theta .-sesqui").

Local Open Scope ring_scope.
Import GRing.Theory Order.Theory Num.Theory.

Notation "u '``_' i" := (u 0%R i) : ring_scope.

Notation "''e_' j" := (delta_mx 0 j)
 (format "''e_' j", at level 8, j at level 2) : ring_scope.

Declare Scope sesquilinear_scope.
Delimit Scope sesquilinear_scope with sesqui.
Local Open Scope sesquilinear_scope.

Notation "M ^ phi" := (map_mx phi M) : sesquilinear_scope.
Notation "M ^t phi" := ((M ^T) ^ phi) : sesquilinear_scope.

(* TODO: move? *)
Lemma eq_map_mx_id (R : nzRingType) m n (M : 'M[R]_(m, n)) (f : R -> R) :
  f =1 id -> M ^ f = M.
Proof. by move=> /eq_map_mx->; rewrite map_mx_id. Qed.

HB.mixin Record isInvolutive (R : nzRingType) (f : R -> R) :=
  { involutive_subproof : involutive f }.

(* TODO: move? *)
#[short(type="involutive_rmorphism")]
HB.structure Definition InvolutiveRMorphism (R : nzRingType) :=
  { f of @GRing.RMorphism R R f & @isInvolutive R f }.

Section InvolutiveTheory.
Variable R : nzRingType.

Let idfunK : involutive (@idfun R). Proof. by []. Qed.

HB.instance Definition _ := isInvolutive.Build _ _ idfunK.

Lemma rmorphK (f : involutive_rmorphism R) : involutive f.
Proof. by move: f => [? [? ? []]]. Qed.

End InvolutiveTheory.

Definition conjC {C : numClosedFieldType} (c : C) : C := c^*.

HB.instance Definition _ (C : numClosedFieldType) :=
  GRing.RMorphism.on (@conjC C).

Section conjC_involutive.
Variable C : numClosedFieldType.

Let conjCfun_involutive : involutive (@conjC C). Proof. exact: conjCK. Qed.

HB.instance Definition _ :=
  isInvolutive.Build _ (@conjC C) conjCfun_involutive.

End conjC_involutive.

Lemma map_mxCK {C : numClosedFieldType}  m n (A : 'M[C]_(m, n)) :
  (A ^ conjC) ^ conjC = A.
Proof. by apply/matrixP=> i j; rewrite !mxE conjCK. Qed.

(*Structure revop X Y Z (f : Y -> X -> Z) := RevOp {
  fun_of_revop :> X -> Y -> Z;
  _ : forall x, f x =1 fun_of_revop^~ x
}.
Notation "[ 'revop' revop 'of' op ]" :=
  (@RevOp _ _ _ revop op (fun _ _ => erefl))
  (at level 0, format "[ 'revop'  revop  'of'  op ]") : form_scope.*)

HB.mixin Record isBilinear (R : nzRingType) (U U' : lmodType R) (V : zmodType)
    (s : R -> V -> V) (s' : R -> V -> V) (f : U -> U' -> V) := {
  additivel_subproof : forall u', additive (f ^~ u') ;
  additiver_subproof : forall u, additive (f u) ;
  linearl_subproof : forall u', scalable_for s (f ^~ u') ;
  linearr_subproof : forall u, scalable_for s' (f u)
}.

#[short(type="bilinear")]
HB.structure Definition Bilinear (R : nzRingType) (U U' : lmodType R)
    (V : zmodType) (s : R -> V -> V) (s' : R -> V -> V) :=
  {f of isBilinear R U U' V s s' f}.

Definition bilinear_for (R : nzRingType) (U U' : lmodType R) (V : zmodType)
    (s : GRing.Scale.law R V) (s' : GRing.Scale.law R V) (f : U -> U' -> V) :=
  ((forall u', GRing.linear_for (s : R -> V -> V) (f ^~ u'))
  * (forall u, GRing.linear_for s' (f u)))%type.

HB.factory Record bilinear_isBilinear (R : nzRingType) (U U' : lmodType R)
    (V : zmodType) (s : GRing.Scale.law R V) (s' : GRing.Scale.law R V)
    (f : U -> U' -> V) := {
  bilinear_subproof : bilinear_for s s' f
}.

HB.builders Context R U U' V s s' f of bilinear_isBilinear R U U' V s s' f.
HB.instance Definition _ := isBilinear.Build R U U' V s s' f
    (fun u' => additive_linear (bilinear_subproof.1 u'))
    (fun u => additive_linear (bilinear_subproof.2 u))
    (fun u' => scalable_linear (bilinear_subproof.1 u'))
    (fun u => scalable_linear (bilinear_subproof.2 u)).
HB.end.

Module BilinearExports.

Module Bilinear.
Section bilinear.
Variables (R : nzRingType) (U U' : lmodType R) (V : zmodType) (s s' : R -> V -> V).

Local Notation bilinear f := (bilinear_for *:%R *:%R f).
Local Notation biscalar f := (bilinear_for *%R *%R f).

(* Support for right-to-left rewriting with the generic linearZ rule. *)

Notation mapUUV := (@Bilinear.type R U U' V s s').
Definition map_class := mapUUV.
Definition map_at_left (a : R) := mapUUV.
Definition map_at_right (b : R) := mapUUV.
Definition map_at_both (a b : R) := mapUUV.
Structure map_for_left a s_a :=
  MapForLeft {map_for_left_map : mapUUV; _ : s a = s_a }.
Structure map_for_right b s'_b :=
  MapForRight {map_for_right_map : mapUUV; _ : s' b = s'_b }.
Structure map_for_both a b s_a s'_b :=
  MapForBoth {map_for_both_map : mapUUV; _ : s a = s_a ; _ : s' b = s'_b }.
Definition unify_map_at_left a (f : map_at_left a) :=
  MapForLeft f (erefl (s a)).
Definition unify_map_at_right b (f : map_at_right b) :=
  MapForRight f (erefl (s' b)).
Definition unify_map_at_both a b (f : map_at_both a b) :=
   MapForBoth f (erefl (s a)) (erefl (s' b)).
Structure wrapped := Wrap {unwrap : mapUUV}.
Definition wrap (f : map_class) := Wrap f.
End bilinear.
End Bilinear.

Notation "{ 'bilinear' U -> V -> W | s & t }" :=
  (@Bilinear.type _ U%type V%type W%type s t)
    (at level 0, U at level 98, V at level 98, W at level 99,
     format "{ 'bilinear'  U  ->  V  ->  W  |  s  &  t }") : ring_scope.
Notation "{ 'bilinear' U -> V -> W | s }" :=
  ({bilinear U -> V -> W | s.1 & s.2})
    (at level 0, U at level 98, V at level 98, W at level 99,
     format "{ 'bilinear'  U  ->  V  ->  W  |  s }") : ring_scope.
Notation "{ 'bilinear' U -> V -> W }" := {bilinear U -> V -> W  | *:%R & *:%R}
  (at level 0, U at level 98, V at level 98, W at level 99,
   format "{ 'bilinear'  U  ->  V  -> W }") : ring_scope.
Notation "{ 'biscalar' U }" := {bilinear U%type -> U%type -> _ | *%R & *%R}
  (at level 0, format "{ 'biscalar'  U }") : ring_scope.
End BilinearExports.

Export BilinearExports.

#[non_forgetful_inheritance]
HB.instance Definition _ (R : nzRingType) (U U' : lmodType R) (V : zmodType)
    (s : R -> V -> V) (s' : R -> V -> V)
  (f : {bilinear U -> U' -> V | s & s'}) (u : U)
  := @GRing.isAdditive.Build U' V (f u) (@additiver_subproof _ _ _ _ _ _ f u).

#[non_forgetful_inheritance]
HB.instance Definition _ (R : nzRingType) (U U' : lmodType R) (V : zmodType)
    (s : R -> V -> V) (s' : R -> V -> V) (f : @bilinear R U U' V s s') (u : U)
  := @GRing.isScalable.Build _ _ _ _ (f u) (@linearr_subproof _ _ _ _ _ _ f u).

Section applyr.
Variables (R : nzRingType) (U U' : lmodType R) (V : zmodType)
  (s s' : R -> V -> V).

Definition applyr_head t (f : U -> U' -> V) u v := let: tt := t in f v u.

End applyr.

Notation applyr := (applyr_head tt).

Coercion Bilinear.map_for_left_map : Bilinear.map_for_left >-> Bilinear.type.
Coercion Bilinear.map_for_right_map : Bilinear.map_for_right >-> Bilinear.type.
Coercion Bilinear.map_for_both_map : Bilinear.map_for_both >-> Bilinear.type.
Coercion Bilinear.unify_map_at_left : Bilinear.map_at_left >-> Bilinear.map_for_left.
Coercion Bilinear.unify_map_at_right : Bilinear.map_at_right >-> Bilinear.map_for_right.
Coercion Bilinear.unify_map_at_both : Bilinear.map_at_both >-> Bilinear.map_for_both.
Canonical Bilinear.unify_map_at_left.
Canonical Bilinear.unify_map_at_right.
Canonical Bilinear.unify_map_at_both.
Coercion Bilinear.unwrap : Bilinear.wrapped >-> Bilinear.type.
Coercion Bilinear.wrap : Bilinear.map_class >-> Bilinear.wrapped.
Canonical Bilinear.wrap.

Section BilinearTheory.
Variable R : nzRingType.

Section GenericProperties.
Variables (U U' : lmodType R) (V : zmodType) (s : R -> V -> V) (s' : R -> V -> V).
Variable f : {bilinear U -> U' -> V | s & s'}.

Section GenericPropertiesr.
Variable z : U.

#[local, non_forgetful_inheritance, warning="-HB.no-new-instance"]
HB.instance Definition _ :=
  GRing.isAdditive.Build _ _ (f z) (@additiver_subproof _ _ _ _ _ _ f z).
#[local, non_forgetful_inheritance]
HB.instance Definition _ :=
  GRing.isScalable.Build _ _ _ _ (f z) (@linearr_subproof _ _ _ _ _ _ f z).

Lemma linear0r : f z 0 = 0. Proof. by rewrite raddf0. Qed.
Lemma linearNr : {morph f z : x / - x}. Proof. exact: raddfN. Qed.
Lemma linearDr : {morph f z : x y / x + y}. Proof. exact: raddfD. Qed.
Lemma linearBr : {morph f z : x y / x - y}. Proof. exact: raddfB. Qed.
Lemma linearMnr n : {morph f z : x / x *+ n}. Proof. exact: raddfMn. Qed.
Lemma linearMNnr n : {morph f z : x / x *- n}. Proof. exact: raddfMNn. Qed.
Lemma linear_sumr I r (P : pred I) E :
  f z (\sum_(i <- r | P i) E i) = \sum_(i <- r | P i) f z (E i).
Proof. exact: raddf_sum. Qed.

Lemma linearZr_LR : scalable_for s' (f z). Proof. exact: linearZ_LR. Qed.
Lemma linearPr a : {morph f z : u v / a *: u + v >-> s' a u + v}.
Proof. exact: linearP. Qed.

End GenericPropertiesr.

Lemma applyrE x : applyr f x =1 f^~ x. Proof. by []. Qed.

Section GenericPropertiesl.
Variable z : U'.

HB.instance Definition _ :=
  GRing.isAdditive.Build _ _ (applyr f z) (@additivel_subproof _ _ _ _ _ _ f z).
HB.instance Definition _ :=
  GRing.isScalable.Build _ _ _ _ (applyr f z) (@linearl_subproof _ _ _ _ _ _ f z).

Lemma linear0l : f 0 z = 0. Proof. by rewrite -applyrE raddf0. Qed.
Lemma linearNl : {morph f^~ z : x / - x}.
Proof. by move=> ?; rewrite -applyrE raddfN. Qed.
Lemma linearDl : {morph f^~ z : x y / x + y}.
Proof. by move=> ? ?; rewrite -applyrE raddfD. Qed.
Lemma linearBl : {morph f^~ z : x y / x - y}.
Proof. by move=> ? ?; rewrite -applyrE raddfB. Qed.
Lemma linearMnl n : {morph f^~ z : x / x *+ n}.
Proof. by move=> ?; rewrite -applyrE raddfMn. Qed.
Lemma linearMNnl n : {morph f^~ z : x / x *- n}.
Proof. by move=> ?; rewrite -applyrE raddfMNn. Qed.
Lemma linear_sumlz I r (P : pred I) E :
  f (\sum_(i <- r | P i) E i) z = \sum_(i <- r | P i) f (E i) z.
Proof. by rewrite -applyrE raddf_sum. Qed.

Lemma linearZl_LR : scalable_for s (f ^~ z).
Proof. by move=> ? ?; rewrite -applyrE linearZ_LR. Qed.
Lemma linearPl a : {morph f^~ z : u v / a *: u + v >-> s a u + v}.
Proof. by move=> ? ?; rewrite -applyrE linearP. Qed.

End GenericPropertiesl.

End GenericProperties.

Section BidirectionalLinearZ.
Variables (U U' : lmodType R) (V : zmodType) (s s' : R -> V -> V).
Variables (S : nzRingType) (h : GRing.Scale.law S V) (h' : GRing.Scale.law S V).

Lemma linearZl z (c : S) (a : R) (h_c := h c)
    (f : Bilinear.map_for_left U U' s s' a h_c) u :
  f (a *: u) z = h_c (Bilinear.wrap f u z).
Proof. by rewrite linearZl_LR; case: f => f /= ->. Qed.

Lemma linearZr z c' b (h'_c' := h' c')
    (f : Bilinear.map_for_right U U' s s' b h'_c') u :
  f z (b *: u) = h'_c' (Bilinear.wrap f z u).
Proof. by rewrite linearZr_LR; case: f => f /= ->. Qed.

Lemma linearZlr c c' a b (h_c := h c) (h'_c' := h' c')
    (f : Bilinear.map_for_both U U' s s' a b h_c h'_c') u v :
  f (a *: u) (b *: v) = h_c (h'_c' (Bilinear.wrap f u v)).
Proof. by rewrite linearZl_LR linearZ_LR; case: f => f /= -> ->. Qed.

Lemma linearZrl c c' a b (h_c := h c) (h'_c' := h' c')
    (f : Bilinear.map_for_both U U' s s' a b h_c h'_c') u v :
  f (a *: u) (b *: v) = h'_c' (h_c (Bilinear.wrap f u v)).
Proof. by rewrite linearZ_LR/= linearZl_LR; case: f => f /= -> ->. Qed.

End BidirectionalLinearZ.

End BilinearTheory.

(* TODO
Canonical rev_mulmx (R : nzRingType) m n p := [revop mulmxr of @mulmx R m n p].
*)

(*Canonical mulmx_bilinear (R : comNzRingType) m n p := [bilinear of @mulmx R m n p].*)
Lemma mulmx_is_bilinear (R : comNzRingType) m n p : bilinear_for
  (GRing.Scale.Law.clone _ _ *:%R _) (GRing.Scale.Law.clone _ _ *:%R _)
  (@mulmx R m n p).
Proof.
split=> [u'|u] a x y /=.
- by rewrite mulmxDl scalemxAl.
- by rewrite mulmxDr scalemxAr.
Qed.

HB.instance Definition _ (R : comNzRingType) m n p := bilinear_isBilinear.Build R
  [the lmodType R of 'M[R]_(m, n)] [the lmodType R of 'M[R]_(n, p)]
  [the zmodType of 'M[R]_(m, p)] _ _ (@mulmx R m n p)
  (mulmx_is_bilinear R m n p).

Section BilinearForms.
Variables (R : fieldType) (theta : {rmorphism R -> R}).
Variables (n : nat) (M : 'M[R]_n).
Implicit Types (a b : R) (u v : 'rV[R]_n) (N P Q : 'M[R]_n).

Definition form u v := (u *m M *m (v ^t theta)) 0 0.

Local Notation "''[' u , v ]" := (form u%R v%R) : ring_scope.
Local Notation "''[' u ]" := '[u, u] : ring_scope.

Lemma form0l u : '[0, u] = 0. Proof. by rewrite /form !mul0mx mxE. Qed.

Lemma form0r u : '[u, 0] = 0.
Proof. by rewrite /form trmx0 map_mx0 mulmx0 mxE. Qed.

Lemma formDl u v w : '[u + v, w] = '[u, w] + '[v, w].
Proof. by rewrite /form !mulmxDl mxE. Qed.

Lemma formDr u v w : '[u, v + w] = '[u, v] + '[u, w].
Proof. by rewrite /form linearD !map_mxD !mulmxDr mxE. Qed.

Lemma formZr a u v : '[u, a *: v] = theta a * '[u, v].
Proof. by rewrite /form !(linearZ, map_mxZ) /= mxE. Qed.

Lemma formZl a u v : '[a *: u, v] = a * '[u, v].
Proof.
by do !rewrite /form  -[_ *: _ *m _]/(mulmxr _ _) linearZ /=; rewrite mxE.
Qed.

Lemma formNl u v : '[- u, v] = - '[u, v].
Proof. by rewrite -scaleN1r formZl mulN1r. Qed.

Lemma formNr u v : '[u, - v] = - '[u, v].
Proof. by rewrite -scaleN1r formZr rmorphN1 mulN1r. Qed.

Lemma formee i j : '['e_i, 'e_j] = M i j.
Proof.
rewrite /form -rowE -map_trmx map_delta_mx -[M in LHS]trmxK.
by rewrite -tr_col -trmx_mul -rowE !mxE.
Qed.

Lemma form0_eq0 : M = 0 -> forall u v, '[u, v] = 0.
Proof. by rewrite/form=> -> u v; rewrite mulmx0 mul0mx mxE. Qed.

End BilinearForms.

HB.mixin Record isHermitianSesquilinear (R : nzRingType) (U : lmodType R)
    (eps : bool) (theta : R -> R) (f : U -> U -> R) := {
  hermitian_subproof : forall x y : U, f x y = (-1) ^+ eps * theta (f y x)
}.

HB.structure Definition Hermitian (R : nzRingType) (U : lmodType R)
    (eps : bool) (theta : R -> R) :=
  {f of @Bilinear R U U _ ( *%R ) (theta \; *%R) f &
        @isHermitianSesquilinear R U eps theta f}.

Notation "{ 'hermitian' U 'for' eps & theta }" := (@Hermitian.type _ U eps theta)
  (at level 0, format "{ 'hermitian'  U  'for'  eps  &  theta }") : ring_scope.

(* duplicate to trick HB *)
#[non_forgetful_inheritance]
HB.instance Definition _ (R : nzRingType) (U : lmodType R)
    (eps : bool) (theta : R -> R) (f : {hermitian U for eps & theta}) (u : U) :=
  @GRing.isAdditive.Build _ _ (f u) (@additiver_subproof _ _ _ _ _ _ f u).

#[non_forgetful_inheritance]
HB.instance Definition _ (R : nzRingType) (U : lmodType R)
    (eps : bool) (theta : R -> R) (f : {hermitian U for eps & theta}) (u : U) :=
  @GRing.isScalable.Build _ _ _ _ (f u) (@linearr_subproof _ _ _ _ _ _ f u).

(*Variables (R : nzRingType) (U : lmodType R) (eps : bool) (theta : R -> R).
Implicit Types phU : phant U.

Local Coercion GRing.Scale.op : GRing.Scale.law >-> Funclass.
Definition axiom (f : U -> U -> R) :=
  forall x y : U, f x y = (-1) ^+ eps * theta (f y x).

Record class_of (f : U -> U -> R) : Prop := Class {
  base : Bilinear.class_of ( *%R) (theta \; *%R) f;
  mixin : axiom f
}.*)

(*Canonical additiver (u : U) := Additive (base class u).
Canonical linearr (u : U) := Linear (base class u).
Canonical additivel (u' : U) := @GRing.Additive.Pack _ _ (Phant (U -> R))
  (applyr cF u') (Bilinear.basel (base class) u').
Canonical linearl (u' : U) := @GRing.Linear.Pack _ _ _ _ (Phant (U -> R))
  (applyr cF u') (Bilinear.basel (base class) u').
Canonical bilinear := @Bilinear.Pack _ _ _ _ _ _ (Phant (U -> U -> R)) cF (base class).*)

(*Module Exports.
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
Include Hermitian.Exports.*)

Definition orthomx {R : fieldType} (theta : R -> R) n m M (B : 'M_(m, n)) : 'M_n :=
  kermx (M *m (B ^t theta)).

Section Sesquilinear.
Variables (R : fieldType) (n : nat).
Implicit Types (a b : R) (u v : 'rV[R]_n) (N P Q : 'M[R]_n).

Section Def.
Variable eps_theta : bool * {rmorphism R -> R}.

Definition sesqui :=
  [qualify M : 'M_n | M == ((-1) ^+ eps_theta.1) *: M ^t eps_theta.2].
Fact sesqui_key : pred_key sesqui. Proof. by []. Qed.

Canonical sesqui_keyed := KeyedQualifier sesqui_key.

End Def.

Local Notation "eps_theta .-sesqui" := (sesqui eps_theta).

Variables (eps : bool) (theta : {rmorphism R -> R}) (M : 'M[R]_n).
Local Notation "''[' u , v ]" := (form theta M u%R v%R) : ring_scope.
Local Notation "''[' u ]" := '[u, u] : ring_scope.

Lemma sesquiE : (M \is (eps, theta).-sesqui) = (M == (-1) ^+ eps *: M ^t theta).
Proof. by rewrite qualifE. Qed.

Lemma sesquiP : reflect (M = (-1) ^+ eps *: M ^t theta)
                        (M \is (eps, theta).-sesqui).
Proof. by rewrite sesquiE; exact/eqP. Qed.

Hypotheses (thetaK : involutive theta) (M_sesqui : M \is (eps, theta).-sesqui).

Lemma trmx_sesqui : M^T = (-1) ^+ eps *: M ^ theta.
Proof.
rewrite [in LHS](sesquiP _) // -mul_scalar_mx trmx_mul.
by rewrite tr_scalar_mx mul_mx_scalar map_trmx trmxK.
Qed.

Lemma maptrmx_sesqui : M^t theta = (-1) ^+ eps *: M.
Proof.
by rewrite trmx_sesqui map_mxZ rmorph_sign -map_mx_comp eq_map_mx_id.
Qed.

Lemma formC u v : '[u, v] = (-1) ^+ eps * theta '[v, u].
Proof.
rewrite /form [M in LHS](sesquiP _) // -mulmxA !mxE rmorph_sum mulr_sumr.
apply: eq_bigr => /= i _; rewrite !(mxE, mulr_sumr, mulr_suml, rmorph_sum).
apply: eq_bigr => /= j _; rewrite !mxE !rmorphM  mulrCA -!mulrA.
by congr (_ * _); rewrite mulrA mulrC /= thetaK.
Qed.

Lemma form_eq0C u v : ('[u, v] == 0) = ('[v, u] == 0).
Proof. by rewrite formC mulf_eq0 signr_eq0 /= fmorph_eq0. Qed.

Definition ortho m (B : 'M_(m, n)) := orthomx theta M B.
Local Notation "B ^_|_" := (ortho B) : ring_scope.
Local Notation "A '_|_ B" := (A%MS <= B^_|_)%MS : ring_scope.

Lemma normalE u v : (u '_|_ v) = ('[u, v] == 0).
Proof.
by rewrite (sameP sub_kermxP eqP) mulmxA [_ *m _^t _]mx11_scalar fmorph_eq0.
Qed.

Lemma form_eq0P {u v} : reflect ('[u, v] = 0) (u '_|_ v).
Proof. by rewrite normalE; apply/eqP. Qed.

Lemma normalP p q (A : 'M_(p, n)) (B :'M_(q, n)) :
  reflect (forall (u v : 'rV_n), (u <= A)%MS -> (v <= B)%MS -> u '_|_ v)
          (A '_|_ B).
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

Lemma normalC p q (A : 'M_(p, n)) (B : 'M_(q, n)) : (A '_|_ B) = (B '_|_ A).
Proof.
gen have nC : p q A B / A '_|_ B -> B '_|_ A; last by apply/idP/idP; apply/nC.
move=> AnB; apply/normalP => u v ? ?; rewrite normalE.
rewrite formC mulf_eq0 ?fmorph_eq0 ?signr_eq0 /=.
by rewrite -normalE (normalP _ _ AnB).
Qed.

Lemma normal_ortho_mx p (A : 'M_(p, n)) : ((A^_|_) '_|_ A).
Proof. by []. Qed.

Lemma normal_mx_ortho p (A : 'M_(p, n)) : (A '_|_ (A^_|_)).
Proof. by rewrite normalC. Qed.

Lemma rank_normal u : (\rank (u ^_|_) >= n.-1)%N.
Proof.
rewrite mxrank_ker -subn1 leq_sub2l //.
by rewrite (leq_trans (mxrankM_maxr  _ _)) // rank_leq_col.
Qed.

Definition rad := 1%:M^_|_.

Lemma rad_ker : rad = kermx M.
Proof. by rewrite /rad /ortho /orthomx trmx1 map_mx1 mulmx1. Qed.

(* Pythagoras *)
Theorem formDd u v : u '_|_ v -> '[u + v] = '[u] + '[v].
Proof.
move=> uNv; rewrite formDl !formDr ['[v, u]]formC.
by rewrite ['[u, v]](form_eq0P _) // rmorph0 mulr0 addr0 add0r.
Qed.

Lemma formZ a u : '[a *: u]= (a * theta a) * '[u].
Proof. by rewrite formZl formZr mulrA. Qed.

Lemma formN u : '[- u] = '[u].
Proof. by rewrite formNr formNl opprK. Qed.

Lemma form_sign m u : '[(-1) ^+ m *: u] = '[u].
Proof. by rewrite -signr_odd scaler_sign; case: odd; rewrite ?formN. Qed.

Lemma formD u v : let d := '[u, v] in
  '[u + v] = '[u] + '[v] + (d + (-1) ^+ eps * theta d).
Proof. by rewrite formDl !formDr ['[v, _]]formC [_ + '[v]]addrC addrACA. Qed.

Lemma formB u v : let d := '[u, v] in
  '[u - v] = '[u] + '[v] - (d + (-1) ^+ eps * theta d).
Proof. by rewrite formD formN !formNr rmorphN mulrN -opprD. Qed.

Lemma formBd u v : u '_|_ v -> '[u - v] = '[u] + '[v].
Proof.
by move=> uTv; rewrite formDd ?formN // normalE formNr oppr_eq0 -normalE.
Qed.

(* Lemma formJ u v : '[u ^ theta, v ^ theta] = (-1) ^+ eps * theta '[u, v]. *)
(* Proof. *)
(* rewrite {1}/form -map_trmx -map_mx_comp (@eq_map_mx _ _ _ _ _ id) ?map_mx_id //. *)
(* set x := (_ *m _); have -> : x 0 0 = theta ((x^t theta) 0 0) by rewrite !mxE. *)
(* rewrite !trmx_mul trmxK map_trmx mulmxA !map_mxM. *)
(* rewrite maptrmx_sesqui -!scalemxAr -scalemxAl mxE rmorphM rmorph_sign. *)

(* Lemma formJ u : '[u ^ theta] = (-1) ^+ eps * '[u]. *)
(* Proof.  *)
(* rewrite {1}/form -map_trmx -map_mx_comp (@eq_map_mx _ _ _ _ _ id) ?map_mx_id //. *)
(* set x := (_ *m _); have -> : x 0 0 = theta ((x^t theta) 0 0) by rewrite !mxE. *)
(* rewrite !trmx_mul trmxK map_trmx mulmxA !map_mxM. *)
(* rewrite maptrmx_sesqui -!scalemxAr -scalemxAl mxE rmorphM rmorph_sign. *)
(* rewrite !map_mxM. *)
(* rewrite -map_mx_comp eq_map_mx_id //. *)
(*  !linearZr_LR /=. linearZ. *)
(*  linearZl. *)
(* rewrite trmx_sesqui. *)


(* rewrite mapmx. *)
(* rewrite map *)
(* apply/matrixP.  *)

(* rewrite formC. *)
(* Proof. by rewrite cfdot_conjC geC0_conj // cfnorm_ge0. Qed. *)

(* Lemma cfCauchySchwarz u v : *)
(*   `|'[u, v]| ^+ 2 <= '[u] * '[v] ?= iff ~~ free (u :: v). *)
(* Proof. *)
(* rewrite free_cons span_seq1 seq1_free -negb_or negbK orbC. *)
(* have [-> | nz_v] /= := altP (v =P 0). *)
(*   by apply/lerifP; rewrite !cfdot0r normCK mul0r mulr0. *)
(* without loss ou: u / '[u, v] = 0. *)
(*   move=> IHo; pose a := '[u, v] / '[v]; pose u1 := u - a *: v. *)
(*   have ou: '[u1, v] = 0. *)
(*     by rewrite cfdotBl cfdotZl divfK ?cfnorm_eq0 ?subrr. *)
(*   rewrite (canRL (subrK _) (erefl u1)) rpredDr ?rpredZ ?memv_line //. *)
(*   rewrite cfdotDl ou add0r cfdotZl normrM (ger0_norm (cfnorm_ge0 _)). *)
(*   rewrite exprMn mulrA -cfnormZ cfnormDd; last by rewrite cfdotZr ou mulr0. *)
(*   by have:= IHo _ ou; rewrite mulrDl -lerif_subLR subrr ou normCK mul0r. *)
(* rewrite ou normCK mul0r; split; first by rewrite mulr_ge0 ?cfnorm_ge0. *)
(* rewrite eq_sym mulf_eq0 orbC cfnorm_eq0 (negPf nz_v) /=. *)
(* apply/idP/idP=> [|/vlineP[a {2}->]]; last by rewrite cfdotZr ou mulr0. *)
(* by rewrite cfnorm_eq0 => /eqP->; apply: rpred0. *)
(* Qed. *)

End Sesquilinear.
Notation "eps_theta .-sesqui" := (sesqui _ eps_theta) : ring_scope.

Notation symmetric_form := (false, idfun).-sesqui.
Notation skew := (true, idfun).-sesqui.
Notation hermitian := (false, @Num.conj_op _).-sesqui.

HB.mixin Record isDotProduct (R : numDomainType) (U : lmodType R)
  (op : U -> U -> R) := { neq0_dnorm_gt0 : forall u, u != 0 -> 0 < op u u }.

HB.structure Definition Dot (R : numDomainType) (U : lmodType R)
    (theta : R -> R) :=
  {op of isDotProduct R U op & @Hermitian R U false theta op}.

Notation "{ 'dot' U 'for' theta }" := (@Dot.type _ U theta)
  (at level 0, format "{ 'dot'  U  'for'  theta }") : ring_scope.

(* duplicate to trick HB *)
#[non_forgetful_inheritance]
HB.instance Definition _ (R : numDomainType) (U : lmodType R)
    (theta : R -> R) (f : {dot U for theta}) (u : U) :=
  @GRing.isAdditive.Build _ _ (f u) (@additiver_subproof _ _ _ _ _ _ f u).

#[non_forgetful_inheritance]
HB.instance Definition _ (R : numDomainType) (U : lmodType R)
    (theta : R -> R) (f : {dot U for theta}) (u : U) :=
  @GRing.isScalable.Build _ _ _ _ (f u) (@linearr_subproof _ _ _ _ _ _ f u).

(*Notation "{ 'dot' U 'for' theta }" := (map theta (Phant U))
  (at level 0, format "{ 'dot'  U  'for'  theta }") : ring_scope.
Coercion base : class_of >-> Hermitian.class_of.
Coercion apply : map >-> Funclass.
Notation "[ 'dot' 'of' f 'as' g ]" := (@clone _ _ _ _ _ f g _ idfun idfun)
  (at level 0, format "[ 'dot'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'dot' 'of' f ]" := (@clone _ _ _ _ _ f f _ idfun idfun)
  (at level 0, format "[ 'dot'  'of'  f ]") : form_scope.
Notation Dot fM := (pack fM idfun).
Notation is_dot := Dot.axiom.*)

Notation "{ 'symmetric' U }" := ({hermitian U for false & idfun})
  (at level 0, format "{ 'symmetric'  U }") : ring_scope.
Notation "{ 'skew_symmetric' U }" := ({hermitian U for true & idfun})
  (at level 0, format "{ 'skew_symmetric'  U }") : ring_scope.
Notation "{ 'hermitian_sym' U 'for' theta }" := ({hermitian U for false & theta})
  (at level 0, format "{ 'hermitian_sym'  U  'for'  theta }") : ring_scope.

Definition is_skew (R : nzRingType) (eps : bool) (theta : R -> R)
  (U : lmodType R) (form : {hermitian U for eps & theta}) :=
  (eps = true) /\ (theta =1 id).
Definition is_sym (R : nzRingType) (eps : bool) (theta : R -> R)
  (U : lmodType R) (form : {hermitian U for eps & theta}) :=
  (eps = false) /\ (theta =1 id).
Definition is_hermsym  (R : nzRingType) (eps : bool) (theta : R -> R)
  (U : lmodType R) (form : {hermitian U for eps & theta}) :=
  (eps = false).

Section HermitianModuleTheory.
Variables (R : nzRingType) (eps : bool) (theta : {rmorphism R -> R}).
Variables (U : lmodType R) (form : {hermitian U for eps & theta}).

Local Notation "''[' u , v ]" := (form u%R v%R) : ring_scope.
Local Notation "''[' u ]" := '[u, u]%R : ring_scope.

Lemma hermC u v : '[u, v] = (-1) ^+ eps * theta '[v, u].
Proof. by move: form => [? [[? ? ? ?] []]] /=. Qed.

Lemma hnormN u : '[- u] = '[u].
Proof. by rewrite linearNl linearNr opprK. Qed.

Lemma hnorm_sign n u : '[(-1) ^+ n *: u] = '[u].
Proof. by rewrite -signr_odd scaler_sign; case: (odd n); rewrite ?hnormN. Qed.

Lemma hnormD u v :
  let d := '[u, v] in '[u + v] = '[u] + '[v] + (d + (-1) ^+ eps * theta d).
Proof. by rewrite /= addrAC -hermC linearDl 2!linearDr !addrA. Qed.

Lemma hnormB u v :
  let d := '[u, v] in '[u - v] = '[u] + '[v] - (d + (-1) ^+ eps * theta d).
Proof.
by rewrite /= hnormD hnormN linearNr addrA rmorphN mulrN opprD addrA.
Qed.

Lemma hnormDd u v : '[u, v] = 0 -> '[u + v] = '[u] + '[v].
Proof. by move=> ouv; rewrite hnormD ouv rmorph0 mulr0 !addr0. Qed.

Lemma hnormBd u v : '[u, v] = 0 -> '[u - v] = '[u] + '[v].
Proof.
by move=> ouv; rewrite hnormDd ?hnormN// linearNr [X in - X]ouv oppr0.
Qed.

Local Notation "u '_|_ v" := ('[u, v] == 0) : ring_scope.

Definition ortho_rec (s1 s2 : seq U) :=
  all [pred u | all [pred v | u '_|_ v] s2] s1.

Fixpoint pair_ortho_rec (s : seq U) :=
  if s is v :: s' then ortho_rec [:: v] s' && pair_ortho_rec s' else true.

(* We exclude 0 from pairwise orthogonal sets. *)
Definition pairwise_orthogonal s := (0 \notin s) && pair_ortho_rec s.

Definition orthogonal s1 s2 := (@ortho_rec s1 s2).
Arguments orthogonal : simpl never.

Lemma orthogonal_cons u us vs :
  orthogonal (u :: us) vs = orthogonal [:: u] vs && orthogonal us vs.
Proof. by rewrite /orthogonal /= andbT. Qed.

Definition orthonormal s := all [pred v | '[v] == 1] s && pair_ortho_rec s.

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
Arguments orthogonal {R eps theta U} form s1 s2.
Arguments pairwise_orthogonal {R eps theta U} form s.
Arguments orthonormal {R eps theta U} form s.

Section HermitianIsometry.
Variables (R : nzRingType) (eps : bool) (theta : {rmorphism R -> R}).
Variables (U1 U2 : lmodType R) (form1 : {hermitian U1 for eps & theta})
          (form2 : {hermitian U2 for eps & theta}).

Local Notation "''[' u , v ]_1" := (form1 u%R v%R) : ring_scope.
Local Notation "''[' u , v ]_2" := (form2 u%R v%R) : ring_scope.
Local Notation "''[' u ]_1" := (form1 u%R u%R)  : ring_scope.
Local Notation "''[' u ]_2" := (form2 u%R u%R): ring_scope.

Definition isometry tau := forall u v, form1 (tau u) (tau v) = form2 u%R v%R.

Definition isometry_from_to mD tau mR :=
  prop_in2 mD (inPhantom (isometry tau)) /\
  prop_in1 mD (inPhantom (forall u, in_mem (tau u) mR)).

Local Notation "{ 'in' D , 'isometry' tau , 'to' R }" :=
    (isometry_from_to (mem D) tau (mem R))
  (at level 0, format "{ 'in'  D ,  'isometry'  tau ,  'to'  R }")
     : type_scope.

End HermitianIsometry.

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
Variables (vT : vectType F) (form : {hermitian vT for eps & theta}).
Let n := \dim {:vT}.
Implicit Types (u v : vT) (U V : {vspace vT}).

Local Notation "''[' u , v ]" := (form u%R v%R) : ring_scope.
Local Notation "''[' u ]" := '[u, u]%R : ring_scope.

Let alpha v := (linfun (applyr form v : vT -> F^o)).

Definition orthov V := (\bigcap_(i < \dim V) lker (alpha (vbasis V)`_i))%VS.

Local Notation "U '_|_ V" := (U <= orthov V)%VS : vspace_scope.

Lemma mem_orthovPn V u : reflect (exists2 v, v \in V & '[u, v] != 0) (u \notin orthov V).
Proof.
apply: (iffP idP) => [u_orthovV|[v /coord_vbasis-> uvNorthov]]; last first.
  apply/subv_bigcapP => uP.
  rewrite linear_sumr big1 ?eqxx//= in uvNorthov.
  move=> i _; have := uP i isT.
  by rewrite -memvE memv_ker lfunE/= linearZr/= => /eqP/= ->; rewrite mulr0.
suff /existsP [i ui_neq0] : [exists i : 'I_(\dim V), '[u, (vbasis V)`_i] != 0].
  by exists (vbasis V)`_i => //; rewrite vbasis_mem ?mem_nth ?size_tuple.
apply: contraNT u_orthovV; rewrite negb_exists => /forallP ui_eq0.
apply/subv_bigcapP => i _.
by rewrite -memvE memv_ker lfunE /= -[_ == _]negbK.
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

Lemma orthovP U V : reflect {in U & V, forall u v, '[u, v] = 0} (U '_|_ V)%VS.
Proof.
apply: (iffP subvP); last by move=> H ??; apply/mem_orthovP=> ??; apply: H.
by move=> /(_ _ _)/mem_orthovP; move=> H ????; apply: H.
Qed.

Lemma orthov_sym U V : (U '_|_ V)%VS = (V '_|_ U)%VS.
Proof. by apply/orthovP/orthovP => eq0 ????; apply/eqP; rewrite herm_eq0C eq0. Qed.

Lemma mem_orthov1 v u : (u \in orthov <[v]>) = ('[u, v] == 0).
Proof. by rewrite orthov1E memv_ker lfunE. Qed.

Lemma orthov11 u v : (<[u]> '_|_ <[v]>)%VS = ('[u, v] == 0).
Proof. exact: mem_orthov1. Qed.

Lemma mem_orthov1_sym v u : (u \in orthov <[v]>) = (v \in orthov <[u]>).
Proof. exact: orthov_sym. Qed.

Lemma orthov0 : orthov 0 = fullv.
Proof.
apply/eqP; rewrite eqEsubv subvf.
apply/subvP => x _; rewrite mem_orthov1.
by rewrite linear0r.
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
rewrite -[1%N as X in (_ <= X)%N](dimvf [the vectType F of F^o]) dimvS ?subvf//=.
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

Lemma orthogonalE us vs : (orthogonal form us vs) = (<<us>> '_|_ <<vs>>)%VS.
Proof.
apply/orthogonalP/orthovP => uvsP u v; last first.
  by move=> uus vvs; rewrite uvsP // memv_span.
rewrite -[us]in_tupleE -[vs]in_tupleE => /coord_span-> /coord_span->.
rewrite linear_sumr big1 //= => i _.
rewrite linear_sumlz big1 //= => j _.
by rewrite linearZlr/= uvsP ?mulr0// mem_nth.
Qed.

Lemma orthovE U V : (U '_|_ V)%VS = orthogonal form (vbasis U) (vbasis V).
Proof. by rewrite orthogonalE !(span_basis (vbasisP _)). Qed.

Notation radv := (orthov fullv).

Lemma orthoDv U V W : (U + V '_|_ W)%VS = (U '_|_ W)%VS && (V '_|_ W)%VS.
Proof. by rewrite subv_add. Qed.

Lemma orthovD U V W : (U '_|_ V + W)%VS = (U '_|_ V)%VS && (U '_|_ W)%VS.
Proof. by rewrite ![(U '_|_ _)%VS]orthov_sym orthoDv. Qed.

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

Lemma dnorm_geiff0 u : 0 <= '[u] ?= iff (u == 0).
Proof.
by apply/leifP; have [->|uN0] := altP eqP; rewrite ?linear0r ?neq0_dnorm_gt0.
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
Proof. by rewrite linearZl_LR linearZr_LR/= mulrA normCK. Qed.

Lemma dnormD u v : let d := '[u, v] in '[u + v] = '[u] + '[v] + (d + d^*).
Proof. by rewrite hnormD mul1r. Qed.

Lemma dnormB u v : let d := '[u, v] in '[u - v] = '[u] + '[v] - (d + d^*).
Proof. by rewrite hnormB mul1r. Qed.

End DotVectTheory.
#[global]
Hint Extern 0 (is_true (0 <= Dot.sort _ _ _
  (* NB: This Hint is assuming ^*, a more precise pattern would be welcome *)))
  => apply: dnorm_ge0 : core.

Section HermitianTheory.
Variables (C : numClosedFieldType) (eps : bool) (theta : {rmorphism C -> C}).
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
by move: (opS psi Spsi) => /= /eqP ->; rewrite rmorph0 mulr0.
Qed.

Lemma pairwise_orthogonal_cat R S :
  pairwise_orthogonal form (R ++ S) =
  [&& pairwise_orthogonal form R, pairwise_orthogonal form  S & orthogonal form R S].
Proof.
rewrite /pairwise_orthogonal mem_cat negb_or -!andbA; do !bool_congr.
elim: R => [|phi R /= ->]; rewrite ?andbT// all_cat -!andbA /=.
by do !bool_congr.
Qed.

Lemma orthonormal_cat R S :
  orthonormal form (R ++ S) =
  [&& orthonormal form R, orthonormal form S & orthogonal form R S].
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
Variable C : numClosedFieldType.
Variables (U : vectType C) (form : {dot U for conjC}).

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

Lemma orthogonal_free S : pairwise_orthogonal form S -> free S.
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
  by apply/leifP; rewrite /= !linear0r normCK mul0r mulr0.
without loss ou: u / '[u, v] = 0.
  move=> IHo; pose a := '[u, v] / '[v]; pose u1 := u - a *: v.
  have ou: '[u1, v] = 0.
    rewrite linearBl/=.
    rewrite linearZl_LR.
    by rewrite divfK ?dnorm_eq0 ?subrr.
  rewrite (canRL (subrK _) (erefl u1)) rpredDr ?rpredZ ?memv_line //.
  rewrite linearDl /= ou add0r.
  rewrite linearZl_LR/= normrM (ger0_norm (dnorm_ge0 _ _)).
  rewrite exprMn mulrA -dnormZ hnormDd/=; last by rewrite linearZr_LR/= ou mulr0.
  have:= IHo _ ou.
  by rewrite mulrDl -leifBLR subrr ou normCK mul0r.
rewrite ou normCK mul0r; split; first by rewrite mulr_ge0.
rewrite eq_sym mulf_eq0 orbC dnorm_eq0 (negPf nz_v) /=.
apply/idP/idP=> [|/vlineP[a {2}->]]; last by rewrite linearZr_LR/= ou mulr0.
by rewrite dnorm_eq0 => /eqP->; apply: rpred0.
Qed.

Lemma CauchySchwarz_sqrt u v :
  `|'[u, v]| <= sqrtC '[u] * sqrtC '[v] ?= iff ~~ free [:: u; v].
Proof.
rewrite -(sqrCK (normr_ge0 _)) -sqrtCM ?nnegrE//.
rewrite (mono_in_leif (@ler_sqrtC _)) 1?rpredM//= ?nnegrE//=.
exact: CauchySchwarz.
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
rewrite -(mono_in_leif ler_sqr) ?rpredD ?nnegrE ?sqrtC_ge0//.
rewrite andbC sqrrD !sqrtCK addrAC dnormD (mono_leif (lerD2l _))/=.
rewrite -mulr_natr -[_ + _](divfK (negbT (pnatr_eq0 C 2))) -/('Re _).
rewrite (mono_leif (ler_pM2r _)) ?ltr0n//.
have := leif_trans (leif_Re_Creal '[u, v]) (CauchySchwarz_sqrt u v).
rewrite ReE; congr (_ <= _ ?= iff _); apply: andb_id2r.
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
rewrite linear_sumlz big1 // => i _; rewrite linear_sumr big1 // => j _.
by rewrite linearZlr/= oS12 ?mem_nth ?mulr0.
Qed.

Lemma orthogonal_split S beta :
  {X : U  & X \in <<S>>%VS &
      {Y :U | [/\ beta = X + Y, '[X, Y] = 0 & orthogonal form [:: Y] S]}}.
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
  by rewrite linearBl linearZl_LR /= (orthoPl oVS _ Spsi) mulr0 subr0 (orthoPl oYS).
rewrite linearBl !linearDr /= (span_orthogonal oYS) // ?memv_span ?mem_head //.
rewrite !linearZl_LR /= (span_orthogonal oVS _ S_U) ?mulr0 ?memv_span ?mem_head //.
have [-> | nzV] := eqVneq V 0; first by rewrite linear0r !mul0r subrr.
by rewrite divfK ?dnorm_eq0 ?subrr.
Qed.

End DotFinVectTheory.
Arguments orthoP {C U form phi psi}.
Arguments pairwise_orthogonalP {C U form S}.
Arguments orthonormalP {C U form S}.
Arguments orthoPl {C U form phi S}.
Arguments orthoPr {C U form S psi}.

Section BuildIsometries.
Variables (C : numClosedFieldType) (U U1 U2 : vectType C).
Variables (form : {dot U for conjC}) (form1 : {dot U1 for conjC})
                                     (form2 : {dot U2 for conjC}).

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
apply: eq_bigr => i _ /=; rewrite !linearZ/= !linear_sumlz; congr (_ * _).
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
rewrite  2!{1}linear_sum /= !{1}linear_sumlz /=;  apply/eq_big_seq=> xi1 Sxi1.
rewrite !{1}linear_sumr; apply/eq_big_seq=> xi2 Sxi2 /=.
by rewrite !linearZ /= !linearZl !Dtau //= If.
Qed.

Lemma isometry_raddf_inj (tau : {additive U1 -> U2}) :
    {in U1 &, isometry form2 form1 tau} ->
    {in U1 &, forall u v, u - v \in U1} ->
  {in U1 &, injective tau}.
Proof.
move=> Itau linU phi psi Uphi Upsi /eqP; rewrite -subr_eq0 -raddfB.
by rewrite -(dnorm_eq0 form2)  Itau ?linU // dnorm_eq0 subr_eq0 => /eqP.
Qed.

End BuildIsometries.

Elpi mlock Definition form_of_matrix (R : fieldType) (n : nat) (theta : R -> R) m
   M (U V : 'M_(m, n)) := \tr (U *m M *m (V ^t theta)).

Section MatrixForms.
Variables (R : fieldType) (n : nat).
Implicit Types (a b : R) (u v : 'rV[R]_n) (M N P Q : 'M[R]_n).

Section Def.
Variable theta : R -> R.

Definition matrix_of_form (form : 'rV[R]_n -> 'rV[R]_n -> R) : 'M[R]_n :=
  \matrix_(i, j) form 'e_i 'e_j.

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

Let form_of_matrix_is_linear U :
  linear_for (theta \; *%R) (form_of_matrix theta M U).
Proof.
rewrite unlock => k v w; rewrite -linearP/=.
by rewrite linearP map_mxD map_mxZ !mulmxDr !scalemxAr.
Qed.

HB.instance Definition _ U := @GRing.isLinear.Build _ _ _ _
  (form_of_matrix theta M U) (form_of_matrix_is_linear U).

Definition form_of_matrixr U := (form_of_matrix theta M)^~U.

Let form_of_matrixr_is_linear U : linear_for *%R (form_of_matrixr U).
Proof.
rewrite /form_of_matrixr unlock => k v w.
by rewrite -linearP /= !mulmxDl -!scalemxAl.
Qed.

HB.instance Definition _ U := @GRing.isLinear.Build _ _ _ _
  (form_of_matrixr U) (form_of_matrixr_is_linear U).

(* TODO
Canonical form_of_matrixr_rev :=
  [revop form_of_matrixr of form_of_matrix theta M].
*)

Lemma form_of_matrix_is_bilinear :
  bilinear_for
    (GRing.Scale.Law.clone _ _ ( *%R ) _) (GRing.Scale.Law.clone _ _ (theta \; *%R ) _)
    (@form_of_matrix _ _ theta m M).
Proof.
split=> [u'|u] a x y /=.
- by rewrite unlock !mulmxDl linearD/= -!scalemxAl linearZ.
- rewrite unlock -linearZ/= -linearD/= [in LHS]linearD/= map_mxD.
  rewrite mulmxDr; congr (\tr (_ + _)).
  rewrite scalemxAr; congr (_ *m _).
  by rewrite linearZ/= map_mxZ.
Qed.

HB.instance Definition _ :=
  bilinear_isBilinear.Build R _ _ _
    (GRing.Scale.Law.clone _ _ ( *%R ) _)
    (GRing.Scale.Law.clone _ _ (theta \; *%R ) _)
    (@form_of_matrix _ _ theta m M)
    form_of_matrix_is_bilinear.
(*Canonical form_of_matrix_is_bilinear := [the @bilinear _ _ _ _ of form_of_matrix theta M].*)

End FormOfMatrix.

Section FormOfMatrix1.
Variables (M : 'M[R]_n).
Variables (theta : {rmorphism R -> R}).

Local Notation "''[' u , v ]" := (form_of_matrix theta M u%R v%R) : ring_scope.
Local Notation "''[' u ]" := '[u, u]%R : ring_scope.

Lemma rV_formee i j : '['e_i :'rV__, 'e_j] = M i j.
Proof.
rewrite unlock -rowE -map_trmx map_delta_mx -[M in LHS]trmxK.
by rewrite -tr_col -trmx_mul -rowE trace_mx11 !mxE.
Qed.

Lemma form_of_matrixK : matrix_of_form (form_of_matrix theta M) = M.
Proof. by apply/matrixP => i j; rewrite !mxE rV_formee. Qed.

Lemma rV_form0_eq0 : M = 0 -> forall u v, '[u, v] = 0.
Proof.
by rewrite unlock => -> u v; rewrite mulmx0 mul0mx trace_mx11 mxE.
Qed.

End FormOfMatrix1.

Section MatrixOfForm.
Variable (theta : {rmorphism R -> R}).
Variable form : {bilinear 'rV[R]_n -> 'rV[R]_n -> R | *%R & theta \; *%R}.

Lemma matrix_of_formK : form_of_matrix theta (matrix_of_form form) =2 form.
Proof.
set f := (X in X =2 _); have f_eq i j : f 'e_i 'e_j = form 'e_i 'e_j.
  by rewrite /f rV_formee mxE.
move=> u v; rewrite [u]row_sum_delta [v]row_sum_delta /f.
rewrite !linear_sum/=; apply: eq_bigr => j _.
rewrite !linear_sumlz/=; apply: eq_bigr => i _.
by rewrite !linearZlr/= -f_eq.
Qed.

End MatrixOfForm.

Section HermitianMx.
Variable eps : bool.

Section HermitianMxDef.
Variable theta : R -> R.

Definition hermitianmx :=
  [qualify M : 'M_n | M == ((-1) ^+ eps) *: M ^t theta].
Fact hermitianmx_key : pred_key hermitianmx. Proof. by []. Qed.
Canonical hermitianmx_keyed := KeyedQualifier hermitianmx_key.

Structure hermitian_matrix := HermitianMx {
  mx_of_hermitian :> 'M[R]_n;
  _ : mx_of_hermitian \is hermitianmx }.

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
Variables (theta : involutive_rmorphism R) (M : hermitian_matrix theta).

Lemma maptrmx_hermitian : M^t theta = (-1) ^+ eps *: (M : 'M__).
Proof.
rewrite trmx_hermitian map_mxZ rmorph_sign -map_mx_comp.
by rewrite (map_mx_id (rmorphK _)).
Qed.

Lemma form_of_matrix_is_hermitian m x y :
  (@form_of_matrix _ _ theta m M) x y =
  (-1) ^+ eps * theta ((@form_of_matrix _ _ theta m M) y x).
Proof.
rewrite {1}hermitianmxE unlock.
rewrite -!(scalemxAr, scalemxAl) linearZ/=; congr (_ * _).
rewrite -mxtrace_tr -trace_map_mx !(trmx_mul, map_mxM, map_trmx, trmxK).
by rewrite -mulmxA -!map_mx_comp !(map_mx_id (rmorphK _)).
Qed.

HB.instance Definition _ m := @isHermitianSesquilinear.Build _ _ _ _ _
  (@form_of_matrix_is_hermitian m).

Local Notation "''[' u , v ]" := (form_of_matrix theta M u%R v%R) : ring_scope.
Local Notation "''[' u ]" := '[u, u]%R : ring_scope.
Local Notation "B ^!" := (orthomx theta M B) : matrix_set_scope.
Local Notation "A '_|_ B" := (A%MS <= B%MS^!)%MS : matrix_set_scope.

Lemma orthomxE u v : (u '_|_ v)%MS = ('[u, v] == 0).
Proof.
rewrite (sameP sub_kermxP eqP) mulmxA.
by rewrite [_ *m _^t _]mx11_scalar -trace_mx11 fmorph_eq0 unlock.
Qed.

Lemma hermmx_eq0P {u v} : reflect ('[u, v] = 0) (u '_|_ v)%MS.
Proof. by rewrite orthomxE; apply/eqP. Qed.

Lemma orthomxP p q (A : 'M_(p, n)) (B :'M_(q, n)) :
  reflect (forall (u v : 'rV_n), u <= A -> v <= B -> u '_|_ v)%MS
          (A '_|_ B)%MS.
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
  (A '_|_ B)%MS = (B '_|_ A)%MS.
Proof.
gen have nC : p q A B / (A '_|_ B -> B '_|_ A)%MS; last by apply/idP/idP; apply/nC.
move=> AnB; apply/orthomxP => u v ? ?; rewrite orthomxE.
rewrite hermC mulf_eq0 ?fmorph_eq0 ?signr_eq0 /=.
by rewrite -orthomxE (orthomxP _ _ AnB).
Qed.

Lemma ortho_ortho_mx p (A : 'M_(p, n)) : (A^! '_|_ A)%MS. Proof. by []. Qed.

Lemma ortho_mx_ortho p (A : 'M_(p, n)) : (A '_|_ A^!)%MS.
Proof. by rewrite orthomx_sym. Qed.

Lemma rank_orthomx u : (\rank (u ^!) >= n.-1)%N.
Proof.
rewrite mxrank_ker -subn1 leq_sub2l //.
by rewrite (leq_trans (mxrankM_maxr  _ _)) // rank_leq_col.
Qed.

Local Notation radmx := (1%:M^!)%MS.

Lemma radmxE : radmx = kermx M.
Proof. by rewrite /orthomx /orthomx trmx1 map_mx1 mulmx1. Qed.

Lemma orthoNmx k m (A : 'M[R]_(k, n)) (B : 'M[R]_(m, n)) :
  ((- A) '_|_ B)%MS = (A '_|_ B)%MS.
Proof. by rewrite eqmx_opp. Qed.

Lemma orthomxN k m (A : 'M[R]_(k, n)) (B : 'M[R]_(m, n)) :
  (A '_|_ (- B))%MS = (A '_|_ B)%MS.
Proof. by rewrite ![(A '_|_ _)%MS]orthomx_sym orthoNmx. Qed.

Lemma orthoDmx k m p (A : 'M[R]_(k, n)) (B : 'M[R]_(m, n)) (C : 'M[R]_(p, n)) :
  (A + B '_|_ C)%MS = (A '_|_ C)%MS && (B '_|_ C)%MS.
Proof. by rewrite addsmxE !(sameP sub_kermxP eqP) mul_col_mx col_mx_eq0. Qed.

Lemma orthomxD  k m p (A : 'M[R]_(k, n)) (B : 'M[R]_(m, n)) (C : 'M[R]_(p, n)) :
  (A '_|_ B + C)%MS = (A '_|_ B)%MS && (A '_|_ C)%MS.
Proof. by rewrite ![(A '_|_ _)%MS]orthomx_sym orthoDmx. Qed.

Lemma orthoZmx p m a (A : 'M[R]_(p, n)) (B : 'M[R]_(m, n)) : a != 0 ->
  (a *: A '_|_ B)%MS = (A '_|_ B)%MS.
Proof. by move=> a_neq0; rewrite eqmx_scale. Qed.

Lemma orthomxZ p m a (A : 'M[R]_(p, n)) (B : 'M[R]_(m, n)) : a != 0 ->
  (A '_|_ (a *: B))%MS = (A '_|_ B)%MS.
Proof. by move=> a_neq0; rewrite ![(A '_|_ _)%MS]orthomx_sym orthoZmx. Qed.

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
Notation hermsymmx := (hermitianmx _ false conjC).

Lemma hermitian1mx_subproof {C : numClosedFieldType} n : (1%:M : 'M[C]_n) \is hermsymmx.
Proof.
by rewrite qualifE /= expr0 scale1r tr_scalar_mx map_scalar_mx conjC1.
Qed.

Canonical hermitian1mx {C : numClosedFieldType} n :=
  HermitianMx (@hermitian1mx_subproof C n).
