From mathcomp Require Import ssreflect ssrfun.
From Coq Require Export ssrbool.

(******************************************************************************)
(* Local additions:                                                           *)
(*      {pred T} == a type convertible to pred T but that presents the        *)
(*                  pred_sort coercion class.                                 *)
(*  PredType toP == the predType structure for toP : A -> pred T.             *)
(*    relpre f r == the preimage of r by f, simplifying to r (f x) (f y).     *)
(* --> These will become part of the core SSReflect library with Coq 8.11.    *)
(* This file also anticipates a v8.11 change in the definition of simpl_pred  *)
(* to T -> simpl_pred T. This change ensures that inE expands the definition  *)
(* of r : simpl_rel along with the \in, when rewriting in y \in r x.          *)
(******************************************************************************)

Notation "{ 'pred' T }" := (pred_sort (predPredType T)) (at level 0,
  format "{ 'pred'  T }") : type_scope.

Lemma simpl_pred_sortE T (p : pred T) : (SimplPred p : {pred T}) =1 p.
Proof. by []. Qed.
Definition inE := (inE, simpl_pred_sortE).

Definition PredType : forall T pT, (pT -> pred T) -> predType T.
exact PredType || exact mkPredType.
Defined.
Arguments PredType [T pT] toP.

Definition simpl_rel T := T -> simpl_pred T.
Definition SimplRel {T} (r : rel T) : simpl_rel T := fun x => SimplPred (r x).
Coercion rel_of_simpl_rel T (sr : simpl_rel T) : rel T := sr.
Arguments rel_of_simpl_rel {T} sr x / y : rename.

Notation "[ 'rel' x y | E ]" := (SimplRel (fun x y => E%B)) (at level 0,
  x ident, y ident, format "'[hv' [ 'rel'  x  y  | '/ '  E ] ']'") : fun_scope.
Notation "[ 'rel' x y : T | E ]" := (SimplRel (fun x y : T => E%B)) (at level 0,
  x ident, y ident, only parsing) : fun_scope.
Notation "[ 'rel' x y 'in' A & B | E ]" :=
  [rel x y | (x \in A) && (y \in B) && E] (at level 0, x ident, y ident,
  format "'[hv' [ 'rel'  x  y  'in'  A  &  B  | '/ '  E ] ']'") : fun_scope.
Notation "[ 'rel' x y 'in' A & B ]" := [rel x y | (x \in A) && (y \in B)]
  (at level 0, x ident, y ident,
  format "'[hv' [ 'rel'  x  y  'in'  A  &  B ] ']'") : fun_scope.
Notation "[ 'rel' x y 'in' A | E ]" := [rel x y in A & A | E]
  (at level 0, x ident, y ident,
  format "'[hv' [ 'rel'  x  y  'in'  A  | '/ '  E ] ']'") : fun_scope.
Notation "[ 'rel' x y 'in' A ]" := [rel x y in A & A] (at level 0,
  x ident, y ident, format "'[hv' [ 'rel'  x  y  'in'  A ] ']'") : fun_scope.

Notation xrelpre := (fun f (r : rel _) x y => r (f x) (f y)).
Definition relpre {T rT} (f : T -> rT)  (r : rel rT) :=
  [rel x y | r (f x) (f y)].

Section HomoMonoMorphismFlip.
Variables (aT rT : Type) (aR : rel aT) (rR : rel rT) (f : aT -> rT).
Variable (aD aD' : {pred aT}).

Lemma homo_sym : {homo f : x y / aR x y >-> rR x y} ->
  {homo f : y x / aR x y >-> rR x y}.
Proof. by move=> fR y x; apply: fR. Qed.

Lemma mono_sym : {mono f : x y / aR x y >-> rR x y} ->
  {mono f : y x / aR x y >-> rR x y}.
Proof. by move=> fR y x; apply: fR. Qed.

Lemma homo_sym_in : {in aD &, {homo f : x y / aR x y >-> rR x y}} ->
  {in aD &, {homo f : y x / aR x y >-> rR x y}}.
Proof. by move=> fR y x yD xD; apply: fR. Qed.

Lemma mono_sym_in : {in aD &, {mono f : x y / aR x y >-> rR x y}} ->
  {in aD &, {mono f : y x / aR x y >-> rR x y}}.
Proof. by move=> fR y x yD xD; apply: fR. Qed.

Lemma homo_sym_in11 : {in aD & aD', {homo f : x y / aR x y >-> rR x y}} ->
  {in aD' & aD, {homo f : y x / aR x y >-> rR x y}}.
Proof. by move=> fR y x yD xD; apply: fR. Qed.

Lemma mono_sym_in11 : {in aD & aD', {mono f : x y / aR x y >-> rR x y}} ->
  {in aD' & aD, {mono f : y x / aR x y >-> rR x y}}.
Proof. by move=> fR y x yD xD; apply: fR. Qed.

End HomoMonoMorphismFlip.
Arguments homo_sym {aT rT} [aR rR f].
Arguments mono_sym {aT rT} [aR rR f].
Arguments homo_sym_in {aT rT} [aR rR f aD].
Arguments mono_sym_in {aT rT} [aR rR f aD].
Arguments homo_sym_in11 {aT rT} [aR rR f aD aD'].
Arguments mono_sym_in11 {aT rT} [aR rR f aD aD'].

Section onW_can.

Variables (aT rT : predArgType) (aD : {pred aT}) (rD : {pred rT}).
Variables (f : aT -> rT) (g : rT -> aT).

Lemma onW_can : cancel g f -> {on aD, cancel g & f}.
Proof. by move=> fgK x xaD; apply: fgK. Qed.

Lemma onW_can_in : {in rD, cancel g f} -> {in rD, {on aD, cancel g & f}}.
Proof. by move=> fgK x xrD xaD; apply: fgK. Qed.

Lemma in_onW_can : cancel g f -> {in rD, {on aD, cancel g & f}}.
Proof. by move=> fgK x xrD xaD; apply: fgK. Qed.

Lemma onT_can : (forall x, g x \in aD) -> {on aD, cancel g & f} -> cancel g f.
Proof. by move=> mem_g fgK x; apply: fgK. Qed.

Lemma onT_can_in : {homo g : x / x \in rD >-> x \in aD} ->
  {in rD, {on aD, cancel g & f}} -> {in rD, cancel g f}.
Proof. by move=> mem_g fgK x x_rD; apply/fgK/mem_g. Qed.

Lemma in_onT_can : (forall x, g x \in aD) ->
  {in rT, {on aD, cancel g & f}} -> cancel g f.
Proof. by move=> mem_g fgK x; apply/fgK. Qed.

End onW_can.
Arguments onW_can {aT rT} aD {f g}.
Arguments onW_can_in {aT rT} aD {rD f g}.
Arguments in_onW_can {aT rT} aD rD {f g}.
Arguments onT_can {aT rT} aD {f g}.
Arguments onW_can_in {aT rT} aD {rD f g}.
Arguments in_onT_can {aT rT} aD {f g}.

Section MonoHomoMorphismTheory_in.

Variables (aT rT : predArgType) (aD : {pred aT}) (rD : {pred rT}).
Variables (f : aT -> rT) (g : rT -> aT) (aR : rel aT) (rR : rel rT).

Hypothesis fgK : {in rD, {on aD, cancel g & f}}.
Hypothesis mem_g : {homo g : x / x \in rD >-> x \in aD}.

Lemma homoRL_in :
    {in aD &, {homo f : x y / aR x y >-> rR x y}} ->
  {in rD & aD, forall x y, aR (g x) y -> rR x (f y)}.
Proof. by move=> Hf x y hx hy /Hf; rewrite fgK ?mem_g// ?inE; apply. Qed.

Lemma homoLR_in :
    {in aD &, {homo f : x y / aR x y >-> rR x y}} ->
  {in aD & rD, forall x y, aR x (g y) -> rR (f x) y}.
Proof. by move=> Hf x y hx hy /Hf; rewrite fgK ?mem_g// ?inE; apply. Qed.

Lemma homo_mono_in :
    {in aD &, {homo f : x y / aR x y >-> rR x y}} ->
    {in rD &, {homo g : x y / rR x y >-> aR x y}} ->
  {in rD &, {mono g : x y / rR x y >-> aR x y}}.
Proof.
move=> mf mg x y hx hy; case: (boolP (rR _ _))=> [/mg //|]; first exact.
by apply: contraNF=> /mf; rewrite !fgK ?mem_g//; apply.
Qed.

Lemma monoLR_in :
    {in aD &, {mono f : x y / aR x y >-> rR x y}} ->
  {in aD & rD, forall x y, rR (f x) y = aR x (g y)}.
Proof. by move=> mf x y hx hy; rewrite -{1}[y]fgK ?mem_g// mf ?mem_g. Qed.

Lemma monoRL_in :
    {in aD &, {mono f : x y / aR x y >-> rR x y}} ->
  {in rD & aD, forall x y, rR x (f y) = aR (g x) y}.
Proof. by move=> mf x y hx hy; rewrite -{1}[x]fgK ?mem_g// mf ?mem_g. Qed.

Lemma can_mono_in :
    {in aD &, {mono f : x y / aR x y >-> rR x y}} ->
  {in rD &, {mono g : x y / rR x y >-> aR x y}}.
Proof. by move=> mf x y hx hy; rewrite -mf ?mem_g// !fgK ?mem_g. Qed.

End MonoHomoMorphismTheory_in.
Arguments homoRL_in {aT rT aD rD f g aR rR}.
Arguments homoLR_in {aT rT aD rD f g aR rR}.
Arguments homo_mono_in {aT rT aD rD f g aR rR}.
Arguments monoLR_in {aT rT aD rD f g aR rR}.
Arguments monoRL_in {aT rT aD rD f g aR rR}.
Arguments can_mono_in {aT rT aD rD f g aR rR}.

Section inj_can_sym_in_on.
Variables (aT rT : predArgType) (aD : {pred aT}) (rD : {pred rT}).
Variables (f : aT -> rT) (g : rT -> aT).

Lemma inj_can_sym_in_on : {homo f : x / x \in aD >-> x \in rD} ->
  {in aD, {on rD, cancel f & g}} ->
  {in [pred x | x \in rD & g x \in aD], injective g} ->
  {in rD, {on aD, cancel g & f}}.
Proof. by move=> fD fK gI x x_rD gx_aD; apply: gI; rewrite ?inE ?fK ?fD. Qed.

Lemma inj_can_sym_on : {in aD, cancel f g} ->
  {in [pred x | g x \in aD], injective g} -> {on aD, cancel g & f}.
Proof. by move=> fK gI x gx_aD; apply: gI; rewrite ?inE ?fK. Qed.

Lemma inj_can_sym_in : {homo f \o g : x / x \in rD} -> {on rD, cancel f & g} ->
  {in rD, injective g} ->  {in rD, cancel g f}.
Proof. by move=> fgD fK gI x x_rD; apply: gI; rewrite ?fK ?fgD. Qed.

End inj_can_sym_in_on.
Arguments inj_can_sym_in_on {aT rT aD rD f g}.
Arguments inj_can_sym_on {aT rT aD f g}.
Arguments inj_can_sym_in {aT rT rD f g}.

