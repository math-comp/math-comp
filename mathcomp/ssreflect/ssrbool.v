From mathcomp Require Import ssreflect ssrfun.
From Coq Require Export ssrbool.

(******************************************************************************)
(* Local additions:                                                           *)
(*        [in A] == the applicative counterpart of a collective predicate A:  *)
(*                  [in A] x beta-expands to x \in A. This is similar to      *)
(*                  mem A, except that mem A x only simplfies to x \in A.     *)
(* --> These will become part of the core SSReflect library in later Coq      *)
(* versions.                                                                  *)
(*   For the sake of backwards compatibility, this file also replicates       *)
(* v8.13-15 additions, including a generalization of the statments of         *)
(* `homoRL_in`, `homoLR_in`, `homo_mono_in`, `monoLR_in`, `monoRL_in`, and    *)
(* `can_mono_in`.                                                             *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*******************)
(* v8.20 additions *)
(*******************)

Notation "[ 'in' A ]" := (in_mem^~ (mem A))
  (at level 0, format "[ 'in'  A ]") : function_scope.

(* The notations below are already defined in Coq.ssr.ssrbool, but we redefine*)
(* them in different notation scopes (mostly fun_scope -> function_scope, in  *)
(* order to replace the former with the latter).                              *)

Notation "[ 'pred' : T | E ]" := (SimplPred (fun _ : T => E%B)) :
  function_scope.
Notation "[ 'pred' x | E ]" := (SimplPred (fun x => E%B)) : function_scope.
Notation "[ 'pred' x | E1 & E2 ]" := [pred x | E1 && E2 ] : function_scope.
Notation "[ 'pred' x : T | E ]" :=
  (SimplPred (fun x : T => E%B)) (only parsing) : function_scope.
Notation "[ 'pred' x : T | E1 & E2 ]" :=
  [pred x : T | E1 && E2 ] (only parsing) : function_scope.

Notation "[ 'rel' x y | E ]" := (SimplRel (fun x y => E%B))
  (only parsing) : function_scope.
Notation "[ 'rel' x y : T | E ]" :=
  (SimplRel (fun x y : T => E%B)) (only parsing) : function_scope.

Notation "[ 'mem' A ]" :=
  (pred_of_simpl (simpl_of_mem (mem A))) (only parsing) : function_scope.

Notation "[ 'pred' x 'in' A ]" := [pred x | x \in A] : function_scope.
Notation "[ 'pred' x 'in' A | E ]" := [pred x | x \in A & E] : function_scope.
Notation "[ 'pred' x 'in' A | E1 & E2 ]" :=
  [pred x | x \in A & E1 && E2 ] : function_scope.

Notation "[ 'rel' x y 'in' A & B | E ]" :=
  [rel x y | (x \in A) && (y \in B) && E] : function_scope.
Notation "[ 'rel' x y 'in' A & B ]" :=
  [rel x y | (x \in A) && (y \in B)] : function_scope.
Notation "[ 'rel' x y 'in' A | E ]" := [rel x y in A & A | E] : function_scope.
Notation "[ 'rel' x y 'in' A ]" := [rel x y in A & A] : function_scope.

(* Both bodies and the scope have been changed for the following notations.   *)
Notation "[ 'predI' A & B ]" := (predI [in A] [in B]) : function_scope.
Notation "[ 'predU' A & B ]" := (predU [in A] [in B]) : function_scope.
Notation "[ 'predD' A & B ]" := (predD [in A] [in B]) : function_scope.
Notation "[ 'predC' A ]" := (predC [in A]) : function_scope.
Notation "[ 'preim' f 'of' A ]" := (preim f [in A]) : function_scope.

(*******************)
(* v8.17 additions *)
(*******************)

Lemma all_sig2_cond {I T} (C : pred I) P Q :
    T -> (forall x, C x -> {y : T | P x y & Q x y}) ->
  {f : I -> T | forall x, C x -> P x (f x) & forall x, C x -> Q x (f x)}.
Proof.
by move=> /all_sig_cond/[apply]-[f Pf]; exists f => i Di; have [] := Pf i Di.
Qed.

Lemma can_in_pcan [rT aT : Type] (A : {pred aT}) [f : aT -> rT] [g : rT -> aT] :
  {in A, cancel f g} -> {in A, pcancel f (fun y : rT => Some (g y))}.
Proof. by move=> fK x Ax; rewrite fK. Qed.

Lemma pcan_in_inj [rT aT : Type] [A : {pred aT}]
    [f : aT -> rT] [g : rT -> option aT] :
  {in A, pcancel f g} -> {in A &, injective f}.
Proof. by move=> fK x y Ax Ay /(congr1 g); rewrite !fK// => -[]. Qed.

Lemma in_inj_comp A B C (f : B -> A) (h : C -> B) (P : pred B) (Q : pred C) :
  {in P &, injective f} -> {in Q &, injective h} -> {homo h : x / Q x >-> P x} ->
  {in Q &, injective (f \o h)}.
Proof.
by move=> Pf Qh QP x y xQ yQ xy; apply Qh => //; apply Pf => //; apply QP.
Qed.

Lemma can_in_comp [A B C : Type] (D : {pred B}) (D' : {pred C})
    [f : B -> A] [h : C -> B] [f' : A -> B] [h' : B -> C] :
  {homo h : x / x \in D' >-> x \in D} ->
  {in D, cancel f f'} -> {in D', cancel h h'} ->
  {in D', cancel (f \o h) (h' \o f')}.
Proof. by move=> hD fK hK c cD /=; rewrite fK ?hK ?hD. Qed.

Lemma pcan_in_comp [A B C : Type] (D : {pred B}) (D' : {pred C})
    [f : B -> A] [h : C -> B] [f' : A -> option B] [h' : B -> option C] :
  {homo h : x / x \in D' >-> x \in D} ->
  {in D, pcancel f f'} -> {in D', pcancel h h'} ->
  {in D', pcancel (f \o h) (obind h' \o f')}.
Proof. by move=> hD fK hK c cD /=; rewrite fK/= ?hK ?hD. Qed.

Definition pred_oapp T (D : {pred T}) : pred (option T) :=
  [pred x | oapp (mem D) false x].

Lemma ocan_in_comp [A B C : Type] (D : {pred B}) (D' : {pred C})
    [f : B -> option A] [h : C -> option B] [f' : A -> B] [h' : B -> C] :
  {homo h : x / x \in D' >-> x \in pred_oapp D} ->
  {in D, ocancel f f'} -> {in D', ocancel h h'} ->
  {in D', ocancel (obind f \o h) (h' \o f')}.
Proof.
move=> hD fK hK c cD /=; rewrite -[RHS]hK/=; case hcE : (h c) => [b|]//=.
have bD : b \in D by have := hD _ cD; rewrite hcE inE.
by rewrite -[b in RHS]fK; case: (f b) => //=; have /hK := cD; rewrite hcE.
Qed.

Lemma eqbLR (b1 b2 : bool) : b1 = b2 -> b1 -> b2.
Proof. by move->. Qed.

Lemma eqbRL (b1 b2 : bool) : b1 = b2 -> b2 -> b1.
Proof. by move->. Qed.

Lemma homo_mono1 [aT rT : Type] [f : aT -> rT] [g : rT -> aT]
    [aP : pred aT] [rP : pred rT] :
  cancel g f ->
  {homo f : x / aP x >-> rP x} ->
  {homo g : x / rP x >-> aP x} -> {mono g : x / rP x >-> aP x}.
Proof. by move=> gK fP gP x; apply/idP/idP => [/fP|/gP//]; rewrite gK. Qed.

Lemma if_and b1 b2 T (x y : T) :
  (if b1 && b2 then x else y) = (if b1 then if b2 then x else y else y).
Proof. by case: b1 b2 => [] []. Qed.

Lemma if_or b1 b2 T (x y : T) :
  (if b1 || b2 then x else y) = (if b1 then x else if b2 then x else y).
Proof. by case: b1 b2 => [] []. Qed.

Lemma if_implyb b1 b2 T (x y : T) :
  (if b1 ==> b2 then x else y) = (if b1 then if b2 then x else y else x).
Proof. by case: b1 b2 => [] []. Qed.

Lemma if_implybC b1 b2 T (x y : T) :
  (if b1 ==> b2 then x else y) = (if b2 then x else if b1 then y else x).
Proof. by case: b1 b2 => [] []. Qed.

Lemma if_add b1 b2 T (x y : T) :
  (if b1 (+) b2 then x else y) = (if b1 then if b2 then y else x else if b2 then x else y).
Proof. by case: b1 b2 => [] []. Qed.

(**********************)
(* not yet backported *)
(**********************)

Lemma relpre_trans {T' T : Type} {leT : rel T} {f : T' -> T} :
  transitive leT -> transitive (relpre f leT).
Proof. by move=> + y x z; apply. Qed.
