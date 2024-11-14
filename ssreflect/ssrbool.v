From mathcomp Require Import ssreflect ssrfun.
From Coq Require Export ssrbool.

(******************************************************************************)
(* Local additions:                                                           *)
(*        [in A] == the applicative counterpart of a collective predicate A:  *)
(*                  [in A] x beta-expands to x \in A. This is similar to      *)
(*                  mem A, except that mem A x only simplifies to x \in A.    *)
(* --> These will become part of the core SSReflect library in later Coq      *)
(* versions.                                                                  *)
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

Lemma classic_sigW T (P : T -> Prop) :
  classically (exists x, P x) <-> classically ({x | P x}).
Proof. by split; apply: classic_bind => -[x Px]; apply/classicW; exists x. Qed.

Lemma classic_ex T (P : T -> Prop) :
  ~ (forall x, ~ P x) -> classically (exists x, P x).
Proof.
move=> NfNP; apply/classicP => exPF; apply: NfNP => x Px.
by apply: exPF; exists x.
Qed.

(**********************)
(* not yet backported *)
(**********************)

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

Lemma relpre_trans {T' T : Type} {leT : rel T} {f : T' -> T} :
  transitive leT -> transitive (relpre f leT).
Proof. by move=> + y x z; apply. Qed.
