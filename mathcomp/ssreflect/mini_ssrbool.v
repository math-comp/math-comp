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
