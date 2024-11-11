From mathcomp Require Import ssreflect.
From Corelib Require Export ssrfun.
From mathcomp Require Export ssrnotations.
#[export] Set Warnings "-overwriting-delimiting-key".
(* remove above line when requiring Rocq >= 9.0 *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*******************)
(* v8.20 additions *)
(*******************)

(* The notations below are already defined in Coq.ssr.ssrfun, but we redefine *)
(* them in different notation scopes (mostly fun_scope -> function_scope, in  *)
(* order to replace the former with the latter).                              *)

Open Scope function_scope.

Definition eqfun (B : Type) (A : B -> Type) (f g : forall b, A b) : Prop :=
  forall x, f x = g x.
Definition eqrel (C : Type) (B : C -> Type) (A : forall c, B c -> Type)
    (f g : forall c (b : B c), A c b) : Prop :=
  forall x y, f x y = g x y.

Global Typeclasses Opaque eqfun eqrel.

Notation "f ^~ y" := (fun x => f x y) : function_scope.
Notation "@^~ x" := (fun f => f x) : function_scope.

Notation "[ 'fun' : T => E ]" := (SimplFun (fun _ : T => E)) : function_scope.
Notation "[ 'fun' x => E ]" := (SimplFun (fun x => E)) : function_scope.
Notation "[ 'fun' x y => E ]" := (fun x => [fun y => E]) : function_scope.
Notation "[ 'fun' x : T => E ]" := (SimplFun (fun x : T => E))
  (only parsing) : function_scope.
Notation "[ 'fun' x y : T => E ]" := (fun x : T => [fun y : T => E])
  (only parsing) : function_scope.
Notation "[ 'fun' ( x : T ) y => E ]" := (fun x : T => [fun y => E])
  (only parsing) : function_scope.
Notation "[ 'fun' x ( y : T ) => E ]" := (fun x => [fun y : T => E])
  (only parsing) : function_scope.
Notation "[ 'fun' ( x : T ) ( y : U ) => E ]" := (fun x : T => [fun y : U => E])
  (only parsing) : function_scope.

Notation "f1 =1 f2" := (eqfun f1 f2) : type_scope.
Notation "f1 =1 f2 :> A" := (f1 =1 (f2 : A)) : type_scope.
Notation "f1 =2 f2" := (eqrel f1 f2) : type_scope.
Notation "f1 =2 f2 :> A" := (f1 =2 (f2 : A)) : type_scope.

Notation "f1 \o f2" := (comp f1 f2) : function_scope.
Notation "f1 \; f2" := (catcomp f1 f2) : function_scope.

Notation "[ 'eta' f ]" := (fun x => f x) : function_scope.

Notation "'fun' => E" := (fun _ => E) : function_scope.

Notation "@ 'id' T" := (fun x : T => x)
  (at level 10, T at level 8, only parsing) : function_scope.

Notation "@ 'sval'" := (@proj1_sig) (at level 10, only parsing) :
  function_scope.

(******************)
(* v9.1 additions *)
(******************)

#[export] Set Warnings "-hiding-delimiting-key".
Delimit Scope function_scope with FUN.
Declare Scope fun_scope.
Close Scope fun_scope.

Definition injective2 (rT aT1 aT2 : Type) (f : aT1 -> aT2 -> rT) :=
  forall (x1 x2 : aT1) (y1 y2 : aT2), f x1 y1 = f x2 y2 -> (x1 = x2) * (y1 = y2).

Arguments injective2 [rT aT1 aT2] f.

Lemma inj_omap {aT rT : Type} (f : aT -> rT) :
  injective f -> injective (omap f).
Proof. by move=> injf [?|] [?|] //= [/injf->]. Qed.

Lemma omap_id {T : Type} (x : option T) : omap id x = x.
Proof. by case: x. Qed.

Lemma eq_omap {aT rT : Type} (f g : aT -> rT) : f =1 g -> omap f =1 omap g.
Proof. by move=> Ef [?|] //=; rewrite Ef. Qed.

Lemma omapK {aT rT : Type} (f : aT -> rT) (g : rT -> aT) :
  cancel f g -> cancel (omap f) (omap g).
Proof. by move=> fK [?|] //=; rewrite fK. Qed.

Definition idempotent_op (S : Type) (op : S -> S -> S) := forall x, op x x = x.

#[deprecated(since="mathcomp 2.3.0", note="use `idempotent_op` instead")]
Notation idempotent:= idempotent_op (only parsing).

Definition idempotent_fun (U : Type) (f : U -> U) := f \o f =1 f.

Lemma inr_inj {A B} : injective (@inr A B). Proof. by move=> ? ? []. Qed.

Lemma inl_inj {A B} : injective (@inl A B). Proof. by move=> ? ? []. Qed.

(**********************)
(* not yet backported *)
(**********************)

Lemma taggedK {I : Type} (T_ : I -> Type) (s : {i : I & T_ i}) :
  Tagged T_ (tagged s) = s.
Proof. by case: s. Qed.

Definition swap_pair {T1 T2 : Type} (x : T1 * T2) := (x.2, x.1).

(* Note that this lemma coudn't be an instance of the [involutive] predicate. *)
Lemma swap_pairK {T1 T2 : Type} : @cancel _ (T1 * T2) swap_pair swap_pair.
Proof. by case. Qed.
