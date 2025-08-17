From mathcomp Require Import ssreflect.
From Corelib Require Export ssrfun.
From mathcomp Require Export ssrnotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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
