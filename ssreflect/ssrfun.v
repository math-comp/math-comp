From mathcomp Require Import ssreflect.
From Corelib Require Export ssrfun.
From mathcomp Require Export ssrnotations.
#[export] Set Warnings "-overwriting-delimiting-key".
(* because there is some Set Warnings "overwriting-delimiting-key".
   somewhere in the above *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**********************)
(* not yet backported *)
(**********************)

#[export] Set Warnings "-hiding-delimiting-key".
Delimit Scope function_scope with FUN.
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
