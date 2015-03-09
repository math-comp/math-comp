Require Import ssreflect eqtype ssrbool ssrnat seq div fintype finfun path bigop.

Lemma big_load R (K K' : R -> Type) idx op I r (P : pred I) F :
  let s := \big[op/idx]_(i <- r | P i) F i in
  K s * K' s -> K' s.
Proof. by move=> /= [_]. Qed.
Implicit Arguments big_load [R K' idx op I r P F].

Section Elim1.

Variables (R : Type) (K : R -> Type) (f : R -> R).
Variables (idx : R) (op op' : R -> R -> R).

Hypothesis Kid : K idx.

Ltac ASSERT1 := match goal with |- (K idx) => admit end.
Ltac ASSERT2 K := match goal with |- (forall x1 : R, R -> 
    forall y1 : R, R -> K x1 -> K y1 -> K (op x1 y1)) => admit end.


Lemma big_rec I r (P : pred I) F
    (Kop : forall i x, P i -> K x -> K (op (F i) x)) :
  K (\big[op/idx]_(i <- r | P i) F i).
Proof.
elim/big_ind2: {-}_.
  ASSERT1. ASSERT2 K. match goal with |- (forall i : I, is_true (P i) -> K (F i)) => admit end. Undo 4.
elim/big_ind2: _ / {-}_.
  ASSERT1. ASSERT2 K. match goal with |- (forall i : I, is_true (P i) -> K (F i)) => admit end. Undo 4.

elim/big_rec2: (\big[op/idx]_(i <- r | P i) op idx (F i))
  / (\big[op/idx]_(i <- r | P i) F i).
  ASSERT1. match goal with |- (forall i : I, R -> forall y2 : R, is_true (P i) -> K y2 -> K (op (F i) y2)) => admit end. Undo 3.

elim/(big_load (phantom R)): _.
  Undo.

Fail elim/big_rec2: {2}_.

elim/big_rec2: (\big[op/idx]_(i <- r | P i) F i)
  / {1}(\big[op/idx]_(i <- r | P i) F i).
  Undo.

elim/(big_load (phantom R)): _.
Undo.

Fail elim/big_rec2: _ / {2}(\big[op/idx]_(i <- r | P i) F i).
Admitted.

Definition morecomplexthannecessary A (P : A -> A -> Prop) x y := P x y.

Lemma grab A (P : A -> A -> Prop) n m : (n = m) -> (P n n) -> morecomplexthannecessary A P n m.
by move->.
Qed.

Goal forall n m, m + (n + m) = m + (n * 1 + m).
Proof. move=> n m; elim/grab : (_ * _) / {1}n => //; exact: muln1. Qed.

End Elim1.
