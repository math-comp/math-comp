Require Import ssreflect.

Class foo (A : Type) : Type := mkFoo { val : A }.
Instance foo_pair {A B} {f1 : foo A} {f2 : foo B} : foo (A * B) | 2 :=
  {| val := (@val _ f1, @val _ f2) |}.
Instance foo_nat : foo nat | 3 := {| val := 0 |}.

Definition id {A} (x : A) := x.
Axiom E : forall A {f : foo A} (a : A), id a = (@val _ f).

Lemma test (x : nat) : id true = true -> id x = 0.
Proof.
Fail move=> _; reflexivity.
Timeout 2 rewrite E => _; reflexivity.
Qed.

Definition P {A} (x : A) : Prop := x = x.
Axiom V : forall A {f : foo A} (x:A), P x -> P (id x).

Lemma test1 (x : nat) : P x -> P (id x).
Proof.
move => px.
Timeout 2 Fail move/V: px.
Timeout 2 move/V : (px) => _.
move/(V nat) : px => H; exact H.
Qed.



