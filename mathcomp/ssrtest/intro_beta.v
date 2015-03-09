Require Import ssreflect.

Axiom T : Type.

Definition C (P : T -> Prop) := forall x, P x.

Axiom P : T -> T -> Prop.

Lemma foo : C (fun x => forall y, let z := x in P y x).
move=> a b. 
match goal with |- (let y := _ in _) => idtac end.
admit.
Qed.
