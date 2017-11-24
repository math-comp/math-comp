(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.


Axiom T : Type.

Definition C (P : T -> Prop) := forall x, P x.

Axiom P : T -> T -> Prop.

Lemma foo : C (fun x => forall y, let z := x in P y x).
move=> a b.
match goal with |- (let y := _ in _) => idtac end.
Admitted.
