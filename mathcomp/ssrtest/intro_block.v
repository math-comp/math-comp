(* (c) Copyright 2006-2015 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import ssreflect.

Section foo.
Variable A : Type.
Record bar (X : Type) := {
  a : X * A;
  b : A;
  c := (a,7);
  _ : X
}.

Inductive baz (X : Type) (Y : Type) : nat -> Type :=
| K1 x (e : 0=1) (f := 3) of x=x:>X : baz X Y O
| K2 n of n=n & baz X nat 0 : baz X Y (n+1).

Axiom my_ind :
  forall P : nat -> Prop, P O -> (forall n m (w : P n /\ P m), P (n+m)) ->
     forall w, P w.


Lemma test x : bar nat -> baz nat nat x -> nat -> True.

move => [^~ _ccc ].
Check (refl_equal _ : c_ccc = (a_ccc, 7)).
move=> [^ xxx_ ].
Check (refl_equal _ : xxx_f = 3).
  by [].
elim/my_ind => [^ wow_ ].
  by [].
Check (wow_w : True /\ True).
by [].
Qed.
End foo.
