(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.


Lemma test1 : Prop -> Prop -> Prop -> Prop -> Prop -> True = False -> Prop -> True \/ True.
by move=> A /= /= /= B C {A} {B} ? _ {C} {1}-> *; right.
Qed.