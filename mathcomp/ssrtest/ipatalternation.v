(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.

Lemma test1 : Prop -> Prop -> Prop -> Prop -> Prop -> True = False -> Prop -> True \/ True.
by move=> A /= /= /= B C {A} {B} ? _ {C} {1}-> *; right.
Qed.