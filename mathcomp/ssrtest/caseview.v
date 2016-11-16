(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.


Lemma test (A B : Prop) : A /\ B -> True.
Proof. by case=> _ /id _. Qed.