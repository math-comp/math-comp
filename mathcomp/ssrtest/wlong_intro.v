(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrnat.

Goal (forall x y : nat, True).
move=> x y.
wlog suff: x y / x <= y.
Admitted.
