(* (c) Copyright 2006-2015 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool.
Goal forall x, x && true = x.
move=> x.
Fail (rewrite [X in _ && _]andbT).
Abort.
