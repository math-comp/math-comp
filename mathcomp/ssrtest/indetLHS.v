(* (c) Copyright 2006-2015 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrnat.
Goal 5 = 3.
Fail (rewrite -(addnK _ 5)).
Abort.