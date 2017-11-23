(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat.
From mathcomp
Require Import ssralg matrix.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope nat_scope.
Local Open Scope ring_scope.

Section TestMx.

Variable R : ringType.
Variable M : 'M[R]_2.

Goal 1%:M = M.
Proof.
Set Printing All.
rewrite [(1%:M : 'M_(1+1)%N)]scalar_mx_block.
(* Success with 1.2 *)
(* With ssreflect 1.3, fails with error : *)
(* Toplevel input, characters 0-44: *)
(* Error: pattern (1%:M) does not match LHS of scalar_mx_block *)
Admitted.

Goal 1%:M = M.
Proof.
rewrite [1%:M](scalar_mx_block 1%N 1%N).
(* Success in both ssr 1.2 and 1.3 *)
Admitted.

End TestMx.