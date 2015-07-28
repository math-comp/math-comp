(* (c) Copyright 2006-2015 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool eqtype ssrnat ssrfun.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* error 2 *)

Goal (exists f: Set -> nat, f nat = 0).
Proof. set (f:= fun  _:Set =>0). by exists f. Qed.

Goal (exists f: Set -> nat, f nat = 0).
Proof. set f := (fun  _:Set =>0). by exists f. Qed.

