Require Import ssreflect ssrbool eqtype ssrnat ssrfun.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* error 2 *)

Goal (exists f: Set -> nat, f nat = 0).
Proof. set (f:= fun  _:Set =>0). by exists f. Qed.

Goal (exists f: Set -> nat, f nat = 0).
Proof. set f := (fun  _:Set =>0). by exists f. Qed.

