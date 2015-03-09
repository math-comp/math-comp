(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool.

Lemma test b : b || ~~b.
wlog _ : b / b = true.
  case: b; [ by apply | by rewrite orbC ].
wlog suff: b /  b || ~~b.
  by case: b.
by case: b.
Qed.

Lemma test2 b c (H : c = b) : b || ~~b.
wlog _ : b {c H} / b = true.
  by case: b H.
by case: b.
Qed.