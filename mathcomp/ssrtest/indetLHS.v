Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrnat.
Goal 5 = 3.
Fail (rewrite -(addnK _ 5)).
Abort.