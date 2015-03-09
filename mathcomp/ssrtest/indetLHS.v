Require Import ssreflect ssrnat.
Goal 5 = 3.
Fail (rewrite -(addnK _ 5)).
Abort.