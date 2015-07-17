Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool.
Goal forall x, x && true = x.
move=> x.
Fail (rewrite [X in _ && _]andbT).
Abort.
