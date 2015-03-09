Require Import ssreflect ssrbool.
Goal forall x, x && true = x.
move=> x.
Fail (rewrite [X in _ && _]andbT).
Abort.
