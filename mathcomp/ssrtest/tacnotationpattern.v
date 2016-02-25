Require Import mathcomp.ssreflect.ssreflect.
Tactic Notation "at" ssrpatternarg(p) tactic(t)
 := 
    ssrpattern p; let top := fresh in intro top;
    t top; try unfold top in * |- *; try clear top.

Goal forall x y, x + y = 4.
intros.
at [RHS] (fun top => remember top as E eqn:E_def).
match goal with
| |- x + y = E => idtac
| |- _ => fail
end.
Admitted.
