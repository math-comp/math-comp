From mathcomp Require Import ssreflect.


Set Primitive Projections.

Module T1.

Record foo A := Foo { foo_car : A }.

Definition bar : foo _ := Foo nat 10.

Goal foo_car _ bar = 10.
match goal with
| |- foo_car _ bar = 10 => idtac
end.
rewrite /foo_car.
Fail match goal with
| |- foo_car _ bar = 10 => idtac
end.
Admitted.

End T1.


Module T2.

Record foo {A} := Foo { foo_car : A }.

Definition bar : foo := Foo nat 10.

Goal foo_car bar = 10.
match goal with
| |- foo_car bar = 10 => idtac
end.
rewrite /foo_car.
Fail match goal with
| |- foo_car bar = 10 => idtac
end.
Admitted.

End T2.


Module T3.

Record foo {A} := Foo { foo_car : A }.

Definition bar : foo := Foo nat 10.

Goal foo_car bar = 10.
rewrite -[foo_car _]/(id _).
match goal with |- id _ = 10 => idtac end.
Admitted.

Goal foo_car bar = 10.
set x := foo_car _.
match goal with |- x = 10 => idtac end.
Admitted.

End T3.