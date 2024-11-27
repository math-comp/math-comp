- in `ssrfun.v`
	+ `eqfun` now has type
			`forall [B] [A : B -> Type] (f g : forall b, A b), Prop`
	+ `eqrel` now has type
			`forall [C] [B : C -> Type] [A : forall c, B c -> Type]
				(f g : forall c b, A c b), Prop`
    (`#1300 <https://github.com/coq/stdlib/pull/1300>`_,
    by Tragicus).
