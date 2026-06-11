- in `rat.v`
  + the `Number Notation` for `rat` in `rat_scope` (`%Q`) now uses a
    binary-positive-encoded parser, so decimal literals elaborate in
    log-size terms instead of unary-nat ones. `0.314159%Q` drops from
    ~27s to sub-millisecond; literals like `3.141592653589793238462643383279%Q`
    (30 digits) that previously overflowed the stack now elaborate cleanly.
  + a new postfix notation `_%:RR` in `ring_scope` lifts a `rat` literal
    into any `unitRingType` via `ratr`, e.g. `(3.14%:RR : R)`. A full
    polymorphic `Number Notation` in `ring_scope` was avoided deliberately:
    it would intercept *all* numeric literals in the scope and break
    pattern-matching lemmas such as `pnatr_eq0` that expect the `n%:R` shape.
  + new definitions: `Posz_of_pos`, `Posz_zero`, `mkRat`, `mkRatN`
    (helpers for the `Number Notation`, all declared `simpl never`).
