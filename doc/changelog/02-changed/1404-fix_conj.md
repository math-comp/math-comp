- in `numfield.v`
  + `Num.conj_op` has been renamed to `Num.conj` and its type has been changed
    from `{rmorphism R -> R}` to `R -> R` (for any `R : numClosedFieldType`).
    The new constant `Num.conj` is canonically a ring morphism. The `Num.Def`
    module now provides its shorthand `conjC`
    ([#1404](https://github.com/math-comp/math-comp/pull/1404),
    fixes [#1401](https://github.com/math-comp/math-comp/issues/1401)).
