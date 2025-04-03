- in `archimedean.v`
  + the definition of archimedean structures now include `Num.floor` and `Num.ceil`
  + as its consequence, `Num.ceil x = - Num.floor (- x)` does not hold definitionally anymore (use lemma `ceilNfloor` instead)
    ([#1250](https://github.com/math-comp/math-comp/pull/1250),
    by Kazuhiko Sakaguchi).
