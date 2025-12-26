- in `vector.v`
  + proper (semi-)vector space structures `nzSemiVectType` and `nzVectType`
  + mixin `SemiVector_isProper`
  + lemma `dim_gt0`
  + canonical `nzSemiVectType` (resp. `nzVectType`) on `R^o` for any
    `nzSemiRingType` (resp. `nzRingType) `R`
    ([#1492](https://github.com/math-comp/math-comp/pull/1492),
    fixes [#1470](https://github.com/math-comp/math-comp/issues/1470)).

- in `falgebra.v`
  + factory `UnitAlgebra_isFalgebra` for deriving a `falgType R` instance of a
    type that is canonically a `vectType R` and a `unitAlgType R`
    ([#1492](https://github.com/math-comp/math-comp/pull/1492),
    fixes [#1470](https://github.com/math-comp/math-comp/issues/1470)).
