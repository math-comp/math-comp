- in `vector.v`
  + Semi-vector space structure `semiVectType` over a `nzSemiRingType` that
    generalizes `vectType` to the case where there is no additive inverse
  + `LSemiModule_hasFinDim` mixin of semi-vector spaces
  + `semivector_axiom_def` (`SemiVector.axiom`) axiom of semi-vector spaces
  + `semiVectType` instances on matrices, `regular`, `prod`, `{ffun I -> vT}`,
    that generalize the corresponding `vectType` instances to the case where
    there is no additive inverse
    ([#1464](https://github.com/math-comp/math-comp/pull/1464)).
