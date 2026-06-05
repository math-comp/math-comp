- in `algebra/numeric_hierarchy/numfield.v`
  + structures `conjFieldType` (`ConjField`) and `NumFieldConj`, a common
    ancestor of `rcfType` and `numClosedFieldType` providing an involutive
    conjugation `conj` with `|x| ^+ 2 = x * conj x` and a square root of
    nonnegative elements
  + mixins `NumField_hasConj`, `NumField_hasSqrt`, `NumField_hasImaginary` and
    `RealField_hasPolyIvt`
    ([#1611](https://github.com/math-comp/math-comp/pull/1611),
    by Guillaume Baudart and Cyril Cohen).

- in `algebra/archimedean.v`
  + join structures `ArchiNumFieldConj` and `ArchiConjField`
    ([#1611](https://github.com/math-comp/math-comp/pull/1611),
    by Guillaume Baudart and Cyril Cohen).

- in `algebra/spectral.v`
  + definition `realsubfield` and injection `realsubval`, equipping the subfield
    of real elements of a `numClosedFieldType` with an `rcfType` structure
  + lemmas `flag_pid_mx` and `schmidt_trig` (the triangular Gram-Schmidt factor)
  + lemma `schmidt_diag_real` and theorem `real_spectral_theorem`, the spectral
    theorem for real symmetric matrices
    ([#1611](https://github.com/math-comp/math-comp/pull/1611),
    by Guillaume Baudart and Cyril Cohen).
