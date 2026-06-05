- in `algebra/numeric_hierarchy/numfield.v`
  + `NumField_isImaginary` and `RealField_isClosed` are now HB factories
    (previously mixins) that rebuild the `conjFieldType` mixins, so that
    `numClosedFieldType` and `rcfType` inherit `conjFieldType`; their existing
    interfaces are otherwise unchanged
  + `conj`, `sqrtr` and their theory (`conjCK`, `normCK`, `mul_conjC_ge0`,
    `mul_conjC_gt0`, `mul_conjC_eq0`, `conjC_ge0`, `sqrtr_ge0`, `sqr_sqrtr`,
    `ler0_sqrtr`) generalized from `numClosedFieldType`/`rcfType` to
    `conjFieldType`
    ([#1611](https://github.com/math-comp/math-comp/pull/1611),
    by Guillaume Baudart and Cyril Cohen).

- in `algebra/sesquilinear.v`
  + the `conjC` `involutive_rmorphism` instance, `map_mxCK`, the dot-norm theory
    (`dnorm_geiff0`, `dnorm_ge0`, `dnorm_eq0`, `dnorm_gt0`, `dnormZ`, `dnormD`,
    `dnormB`) and `hermitian1mx` generalized from `numClosedFieldType` to
    `conjFieldType`
    ([#1611](https://github.com/math-comp/math-comp/pull/1611),
    by Guillaume Baudart and Cyril Cohen).

- in `algebra/spectral.v`
  + `trmxCK`, `dotmx`, `unitarymx`, the orthogonal-complement lemmas and the
    Gram-Schmidt process `schmidt` (with `schmidt_unitarymx`, `row_schmidt_sub`,
    `eqmx_schmidt_full`, `eqmx_schmidt_free`, `schmidt_complete`, ...)
    generalized from `numClosedFieldType` to `conjFieldType`; lemma names and
    statements are preserved
    ([#1611](https://github.com/math-comp/math-comp/pull/1611),
    by Guillaume Baudart and Cyril Cohen).
