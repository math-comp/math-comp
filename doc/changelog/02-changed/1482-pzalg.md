- in `ssralg.v`
  + The type parameter of `nzLSemiAlgType`, `nzSemiAlgType`, `comNzSemiAlgType`,
    `subNzLSemiAlgType`, `subNzSemiAlgType` has been changed from
    `pzSemiRingType` to `nzSemiRingType`
  + The type parameter of `nzLalgType`, `nzAlgType`, `comNzAlgType`,
    `subNzLalgType`, `subNzAlgType` has been changed from `pzRingType` to
    `nzRingType`
  + The linear semiring morphism structure `{lrmorphism A -> B}` generalized to
    `pzLSemiAlgType`
  + Structure `subalgClosed` generalized to `pzLSemiAlgType`
  + Factory `isSubSemiAlgClosed` generalized to `pzLSemiAlgType`
  + Factories `LSemiAlgebra_isComSemiAlgebra`, `LSemiModule_isComSemiAlgebra`
    generalized to `pzSemiAlgType`
  + Factories `Lmodule_isLalgebra` and `isSubalgClosed` generalized to
    `pzLalgType`
  + Factory `Lalgebra_isAlgebra` generalized to `pzAlgType`
  + Factory `Lalgebra_isComAlgebra` generalized to `comPzAlgType`
  + Factory `[SubSemiRing_SubLSemiModule_isSubLSemiAlgebra of V by <:]`
    generalized to `subPzLSemiAlgType`
  + Factory `[SubRing_SubLmodule_isSubLalgebra of V by <:]` generalized to
    `subPzLalgType`
  + Factory `[SubLSemiAlgebra_isSubSemiAlgebra of V by <:]` generalized to
    `subPzSemiAlgType`
  + Factory `[SubLalgebra_isSubAlgebra of V by <:]` generalized to
    `subPzAlgType`
  + Definitions `subsemialg_closed`, `scale_fun`, `in_alg` generalized to
    `pzLSemiAlgType`
  + Definition `subalg_closed` generalized to `pzLalgType`
  + Lemmas `mulr_algl`, `subsemialg_closedZ`, `subsemialg_closedM`,
    `rmorph_alg`, `subsemialgClosedP` generalized to `pzLSemiAlgType`
  + Lemmas `scalerCA`, `mulr_algr`, `comm_alg`, `exprZn`, `scaler_prod`,
    `scaler_prodl`, `scaler_prodr` generalized to `pzSemiAlgType`
  + Lemmas `subalg_closedZ`, `subalg_closedBM`, `subalg_closed_semi`,
    `subsemialg_closed_subalg`, `subsemialg_closedBM`, `subalgClosedP`
    generalized to `pzLalgType`
    ([#1482](https://github.com/math-comp/math-comp/pull/1482),
    fixes [#1386](https://github.com/math-comp/math-comp/issues/1386)).

- in `matrix.v`
  + `pzLSemiAlgType`, `pzLalgType`, `pzSemiAlgType`, `pzAlgType` instance on
    matrices generalized to potentially-zero (semi)rings and the case where the
    size is potentially zero
    ([#1482](https://github.com/math-comp/math-comp/pull/1482),
    fixes [#1386](https://github.com/math-comp/math-comp/issues/1386)).
