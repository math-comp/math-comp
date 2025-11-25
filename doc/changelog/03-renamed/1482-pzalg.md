- in `ssralg.v`
  + `lSemiAlgType` -> `nzLSemiAlgType`
  + `lalgType` -> `nzLalgType`
  + `semiAlgType` -> `nzSemiAlgType`
  + `algType` -> `nzAlgType`
  + `comSemiAlgType` -> `comNzSemiAlgType`
  + `comAlgType` -> `comNzAlgType`
  + `subLSemiAlgType` -> `subNzLSemiAlgType`
  + `subLalgType` -> `subNzLalgType`
  + `subSemiAlgType` -> `subNzSemiAlgType`
  + `subAlgType` -> `subNzAlgType`
  + `[SubNzSemiRing_SubLSemiModule_isSubLSemiAlgebra of U by <:]` ->
    `[SubSemiRing_SubLSemiModule_isSubLSemiAlgebra of U by <:]`
  + `[SubNzRing_SubLmodule_isSubLalgebra of U by <:]` ->
    `[SubRing_SubLmodule_isSubLalgebra of U by <:]`
  + `[SubChoice_isSubLSemiAlgebra of U by <:]` ->
    `[SubChoice_isSubNzLSemiAlgebra of U by <:]`
  + `[SubChoice_isSubLalgebra of U by <:]` ->
    `[SubChoice_isSubNzLalgebra of U by <:]`
  + `[SubChoice_isSubSemiAlgebra of U by <:]` ->
    `[SubChoice_isSubNzSemiAlgebra of U by <:]`
  + `[SubChoice_isSubAlgebra of U by <:]` ->
    `[SubChoice_isSubNzAlgebra of U by <:]`
    ([#1482](https://github.com/math-comp/math-comp/pull/1482),
    fixes [#1386](https://github.com/math-comp/math-comp/issues/1386)).

- in `finalg.v`
  + `finLalgType` -> `finNzLalgType`
  + `finAlgType` -> `finNzAlgType`
    ([#1482](https://github.com/math-comp/math-comp/pull/1482),
    fixes [#1386](https://github.com/math-comp/math-comp/issues/1386)).
