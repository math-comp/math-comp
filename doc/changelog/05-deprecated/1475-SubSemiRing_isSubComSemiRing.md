- in `ssralg.v`
  + factory `Lmodule_isLalgebra`, use `LSemiModule_isLSemiAlgebra` instead
  + factory `PzSemiRing_hasCommutativeMul`, use `SemiRing_hasCommutativeMul`
    instead
  + factory `Ring_hasCommutativeMul`, use `SemiRing_hasCommutativeMul` instead
  + factory `PzRing_hasCommutativeMul`, use `SemiRing_hasCommutativeMul` instead
  + factory `Lalgebra_isAlgebra`, use `LSemiAlgebra_isSemiAlgebra` instead
  + factory `Lalgebra_isComAlgebra`, use `LSemiAlgebra_isComSemiAlgebra` instead
  + factory `[SubPzSemiRing_isSubComPzSemiRing of U by <:]`,
    use `[SubSemiRing_isSubComSemiRing of U by <:]` instead
  + factory `[SubNzSemiRing_isSubComNzSemiRing of U by <:]`,
    use `[SubSemiRing_isSubComSemiRing of U by <:]` instead
  + factory `[SubPzRing_isSubComPzRing of U by <:]`,
    use `[SubSemiRing_isSubComSemiRing of U by <:]` instead
  + factory `[SubNzRing_isSubComNzRing of U by <:]`,
    use `[SubSemiRing_isSubComSemiRing of U by <:]` instead
  + factory `[SubZmodule_isSubLmodule of U by <:]`,
    use `[SubNmodule_isSubLSemiModule of U by <:]` instead
  + factory `[SubLalgebra_isSubAlgebra of U by <:]`,
    use `[SubLSemiAlgebra_isSubSemiAlgebra of U by <:]` instead
    ([#1475](https://github.com/math-comp/math-comp/pull/1475)).
