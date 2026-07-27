- in `rings_modules_and_algebras.v`
  + `pzSemiRingType` -> `semiRingType`
  + HB class `GRing.PzSemiRing` -> `GRing.SemiRing`
  + Mixin `Nmodule_isPzSemiRing` -> `Nmodule_isSemiRing`
  + Factory `isPzSemiRing` -> `isSemiRing`
  + Mixin `PzSemiRing_isNonZero` -> `SemiRing_isNonZero`
  + `comPzSemiRingType` -> `comSemiRingType`
  + HB class `GRing.ComPzSemiRing` -> `GRing.ComSemiRing`
  + Factory `Nmodule_isComPzSemiRing` -> `Nmodule_isComSemiRing`
  + `pzRingType` -> `semiRingType`
  + HB class `GRing.PzRing` -> `GRing.Ring`
  + Factory `Zmodule_isPzRing` -> `Zmodule_isRing`
  + Factory `isPzRing` -> `isRing`
  + `comPzRingType` -> `comRingType`
  + HB class `GRing.ComPzRing` -> `GRing.ComRing`
  + Factory `Zmodule_isComPzRing` -> `Zmodule_isComRing`
  + `pzLSemiAlgType` -> `lSemiAlgType`
  + HB class `GRing.PzLSemiAlgebra` -> `GRing.LSemiAlgebra`
  + `pzLalgType` -> `lalgType`
  + HB class `GRing.PzLalgebra` -> `GRing.Lalgebra`
  + `pzSemiAlgType` -> `semiAlgType`
  + HB class `GRing.PzSemiAlgebra` -> `GRing.SemiAlgebra`
  + `pzAlgType` -> `algType`
  + HB class `GRing.PzAlgebra` -> `GRing.Algebra`
  + `comPzSemiAlgType` -> `comSemiAlgType`
  + HB class `GRing.ComPzSemiAlgebra` -> `GRing.ComSemiAlgebra`
  + `comPzAlgType` -> `comAlgType`
  + HB class `GRing.ComPzAlgebra` -> `GRing.ComAlgebra`
  + `subPzSemiRingType` -> `subSemiRingType`
  + HB class `GRing.SubPzSemiRing` -> `GRing.SubSemiRing`
  + Mixin `isSubPzSemiRing` -> `isSubSemiRing`
  + Factory `[SubNmodule_isSubPzSemiRing of U by <:]` ->
    `[SubNmodule_isSubSemiRing of U by <:]`
  + Factory `[SubChoice_isSubPzSemiRing of U by <:]` ->
    `[SubChoice_isSubSemiRing of U by <:]`
  + `subComPzSemiRingType` -> `subComSemiRingType`
  + HB class `GRing.SubComPzSemiRing` -> `GRing.SubComSemiRing`
  + Factory `[SubChoice_isSubComPzSemiRing of U by <:]` ->
    `[SubChoice_isSubComSemiRing of U by <:]`
  + `subPzRingType` -> `subRingType`
  + HB class `GRing.SubPzRing` -> `GRing.SubRing`
  + Factory `[SubChoice_isSubPzRing of U by <:]` ->
    `[SubChoice_isSubRing of U by <:]`
  + `subComPzRingType` -> `subComRingType`
  + HB class `GRing.SubComPzRing` -> `GRing.SubComRing`
  + Factory `[SubChoice_isSubComPzRing of U by <:]` ->
    `[SubChoice_isSubComRing of U by <:]`
  + `subPzLSemiAlgType` -> `subLSemiAlgType`
  + HB class `GRing.SubPzLSemiAlgebra` -> `GRing.SubLSemiAlgebra`
  + Factory `[SubChoice_isSubPzLSemiAlgebra of U by <:]` ->
    `[SubChoice_isSubLSemiAlgebra of U by <:]`
  + `subPzLalgType` -> `subLalgType`
  + HB class `GRing.SubPzLalgebra` -> `GRing.SubLalgebra`
  + Factory `[SubChoice_isSubPzLalgebra of U by <:]` ->
    `[SubChoice_isSubLalgebra of U by <:]`
  + `subPzSemiAlgType` -> `subSemiAlgType`
  + HB class `GRing.SubPzSemiAlgebra` -> `GRing.SubSemiAlgebra`
  + Factory `[SubChoice_isSubPzSemiAlgebra of U by <:]` ->
    `[SubChoice_isSubSemiAlgebra of U by <:]`
  + `subPzAlgType` -> `subAlgType`
  + HB class `GRing.SubPzAlgebra` -> `GRing.SubAlgebra`
  + Factory `[SubChoice_isSubPzAlgebra of U by <:]` ->
    `[SubChoice_isSubAlgebra of U by <:]`
    ([#1600](https://github.com/math-comp/math-comp/pull/1600),
    fixes [#1487](https://github.com/math-comp/math-comp/issues/1487)).
- in `countalg.v`
  + `countPzSemiRingType` -> `countSemiRingType`
  + HB class `CountRing.PzSemiRing` -> `CountRing.SemiRing`
  + `countPzRingType` -> `countRingType`
  + HB class `CountRing.PzRing` -> `CountRing.Ring`
  + `countComPzSemiRingType` -> `countComSemiRingType`
  + HB class `CountRing.ComPzSemiRing` -> `CountRing.ComSemiRing`
  + `countComPzRingType` -> `countComRingType`
  + HB class `CountRing.ComPzRing` -> `CountRing.ComRing`
    ([#1600](https://github.com/math-comp/math-comp/pull/1600),
    fixes [#1487](https://github.com/math-comp/math-comp/issues/1487)).
- in `finalg.v`
  + `finPzSemiRingType` -> `finSemiRingType`
  + HB class `FinRing.PzSemiRing` -> `FinRing.SemiRing`
  + `finPzRingType` -> `finRingType`
  + HB class `FinRing.PzRing` -> `FinRing.Ring`
  + `finComPzSemiRingType` -> `finComSemiRingType`
  + HB class `FinRing.ComPzSemiRing` -> `FinRing.ComSemiRing`
  + `finComPzRingType` -> `finComRingType`
  + HB class `FinRing.ComPzRing` -> `FinRing.ComRing`
    ([#1600](https://github.com/math-comp/math-comp/pull/1600),
    fixes [#1487](https://github.com/math-comp/math-comp/issues/1487)).
