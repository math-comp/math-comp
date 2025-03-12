- in `ssralg.v`
  + `Nmodule_isSemiRing` -> `Nmodule_isNzSemiRing`
  + `isSemiRing` -> `isNzSemiRing`
  + `Zmodule_isRing` -> `Zmodule_isNzRing`
  + `isRing` -> `isNzRing`
  + `SemiRing_hasCommutativeMul` -> `SemiRing_hasCommutativeMul`
  + `Nmodule_isComSemiRing` -> `Nmodule_isComNzSemiRing`
  + `Ring_hasCommutativeMul` -> `NzRing_hasCommutativeMul`
  + `Zmodule_isComRing` -> `Zmodule_isComNzRing`
  + `Ring_hasMulInverse` -> `NzRing_hasMulInverse`
  + `ComRing_hasMulInverse` -> `ComNzRing_hasMulInverse`
  + `ComRing_isField` -> `ComNzRing_isField`
  + `isSubSemiRing` -> `isSubNzSemiRing`
  + `SubNmodule_isSubSemiRing` -> `SubNmodule_isSubNzSemiRing`
  + `SubSemiRing_isSubComSemiRing` -> `SubNzSemiRing_isSubComNzSemiRing`
  + `SubZmodule_isSubRing` -> `SubZmodule_isSubNzRing`
  + `SubRing_isSubComRing` -> `SubNzRing_isSubComNzRing`
  + `SubRing_SubLmodule_isSubLalgebra` -> `SubNzRing_SubLmodule_isSubLalgebra`
  + `SubChoice_isSubSemiRing` -> `SubChoice_isSubNzSemiRing`
  + `SubChoice_isSubComSemiRing` -> `SubChoice_isSubComNzSemiRing`
  + `SubChoice_isSubRing` -> `SubChoice_isSubNzRing`
  + `SubChoice_isSubComRing` -> `SubChoice_isSubComNzRing`
  + `semiRingType` -> `nzSemiRingType`
  + `ringType` -> `nzRingType`
  + `comSemiRingType` -> `comNzSemiRingType`
  + `comRingType` -> `comNzRingType`
  + `subSemiRingType` -> `subNzSemiRingType`
  + `subComSemiRingType` -> `subComNzSemiRingType`
  + `subRingType` -> `subNzRingType`
  + ``subComNzRingType` -> `subComNzRingType`
  ([#1306](https://github.com/math-comp/math-comp/pull/1306),
  by Quentin Vermande).

- in `ring_quotient.v`
  + `isRingQuotient` -> `isNzRingQuotient`
  + `ringQuotType` -> `nzRingQuotType`
  ([#1306](https://github.com/math-comp/math-comp/pull/1306),
  by Quentin Vermande).

- in `finalg.v`
  + `isRing` -> `isNzRing`
  + `finSemiRingType`-> `finNzSemiRingType`
  + `finRingType` -> `finNzRingType`
  + `finComSemiRingType` -> `finComNzSemiRingType`
  + `finComRingType` -> `finComNzRingType`
  + `card_finRing_gt1` -> `card_finNzRing_gt1`
  ([#1306](https://github.com/math-comp/math-comp/pull/1306),
  by Quentin Vermande).

- in `countalg.v`
  + `countSemiRingType`-> `countNzSemiRingType`
  + `countRingType` -> `countNzRingType`
  + `countComSemiRingType` -> `countComNzSemiRingType`
  + `countComRingType` -> `countComNzRingType`
  ([#1306](https://github.com/math-comp/math-comp/pull/1306),
  by Quentin Vermande).
