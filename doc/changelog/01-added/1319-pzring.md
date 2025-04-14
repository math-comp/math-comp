- in `ssralg.v`
  + mixin `Nmodule_isPzSemiRing`
  + definition `pzSemiRingType`
  + factory `isPzSemiRing`
  + mixin `PzSemiRing_isNonZero`
  + definition `pzRingType`
  + factories `Zmodule_isPzRing`, `isPzRing`
  + mixin `PzSemiRing_hasCommutativeMul`
  + definition `comPzSemiRingType`
  + factory `Nmodule_isComPzSemiRing`
  + definition `comPzRingType`
  + factories `PzRing_hasCommutativeMul`, `Zmodule_isComPzRing`
  + mixin `isSubPzSemiRing`
  + definition `subPzSemiRingType`
  + factory `SubNmodule_isSubPzSemiRing`
  + definition `subComPzSemiRingType`
  + factory `SubPzSemiRing_isSubComPzSemiRing`
  + definition `subPzRingType`
  + factory `subZmodule_isSubPzRing`
  + definition `subComPzRingType`
  + factories `SubPzRing_isSubComPzRing`, `SubChoice_isSubPzSemiRing`,
    `SubChoice_isSubComPzSemiRing`, `SubChoice_isSubPzRing`,
    `SubChoice_isSubComPzRing`
    ([#1319](https://github.com/math-comp/math-comp/pull/1319),
    by Quentin Vermande).
