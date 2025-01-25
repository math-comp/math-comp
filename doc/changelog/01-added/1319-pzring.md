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
	+ definition `pzSubRingType`
	+ factory `subZmodule_isSubPzRing`
	+ definition `subComPzRingType`
	+ factories `SubPzRing_isSubComPzRing`, `SubChoice_isSubPzSemiRing`,
		`SubChoice_isSubComPzSemiRing`, `SubChoice_isSubPzRing`,
		`SubChoice_isSubComPzRing`
    (`#1319 <https://github.com/coq/stdlib/pull/1319>`_,
    by Tragicus).
