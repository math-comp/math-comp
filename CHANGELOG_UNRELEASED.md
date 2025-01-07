# Changelog (unreleased)

To avoid having old PRs put changes into the wrong section of the CHANGELOG,
new entries now go to the present file as discussed
[here](https://github.com/math-comp/math-comp/wiki/Agenda-of-the-April-23rd-2019-meeting-9h30-to-12h30#avoiding-issues-with-changelog).

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

### Added

- in `order.v`
  + notations `\min_<range> e`, `\max_<range> e`, `\min^d_<range> e`,
    `\max^d_<range> e`, `\min^p_<range> e`, `\max^p_<range> e`,
    `\min^sp_<range> e`, `\max^sp_<range> e`, `\meet^l_<range> e`,
    `\join^l_<range> e`, `\min^l_<range> e`, `\max^l_<range> e`

### Changed

- in `sesquilinear.v`,
  + notations `_ ^ _` and `_ ^t _` are now in the dedicated scope `sesquilinear_scope`.

- in `spectral.v`,
  + notations `_ ^t*` is now in the dedicated scope `sesquilinear_scope`.

### Renamed

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
	+ `subRingType` -> `nzSubRingType`
	+ ``subComNzRingType` -> `subComNzRingType`

- in `ring_quotient.v`
	+ `isRingQuotient` -> `isNzRingQuotient`
	+ `ringQuotType` -> `nzRingQuotType`

- in `finalg.v`
	+ `isRing` -> `isNzRing`
	+ `finSemiRingType`-> `finNzSemiRingType`
	+ `finRingType` -> `finNzRingType`
	+ `finComSemiRingType` -> `finComNzSemiRingType`
	+ `finComRingType` -> `finComNzRingType`
	+ `card_finRing_gt1` -> `card_finNzRing_gt1`

- in `countalg.v`
	+ `countSemiRingType`-> `countNzSemiRingType`
	+ `countRingType` -> `countNzRingType`
	+ `countComSemiRingType` -> `countComNzSemiRingType`
	+ `countComRingType` -> `countComNzRingType`

- in `poly.v`:
  + `size_opp` -> `size_polyN`
  + `size_add` -> `size_polyD`
  + `size_addl` -> `size_polyDl`
  + `size_mul_leq` -> `size_polyM_leq`

### Removed

### Deprecated

### Infrastructure

### Misc
