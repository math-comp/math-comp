# Changelog (unreleased)

To avoid having old PRs put changes into the wrong section of the CHANGELOG,
new entries now go to the present file as discussed
[here](https://github.com/math-comp/math-comp/wiki/Agenda-of-the-April-23rd-2019-meeting-9h30-to-12h30#avoiding-issues-with-changelog).

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

### Added

### Changed

### Renamed

- in `binomial.v`
  + `triangular_sum` -> `bin2_sum`

- in `order.v` (cf. Changed section)
  + `finLatticeType` -> `finTBLatticeType`
  + `finDistrLatticeType` -> `finTBDistrLatticeType`
  + `finOrderType` -> `finTBOrderType`
  + `finCDistrLatticeType` -> `finCTBDistrLatticeType`

- in `archimedean.v`
  + `floor_itv` -> `real_floor_itv`
  + `ge_floor` -> `real_ge_floor`
  + `lt_succ_floor` -> `real_lt_succ_floor`
  + `floor_ge_int` -> `real_floor_ge_int`
  + `floorD` -> `real_floorDzr`
  + `ceil_itv` -> `real_ceil_itv`
  + `gt_pred_ceil` -> `real_gt_pred_ceil`
  + `le_ceil` -> `real_le_ceil`
  + `ceil_le_int` -> `real_ceil_le_int`
  + `ceilD` -> `real_ceilDzr`
  + `ceil_floor` -> `real_ceil_floor`

- in `ssrint.v`
  + `mulrzDr` -> `mulrzDl`
  + `mulrzDl` -> `mulrzDr`

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


### Removed

### Deprecated

### Infrastructure

### Misc
