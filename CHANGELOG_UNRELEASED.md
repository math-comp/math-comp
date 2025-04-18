# Changelog (unreleased)

To avoid having old PRs put changes into the wrong section of the CHANGELOG,
new entries now go to the present file as discussed
[here](https://github.com/math-comp/math-comp/wiki/Agenda-of-the-April-23rd-2019-meeting-9h30-to-12h30#avoiding-issues-with-changelog).

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

### Added

### Renamed

- in `ssralg.v`
    + `semi_additive` -> `nmod_morphism`
	+ `isSemiAdditive` -> `isNmodMorphism`
	+ `additive` -> `zmod_morphism`
	+ `isAdditive` -> `isZmodMorphism`
	+ `multiplicative` -> `monoid_morphism`
    + `isMultiplicative` -> `isMonoidMorphism`

    + `can2_semi_additive` -> `can2_nmod_morphism`.
    + `can2_additive` -> `can2_zmod_morphism`.
    + `additive_semilinear` -> `nmod_morphism_semilinear`.
    + `additive_linear` -> `zmod_morphism_linear`.
    + `rmorphismMP` -> `rmorphism_monoidP`.

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

- in `fraction.v`
    + `tofrac_is_additive` -> `tofrac_is_zmod_morphism`
    + `tofrac_is_multiplicative` -> `tofrac_is_monoid_morphism`

- in `matrix.v`
    + `const_mx_is_semi_additive` -> `const_mx_is_nmod_morphism`
    + `swizzle_mx_is_semi_additive` -> `swizzle_mx_is_nmod_morphism`
    + `diag_mx_is_semi_additive` -> `diag_mx_is_nmod_morphism`
    + `scalar_mx_is_semi_additive` -> `scalar_mx_is_nmod_morphism`
    + `mxtrace_is_semi_additive` -> `mxtrace_is_nmod_morphism`
    + `const_mx_is_additive` -> `const_mx_is_zmod_morphism`
    + `swizzle_mx_is_additive` -> `swizzle_mx_is_zmod_morphism`
    + `diag_mx_is_additive` -> `diag_mx_is_zmod_morphism`
    + `scalar_mx_is_additive` -> `scalar_mx_is_zmod_morphism`
    + `mxtrace_is_additive` -> `mxtrace_is_zmod_morphism`
    + `scalar_mx_is_multiplicative` -> `scalar_mx_is_monoid_morphism`
    + `map_mx_is_multiplicative` -> `map_mx_is_monoid_morphism`

- in `poly.v`
    + `polyC_multiplicative` -> `polyC_is_monoid_morphism`
    + `coefp0_multiplicative` -> `coefp0_is_monoid_morphism`
    + `map_poly_is_additive` -> `map_poly_is_zmod_morphism`
    + `map_poly_is_multiplicative` -> `map_poly_is_monoid_morphism`
    + `horner_is_multiplicative` -> `horner_is_monoid_morphism`
    + `horner_eval_is_multiplicative` -> `horner_eval_is_monoid_morphism`
    + `comp_poly_multiplicative` -> `comp_poly_is_monoid_morphism`

- TODO:

polyXY.v
qpoly.v
rat.v
ring_quotient.v
ssrint.v
ssrnum.v
character.v
classfun.v
inertia.v
mxrepresentation.v
algC.v
algebraics_fundamentals.v
algnum.v
closed_field.v
falgebra.v
fieldext.v
galois.v


### Removed

### Deprecated

### Infrastructure

### Misc
