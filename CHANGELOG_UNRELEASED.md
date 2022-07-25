# Changelog (unreleased)

To avoid having old PRs put changes into the wrong section of the CHANGELOG,
new entries now go to the present file as discussed
[here](https://github.com/math-comp/math-comp/wiki/Agenda-of-the-April-23rd-2019-meeting-9h30-to-12h30#avoiding-issues-with-changelog).

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

### Added

- in `seq.v`
  + lemmas `subset_mapP`, `take_takel`, `take_taker`
  + generalized lemma `take_take` (the old `take_take` is now `take_takel`)

- in `path.v` 
  + lemmas `prefix_path`, `prefix_sorted`, `infix_sorted`, `suffix_sorted` 

- in `ssralg.v`
  + lemmas `natr1`, `nat1r`

- in `poly.v`
  + lemmas `comm_polyD`, `comm_polyM`, `comm_poly_exp`, `root_exp`,
    `root_ZXsubC`

- in `ssralg.v`
  + lemma `eqr_sum_div`

- in `ssrnum.v`
  + lemmas `psumr_neq0`, `psumr_neq0P`

- in `ssrnat.v`
  + lemmas `ltn_half_double`, `leq_half_double`, `gtn_half_double`
  + lemmas `uphalfE`, `ltn_uphalf_double`, `geq_uphalf_double`, `gtn_uphalf_double`

- in `ssrint.v`
  + printing only notation for `x = y :> int`, opening `int_scope` on
    `x` and `y` to better match the already existing parsing only
    notation with the introduction of number notations in `ring_scope`

### Changed

- in `poly.v`:
  + generalize `eq_poly`

- in `poly.v`:
  + made hornerE preserve powers

### Renamed

### Removed

### Infrastructure

### Misc

