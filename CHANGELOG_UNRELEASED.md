# Changelog (unreleased)

To avoid having old PRs put changes into the wrong section of the CHANGELOG,
new entries now go to the present file as discussed
[here](https://github.com/math-comp/math-comp/wiki/Agenda-of-the-April-23rd-2019-meeting-9h30-to-12h30#avoiding-issues-with-changelog).

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

### Added

- in `seq.v`
  + lemma `foldl_foldr`

- in `poly.v`
  + multirule `coefE`
  + lemmas `deg2_poly_canonical`, `deg2_poly_factor`,
    `deg2_poly_root1`, `deg2_poly_root2`,
    `FieldMonic.deg2_poly_canonical`, `FieldMonic.deg2_poly_factor`,
    `FieldMonic.deg2_poly_root1`, `FieldMonic.deg2_poly_root2`

- in `ssrnum.v`
  + lemmas `NumClosed.deg2_poly_factor`, `NumClosed.deg2_poly_root1`,
    `NumClosed.deg2_poly_root2`, `NumClosedMonic.deg2_poly_factor`,
    `NumClosedMonic.deg2_poly_root1`,
    `NumClosedMonic.deg2_poly_root2`, `Real.deg2_poly_min`,
    `Real.deg2_poly_minE`, `Real.deg2_poly_gt0`, `Real.deg2_poly_ge0`,
    `Real.deg2_poly_max`, `Real.deg2_poly_maxE`, `Real.deg2_poly_lt0`,
    `Real.deg2_poly_le0`, `Real.deg2_poly_factor`,
    `Real.deg2_poly_root1`, `Real.deg2_poly_root2`,
    `Real.deg2_poly_noroot`, `Real.deg2_poly_gt0l`,
    `Real.deg2_poly_gt0r`, `Real.deg2_poly_lt0m`,
    `Real.deg2_poly_ge0l`, `Real.deg2_poly_ge0r`,
    `Real.deg2_poly_le0m`, `Real.deg2_poly_lt0l`,
    `Real.deg2_poly_lt0r`, `Real.deg2_poly_gt0m`,
    `Real.deg2_poly_le0l`, `Real.deg2_poly_le0r`,
    `Real.deg2_poly_ge0m`, `RealMonic.deg2_poly_min`,
    `RealMonic.deg2_poly_minE`, `RealMonic.deg2_poly_gt0`,
    `RealMonic.deg2_poly_ge0`, `RealMonic.deg2_poly_factor`,
    `RealMonic.deg2_poly_root1`, `RealMonic.deg2_poly_root2`,
    `RealMonic.deg2_poly_noroot`, `RealMonic.deg2_poly_gt0l`,
    `RealMonic.deg2_poly_gt0r`, `RealMonic.deg2_poly_lt0m`,
    `RealMonic.deg2_poly_ge0l`, `RealMonic.deg2_poly_ge0r`,
    `RealMonic.deg2_poly_le0m`, `deg_le2_poly_delta_ge0`,
    `deg_le2_poly_delta_le0`, `deg_le2_poly_ge0`, `deg_le2_poly_le0`

- in `cyclic.v`
  + added lemma `units_Zp_cyclic`

### Changed

### Renamed

### Removed

### Deprecated

### Infrastructure

### Misc

