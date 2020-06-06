# Changelog (unreleased)

To avoid having old PRs put changes into the wrong section of the CHANGELOG,
new entries now go to the present file as discussed
[here](https://github.com/math-comp/math-comp/wiki/Agenda-of-the-April-23rd-2019-meeting-9h30-to-12h30#avoiding-issues-with-changelog).

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

- Added lemmas about monotony of functions `nat -> T` where `T` is an
  ordered type: `homo_ltn_lt_in`, `incn_inP`, `nondecn_inP`,
  `nhomo_ltn_lt_in`, `decn_inP`, `nonincn_inP`, `homo_ltn_lt`,
  `incnP`, `nondecnP`, `nhomo_ltn_lt`, `decnP`, `nonincnP` in file
  `order.v`.

- Added lemmas for swaping arguments of homomorphisms and
  monomorphisms: `homo_sym`, `mono_sym`, `homo_sym_in`, `mono_sym_in`,
  `homo_sym_in11`, `mono_sym_in11` in `ssrbool.v`

### Added

- in `ssrnum.v`, new lemmas:
  + `(real_)ltr_normlW`, `(real_)ltrNnormlW`, `(real_)ler_normlW`, `(real_)lerNnormlW`
  + `(real_)ltr_distl_addr`, `(real_)ler_distl_addr`, `(real_)ltr_distlC_addr`, `(real_)ler_distlC_addr`,
    `(real_)ltr_distl_subl`, `(real_)ler_distl_subl`, `(real_)ltr_distlC_subl`, `(real_)ler_distlC_subl`

- in `order.v`, defining `min` and `max` independently from `meet` and
  `join`, and providing a theory about for min and max, hence generalizing
  the theory of `Num.min` and `Num.max` from versions <= `1.10`, instead
  of specializing to total order as in `1.11+beta1`:
  ```
  Definition min (T : porderType) (x y : T) := if x < y then x else y.
  Definition max (T : porderType) (x y : T) := if x < y then y else x.
  ```
  + Lemmas: `min_l`, `min_r`, `max_l`, `max_r`, `minxx`, `maxxx`, `eq_minl`, `eq_maxr`,
    `min_idPl`, `max_idPr`, `min_minxK`, `min_minKx`, `max_maxxK`, `max_maxKx`,
    `comparable_minl`, `comparable_minr`,  `comparable_maxl`, and `comparable_maxr`
  + Lemmas about interaction with lattice operations:  `meetEtotal`, `joinEtotal`,
  + Lemmas under condition of pairwise comparability of a (sub)set of their arguments:
    `comparable_minC`, `comparable_maxC`, `comparable_eq_minr`, `comparable_eq_maxl`,
    `comparable_le_minr`, `comparable_le_minl`, `comparable_min_idPr`,
    `comparable_max_idPl`, `comparableP`, `comparable_lt_minr`,
    `comparable_lt_minl`, `comparable_le_maxr`, `comparable_le_maxl`,
    `comparable_lt_maxr`, `comparable_lt_maxl`, `comparable_minxK`, `comparable_minKx`,
    `comparable_maxxK`, `comparable_maxKx`,
    `comparable_minA`, `comparable_maxA`, `comparable_max_minl`, `comparable_min_maxl`,
    `comparable_minAC`, `comparable_maxAC`, `comparable_minCA`, `comparable_maxCA`,
    `comparable_minACA`, `comparable_maxACA`, `comparable_max_minr`, `comparable_min_maxr`
  + and the same but in a total order: `minC`, `maxC`, `minA`, `maxA`, `minAC`, `maxAC`,
    `minCA`, `maxCA`, `minACA`, `maxACA`, `eq_minr`, `eq_maxl`,
    `min_idPr`, `max_idPl`, `le_minr`, `le_minl`, `lt_minr`,
    `lt_minl`, `le_maxr`,`le_maxl`, `lt_maxr`, `lt_maxl`, `minxK`, `minKx`,
    `maxxK`, `maxKx`, `max_minl`, `min_maxl`, `max_minr`, `min_maxr`
- in `ssrnum.v`, theory about `min` and `max` extended to `numDomainType`:
  + Lemmas: `real_oppr_max`, `real_oppr_min`, `real_addr_minl`, `real_addr_minr`,
    `real_addr_maxl`, `real_addr_maxr`, `minr_pmulr`, `maxr_pmulr`, `real_maxr_nmulr`,
    `real_minr_nmulr`, `minr_pmull`, `maxr_pmull`, `real_minr_nmull`, `real_maxr_nmull`,
    `real_maxrN`, `real_maxNr`, `real_minrN`, `real_minNr`
- the compatibility module `ssrnum.mc_1_10` was extended to  support definitional
  compatibility with `min` and `max` which had been lost in `1.11+beta1` for most instances.
- in `fintype.v`, new lemmas: `seq_sub_default`, `seq_subE`
- in `order.v`, new "unfolding" lemmas: `minEnat` and `maxEnat`

### Changed

- in `order.v`, `le_xor_gt`, `lt_xor_ge`, `compare`, `incompare`, `lel_xor_gt`,
  `ltl_xor_ge`, `comparel`, `incomparel` have more parameters, so that the
  the following now deal with `min` and `max`
  + `comparable_ltgtP`, `comparable_leP`, `comparable_ltP`, `comparableP`
  + `lcomparableP`, `lcomparable_ltgtP`, `lcomparable_leP`, `lcomparable_ltP`, `ltgtP`
- in `order.v`:
  + `[arg min_(i < i0 | P) M]` now for `porderType` (was for `orderType`)
  + `[arg max_(i < i0 | P) M]` now for `porderType` (was for `orderType`)
  + added `comparable_arg_minP`,  `comparable_arg_maxP`,  `real_arg_minP`,  `real_arg_maxP`,
    in order to take advantage of the former generalizations.
- in `ssrnum.v`, `maxr` is a notation for `(@Order.max ring_display _)` (was `Order.join`)
  (resp. `minr` is a notation for `(@Order.min ring_display _)`)
- in `ssrnum.v`, `ler_xor_gt`, `ltr_xor_ge`, `comparer`,
  `ger0_xor_lt0`, `ler0_xor_gt0`, `comparer0` have now more parameters, so that
  the following now deal with min and max:
  + `real_leP`, `real_ltP x y`, `real_ltgtP`, `real_ge0P`, `real_le0P`, `real_ltgt0P`
  + `lerP`, `ltrP`, `ltrgtP`, `ger0P`, `ler0P`, `ltrgt0P`
- in `ssrnum.v`, the following have been restated (which were formerly derived from
  `order.v` and stated with specializations of the `meet` and `join` operators):
   + `minrC`, `minrr`, `minr_l`, `minr_r`, `maxrC`, `maxrr`, `maxr_l`,
     `maxr_r`, `minrA`, `minrCA`, `minrAC`, `maxrA`, `maxrCA`, `maxrAC`
   + `eqr_minl`, `eqr_minr`, `eqr_maxl`, `eqr_maxr`, `ler_minr`, `ler_minl`,
     `ler_maxr`, `ler_maxl`, `ltr_minr`, `ltr_minl`, `ltr_maxr`, `ltr_maxl`
   + `minrK`, `minKr`, `maxr_minl`, `maxr_minr`, `minr_maxl`, `minr_maxr`
- The new definitions of `min` and `max` may require the following rewrite rules
  changes when dealing with `max` and `min` instead of `meet` and `join`:
  + `ltexI` -> `(le_minr,lt_minr)`
  + `lteIx` -> `(le_minl,lt_minl)`
  + `ltexU` -> `(le_maxr,lt_maxr)`
  + `lteUx` -> `(le_maxl,lt_maxl)`
  + `lexU` -> `le_maxr`
  + `ltxU` -> `lt_maxr`
  + `lexU` -> `le_maxr`

### Renamed

- in `fintype` we deprecate and rename the following:
  + `arg_minP` -> `arg_minnP`
  + `arg_maxP` -> `arg_maxnP`

- in `order.v`, in module `NatOrder`, renamings:
  + `meetEnat` -> `minEnat`, `joinEnat` -> `maxEnat`,
    `meetEnat` -> `minEnat`, `joinEnat` -> `maxEnat`

### Removed

- in `order.v`, removed `total_display` (was used to provide the notation
  `max` for `join` and `min` for `meet`).
- in `order.v`, removed `minnE` and `maxnE`
- in `order.v`,
  + removed `meetEnat` (in favor of `meetEtotal` followed by `minEnat`)
  + removed `joinEnat` (in favor of `joinEtotal` followed by `maxEnat`).

### Infrastructure

### Misc
