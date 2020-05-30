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

- in `order.v`, theory about for min and max
  ```
  Definition min x y := if x < y then x else y.
  Definition max x y := if x < y then y else x.
  ...
  Definition meet := @min _ T.
  Definition join := @max _ T.
  ```
  + Lemmas: `min_l`, `min_r`, `max_l`, `max_r`, `minxx`, `maxxx`,
    `eq_minl`, `eq_maxr`, `comparable_minl`, `comparable_minr`,
    `comparable_maxl`, `comparable_maxr`
  + Lemmas under condition `x >=< y`:
    `comparable_minC`, `comparable_maxC`, `comparable_eq_minr`, `comparable_eq_maxl`,
    `comparable_le_minr`, `comparable_le_minl`, `comparableP`, `comparable_lt_minr`,
    `comparable_lt_minl`, `comparable_le_maxr`, `comparable_le_maxl`,
    `comparable_lt_maxr`, `comparable_lt_maxl`, `comparable_minxK`, `comparable_minKx`,
    `comparable_maxxK`, `comparable_maxKx`
  + Lemmas under conditions  x >=< y x >=< z y >=< z:
    `comparable_minA`, `comparable_maxA`, `comparable_max_minl`, `comparable_min_maxl`,
    `comparable_minAC`, `comparable_maxAC`, `comparable_minCA`, `comparable_maxCA`,
    `comparable_minACA`, `comparable_maxACA`, `comparable_max_minr`, `comparable_min_maxr`
  + Lemmas about interaction with lattice operations:
    `meetEtotal`, `joinEtotal`, `minC`, `maxC`, `minA`, `maxA`, `minAC`, `maxAC`,
    `minCA`, `maxCA`, `minACA`, `maxACA`, `eq_minr`, `eq_maxl`, `le_minr`, `le_minl`,
    `lt_minr`, `lt_minl`, `le_maxr`, `le_maxl`, `lt_maxr`, `lt_maxl`, `minxK`, `minKx`,
    `maxxK`, `maxKx`, `max_minl`, `min_maxl`, `max_minr`, `min_maxr`
- in `order.v`:
  + in module `NatOrder`, added `nat_display` (instead of the now removed `total_display`)
  + in module `BoolOrder`, added `bool_display` (instead of the now removed `total_display`)
- in `ssrnum.v`, theory about min anx max:
  + Lemmas: `real_oppr_max`, `real_oppr_min`, `real_addr_minl`, `real_addr_minr`,
    `real_addr_maxl`, `real_addr_maxr`, `minr_pmulr`, `maxr_pmulr`, `real_maxr_nmulr`,
    `real_minr_nmulr`, `minr_pmull`, `maxr_pmull`, `real_minr_nmull`, `real_maxr_nmull`,
    `real_maxrN`, `real_maxNr`, `real_minrN`, `real_minNr`
- in `ssrnum.v`,
  + new lemma: `comparable0r`
  + in module `NumIntegralDomainTheory`:
    ```
    Definition minr x y := if x <= y then x else y.
    Definition maxr x y := if x <= y then y else x.
    ```
- in `fintype.v`, new lemmas: `seq_sub_default`, `seq_subE`

### Changed

- in `order.v`, `le_xor_gt`, `lt_xor_ge`, `compare`, `incompare`, `lel_xor_gt`,
  `ltl_xor_ge`, `comparel`, `incomparel` have more parameters
  + the following now deal with `min` and `max`
    * `comparable_ltgtP`, `comparable_leP`, `comparable_ltP`, `comparableP`
    * `lcomparableP`, `lcomparable_ltgtP`, `lcomparable_leP`, `lcomparable_ltP`, `ltgtP`
- in `order.v`:
  + `[arg minr_(i < i0 | P) M]` now for `porderType` (was for `orderType`)
- in `ssrnum.v`, `maxr` is a notation for `(@Order.max ring_display _)` (was `Order.join`)
  (resp. `minr` is a notation for `(@Order.min ring_display _)`)
- in `ssrnum.v`, `ler_xor_gt`, `ltr_xor_ge`, `comparer`,
  `ger0_xor_lt0`, `ler0_xor_gt0`, `comparer0` have now more parameters
  + the following now deal with min and max:
    * `real_leP`, `real_ltP x y`, `real_ltgtP`, `real_ge0P`, `real_le0P`, `real_ltgt0P`
    * `lerP`, `ltrP`, `ltrgtP`, `ger0P`, `ler0P`, `ltrgt0P`
- in `ssrnum.v`:
  + `oppr_min` now restricted to the real subset
  + the following have been redefined (were before derived from
    `order.v` with `meet` and `join` lemmas):
    * `minrC`, `minrr`, `minr_l`, `minr_r`, `maxrC`, `maxrr`, `maxr_l`,
      `maxr_r`, `minrA`, `minrCA`, `minrAC`, `maxrA`, `maxrCA`, `maxrAC`
    * `eqr_minl`, `eqr_minr`, `eqr_maxl`, `eqr_maxr`, `ler_minr`, `ler_minl`,
      `ler_maxr`, `ler_maxl`, `ltr_minr`, `ltr_minl`, `ltr_maxr`, `ltr_maxl`
    * `minrK`, `minKr`, `maxr_minl`, `maxr_minr`, `minr_maxl`, `minr_maxr`

### Renamed

- The added theories of min and max cause the following renamings:
  + `ltexI` -> `(le_minr,lt_minr)`
  + `lteIx` -> `(le_minl,lt_minl)`
  + `ltexU` -> `(le_maxr,lt_maxr)`
  + `lteUx` -> `(le_maxl,lt_maxl)`
  + `lexU` -> `le_maxr`
  + `ltxU` -> `lt_maxr`
  + `lexU` -> `le_maxr`
- in `order.v`, in module `NatOrder`, renamings:
  + `meetEnat` -> `minEnat`, `joinEnat` -> `maxEnat`,
    `meetEnat` -> `minEnat`, `joinEnat` -> `maxEnat`

### Removed

- in `order.v`, removed `total_display` (was defining `max` using
  `join` and `min` using `meet`)
- in `order.v`, removed `minnE` and `maxnE`

### Infrastructure

### Misc
