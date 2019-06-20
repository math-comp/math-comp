# Changelog (unreleased)

To avoid having old PRs put changes into the wrong section of the CHANGELOG,
new entries now go to the present file as discussed
[here](https://github.com/math-comp/math-comp/wiki/Agenda-of-the-April-23rd-2019-meeting-9h30-to-12h30#avoiding-issues-with-changelog).

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

### Added

- Added fixpoint and cofixpoint constructions to `finset`: `fixset`,
  `cofixset` and `fix_order`, with a few theorems about them

- Added functions `tuple_of_finfun`, `finfun_of_tuple`, and their
  "cancellation" lemmas.

- Added theorem `totient_prime` in `prime.v`

- Ported `order.v` from the finmap library, which provides structures of ordered
  sets (`porderType`, `latticeType`, `orderType`, etc.) and its theory.


### Changed

- `eqVneq` lemma is changed from `{x = y} + {x != y}` to
  `eq_xor_neq x y (y == x) (x == y)`, on which a case analysis performs
  simultaneous replacement of expressions of the form `x == y` and `y == x`
  by `true` or `false`, while keeping the ability to use it in the way
  it was used before.

- Reorganized the algebraic hierarchy and the theory of `ssrnum.v`.
  + `numDomainType` and `realDomainType` get inheritances respectively from
    `porderType` and `orderType`.
  + `normedDomainType` is a new structure for `numDomainType` indexed normed
    integral domains.
  + `[arg minr_( i < n | P ) F]` and `[arg maxr_( i < n | P ) F]` notations are
    removed. Now `[arg min_( i < n | P ) F]` and `[arg max_( i < n | P ) F]`
    notations are defined in `nat_scope` (specialized for `nat`), `order_scope`
    (general one), and `ring_scope` (specialized for `ring_display`).
    `fintype.arg_minP` is aliased to `arg_minnP` and the same for `arg_maxnP`.
  + The following lemmas are generalized, renamed, and relocated to `order.v`:
    * `ltr_def` -> `lt_def`
    * `(ger|gtr)E` -> `(ge|gt)E`
    * `(le|lt|lte)rr` -> `(le|lt|lte)xx`
    * `ltrW` -> `ltW`
    * `ltr_neqAle` -> `lt_neqAle`
    * `ler_eqVlt` -> `le_eqVlt`
    * `(gtr|ltr)_eqF` -> `(gt|lt)_eqF`
    * `ler_anti`, `ler_asym` -> `le_anti`
    * `eqr_le` -> `eq_le`
    * `(ltr|ler_lt|ltr_le|ler)_trans` -> `(lt|le_lt|lt_le|le)_trans`
    * `lerifP` -> `leifP`
    * `(ltr|ltr_le|ler_lt)_asym` -> `(lt|lt_le|le_lt)_asym`
    * `lter_anti` -> `lte_anti`
    * `ltr_geF` -> `lt_geF`
    * `ler_gtF` -> `le_gtF`
    * `ltr_gtF` -> `lt_gtF`
    * `lt(r|nr|rn)W_(n)homo(_in)` -> `ltW_(n)homo(_in)`
    * `inj_(n)homo_lt(r|nr|rn)(_in)` -> `inj_(n)homo_lt(_in)`
    * `(inc|dec)(r|nr|rn)_inj(_in)` -> `(inc_dec)_inj(_in)`
    * `le(r|nr|rn)W_(n)mono(_in)` -> `leW_(n)mono(_in)`
    * `lenr_(n)mono(_in)` -> `le_(n)mono(_in)`
    * `lerif_(refl|trans|le|eq)` -> `leif_(refl|trans|le|eq)`
    * `(ger|ltr)_lerif` -> `(ge|lt)_leif`
    * `(n)mono(_in)_lerif` -> `(n)mono(_in)_leif`
    * `(ler|ltr)_total` -> `(le|lt)_total`
    * `wlog_(ler|ltr)` -> `wlog_(le|lt)`
    * `ltrNge` -> `ltNge`
    * `lerNgt` -> `leNgt`
    * `neqr_lt` -> `neq_lt`
    * `eqr_(le|lt)(LR|RL)` -> `eq_(le|lt)(LR|RL)`
    * `eqr_(min|max)(l|r)` -> `eq_(meet|join)(l|r)`
    * `ler_minr` -> `lexI`
    * `ler_minl` -> `leIx`
    * `ler_maxr` -> `lexU`
    * `ler_maxl` -> `leUx`
    * `lt(e)r_min(r|l)` -> `lt(e)(xI|Ix)`
    * `lt(e)r_max(r|l)` -> `lt(e)(xU|Ux)`
    * `minrK` -> `meetUKC`
    * `minKr` -> `joinKIC`
    * `maxr_min(l|r)` -> `joinI(l|r)`
    * `minr_max(l|r)` -> `meetU(l|r)`
    * `minrP`, `maxrP` -> `leP`, `ltP`
    * `(minr|maxr)(r|C|A|CA|AC)` -> `(meet|join)(xx|C|A|CA|AC)`
    * `minr_l` -> `elimT meet_idPl`
    * `minr_r` -> `elimT meet_idPr`
    * `maxr_l` -> `elimT join_idPr`
    * `maxr_r` -> `elimT join_idPl`
    * `arg_minrP` -> `arg_minP`
    * `arg_maxrP` -> `arg_maxP`
  + The following naming inconsistencies have been fixed in `ssrnat`:
    * `homo_inj_lt(_in)` -> `inj_homo_ltn(in)`
    * `incr(_in)` -> `incn(_in)`
    * `decr(_in)` -> `decn(_in)`
  + Generalized the following lemmas as properties of `normedDomainType`:
    `normr0`, `normr0P`, `normr_eq0`, `distrC`, `normr_id`, `normr_ge0`,
    `normr_le0`, `normr_lt0`, `normr_gt0`, `normrE`, `normr_real`,
    `ler_norm_sum`, `ler_norm_sub`, `ler_dist_add`, `ler_sub_norm_add`,
    `ler_sub_dist`, `ler_dist_dist`, `ler_dist_norm_add`, `ler_nnorml`,
    `ltr_nnorml`, `lter_nnormr`.
  + The compatibility layer for the version 1.9 is provided as the
    `ssrnum.mc_1_9` module. One may compile proofs compatible with the version
    1.9 in newer versions by using the `mc_1_9.Num` module instead of the `Num`
    module. However, instances of the number structures may require changes.

### Renamed

- `real_lerP` -> `real_leP`
- `real_ltrP` -> `real_ltP`
- `real_ltrNge` -> `real_ltNge`
- `real_lerNgt` -> `real_leNgt`
- `real_ltrgtP` -> `real_ltgtP`
- `real_ger0P` -> `real_ge0P`
- `real_ltrgt0P` -> `real_ltgt0P`
- `lerif_nat` -> `leif_nat_r`
- Replaced `lerif` with `leif` in the following names of lemmas:
  + `lerif_subLR`, `lerif_subRL`, `lerif_add`, `lerif_sum`, `lerif_0_sum`,
    `real_lerif_norm`, `lerif_pmul`, `lerif_nmul`, `lerif_pprod`,
    `real_lerif_mean_square_scaled`, `real_lerif_AGM2_scaled`,
    `lerif_AGM_scaled`, `real_lerif_mean_square`, `real_lerif_AGM2`,
    `lerif_AGM`, `relif_mean_square_scaled`, `lerif_AGM2_scaled`,
    `lerif_mean_square`, `lerif_AGM2`, `lerif_normC_Re_Creal`, `lerif_Re_Creal`,
    `lerif_rootC_AGM`.

### Misc

