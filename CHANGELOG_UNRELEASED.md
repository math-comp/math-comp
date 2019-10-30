# Changelog (unreleased)

To avoid having old PRs put changes into the wrong section of the CHANGELOG,
new entries now go to the present file as discussed
[here](https://github.com/math-comp/math-comp/wiki/Agenda-of-the-April-23rd-2019-meeting-9h30-to-12h30#avoiding-issues-with-changelog).

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

### Added

- Added a `void` notation for the `Empty_set` type of the standard library, the
  canonical injection `of_void` and its cancellation lemma `of_voidK`, and
  `eq`, `choice`, `count` and `fin` instances.

- Added fixpoint and cofixpoint constructions to `finset`: `fixset`,
  `cofixset` and `fix_order`, with a few theorems about them

- Added functions `tuple_of_finfun`, `finfun_of_tuple`, and their
  "cancellation" lemmas.

- Added theorems `totient_prime` and `Euclid_dvd_prod` in `prime.v`

- Added theorems `ffact_prod`, `prime_modn_expSn` and `fermat_little`
  in `binomial.v`

- Added theorems `flatten_map1`, `allpairs_consr`, and `mask_filter` in `seq.v`.

- Fintype theorems: `fintype0`, `card_le1P`, `mem_card1`,
  `card1P`, `fintype_le1P`, `fintype1`, `fintype1P`.

- Bigop theorems: `big_rmcond`, `bigD1_seq`,
  `big_enum_val_cond`, `big_enum_rank_cond`,
  `big_enum_val`, `big_enum_rank`, `big_set`.

- Arithmetic theorems in ssrnat and div:
  - some trivial results in ssrnat: `ltn_predl`, `ltn_predr`,
    `ltn_subr` and `predn_sub`,
  - theorems about `n <=/< p +/- m` and `m +/- n <=/< p`:
    `leq_psubRL`, `ltn_psubLR`, `leq_subRL`, `ltn_subLR`, `leq_subCl`,
    `leq_psubCr`, `leq_subCr`, `ltn_subCr`, `ltn_psubCl` and
    `ltn_subCl`,
  - some commutations between modulo and division: `modn_divl` and
    `divn_modl`,
  - theorems about the euclidean division of additions and subtraction,
     + without preconditions of divisibility: `edivnD`, `edivnB`,
       `divnD`, `divnB`, `modnD`, `modnB`,
     + with divisibility of one argument: `divnDMl`, `divnMBl`,
       `divnBMl`, `divnBl` and `divnBr`,
     + specialization of the former theorems for .+1 and .-1:
       `edivnS`, `divnS`, `modnS`, `edivn_pred`, `divn_pred` and
       `modn_pred`.

- Added map/parametricity theorems about `path`, `sort` and `sorted`:

- Added `mem2E` in `path.v`.

- Added `sort_rec1` and `sortE` to help inductive reasoning on `sort`.

- Added map/parametricity theorems about `path`, `sort`, and `sorted`:
  `homo_path`, `mono_path`, `homo_path_in`, `mono_path_in`,
  `homo_sorted`, `mono_sorted`, `map_merge`, `merge_map`, `map_sort`,
  `sort_map`, `sorted_map`, `homo_sorted_in`, `mono_sorted_in`.

- Added the theorem `perm_iota_sort` to express that the sorting of
  any sequence `s` is equal to a mapping of `iota 0 (size s)` to the
  nth elements of `s`, so that one can still reason on `nat`, even
  though the elements of `s` are not in an `eqType`.

- Added stability theorems about `merge` and `sort`: `sorted_merge`,
  `merge_stable_path`, `merge_stable_sorted`, `sorted_sort`, `sort_stable`,
  `filter_sort`, `mask_sort`, `sorted_mask_sort`, `subseq_sort`,
  `sorted_subseq_sort`, and `mem2_sort`.

- Lemmas `ltnNleqif`, `eq_leqif`, `eqTleqif` in `ssrnat`

- Lemmas `eqEtupe`, `tnthS` and `tnth_nseq` in `tuple`

- Ported `order.v` from the finmap library, which provides structures of ordered
  sets (`porderType`, `distrLatticeType`, `orderType`, etc.) and its theory.

### Changed

- `eqVneq` lemma is changed from `{x = y} + {x != y}` to
  `eq_xor_neq x y (y == x) (x == y)`, on which a case analysis performs
  simultaneous replacement of expressions of the form `x == y` and `y == x`
  by `true` or `false`, while keeping the ability to use it in the way
  it was used before.

- Generalized the `allpairs_catr` lemma to the case where the types of `s`,
  `t1`, and `t2` are non-`eqType`s in `[seq E | i <- s, j <- t1 ++ t2]`.

- Generalized `muln_modr` and `muln_modl` removing hypothesis `0 < p`.

- Generalized `sort` to non-`eqType`s (as well as `merge`,
  `merge_sort_push`, `merge_sort_pop`), together with all the lemmas
  that did not really rely on an `eqType`: `size_merge`, `size_sort`,
  `merge_path`, `merge_sorted`, `sort_sorted`, `path_min_sorted`
  (which statement was modified to remove the dependency in `eqType`),
  and `order_path_min`.

- `compare_nat` type family and `ltngtP` comparison predicate are changed
  from `compare_nat m n (m <= n) (n <= m) (m < n) (n < m) (n == m) (m == n)`
  to `compare_nat m n (n == m) (m == n) (n <= m) (m <= n) (n < m) (m < n)`,
  to make it tries to match subterms with `m < n` first, `m <= n`, then
  `m == n`.
  + The compatibility layer for the version 1.9 is provided as the
    `ssrnat.mc_1_9` module. One may compile proofs compatible with the version
    1.9 in newer versions by using this module.

- Reorganized the algebraic hierarchy and the theory of `ssrnum.v`.
  + `numDomainType` and `realDomainType` get inheritances respectively from
    `porderType` and `orderType`.
  + `normedZmodType` is a new structure for `numDomainType` indexed normed
    additive abelian groups.
  + `[arg minr_( i < n | P ) F]` and `[arg maxr_( i < n | P ) F]` notations are
    removed. Now `[arg min_( i < n | P ) F]` and `[arg max_( i < n | P ) F]`
    notations are defined in `nat_scope` (specialized for `nat`), `order_scope`
    (general one), and `ring_scope` (specialized for `ring_display`). Lemma
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
    * `minr_(l|r)` -> `meet_(l|r)`
    * `maxr_(l|r)` -> `join_(l|r)`
    * `arg_minrP` -> `arg_minP`
    * `arg_maxrP` -> `arg_maxP`
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
- The following naming inconsistencies have been fixed in `ssrnat.v`:
  + `homo_inj_lt(_in)` -> `inj_homo_ltn(in)`
  + `(inc|dec)r(_in)` -> `(inc|dev)n(_in)`

### Infrastructure

- `Makefile` now supports the `test-suite` and `only` targets. Currently,
  `make test-suite` will verify the implementation of mathematical structures
  and their inheritances of MathComp automatically, by using the `hierarchy.ml`
  utility. One can use the `only` target to build the sub-libraries of MathComp
  specified by the `TGTS` variable, e.g.,
  `make only TGTS="ssreflect/all_ssreflect.vo fingroup/all_fingroup.vo"`.

### Misc

