# Changelog (unreleased)

To avoid having old PRs put changes into the wrong section of the CHANGELOG,
new entries now go to the present file as discussed
[here](https://github.com/math-comp/math-comp/wiki/Agenda-of-the-April-23rd-2019-meeting-9h30-to-12h30#avoiding-issues-with-changelog).

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

### Added

- in `bigop.v`, added lemma `sumnB`.

- in `seq.v`,
  + new higher-order predicate `pairwise r xs` which asserts that the relation
    `r` holds for any i-th and j-th element of `xs` such that i < j.
  + new lemmas `allrel_mask(l|r)`, `allrel_filter(l|r)`, `sub(_in)_allrel`,
    `pairwise_cons`, `pairwise_cat`, `pairwise_rcons`, `pairwise2`,
    `pairwise_mask`, `pairwise_filter`, `pairwiseP`, `pairwise_all2rel`,
    `sub(_in)_pairwise`, `eq(_in)_pairwise`, `pairwise_map`, `subseq_pairwise`,
    `uniq_pairwise`, `pairwise_uniq`, and `pairwise_eq`.
  + new lemmas `zip_map`, `eqseq_all`, and `eq_map_all`.
  + new lemmas `count_undup`, `eq_count_undup`, `rev_take`,
    `rev_drop`, `takeEmask`, `dropEmask`, `filter_iota_ltn`,
    `filter_iota_leq`, `map_nth_iota0` and `map_nth_iota`
  + new lemmas `cat_nilp`, `rev_nilp`, `allrelT`, `allrel_relI`, and
    `pairwise_relI`.

- in `path.v`, new lemmas: `sorted_pairwise(_in)`, `path_pairwise(_in)`,
  `cycle_all2rel(_in)`, `pairwise_sort`, and `sort_pairwise_stable`.
  + new lemmas `cat_sorted2`, `path_le`, `take_path`, `take_sorted`,
    `drop_sorted`, `undup_path`, `undup_sorted`, `count_merge`,
    `eq_count_merge`

- in `path.v`, new lemmas: `pairwise_sorted`, `path_relI`, `cycle_relI`,
  `sorted_relI`, `eq(_in)_sorted`, `mergeA`, `all_merge`, and
  `homo_sort_map(_in)`.

- in `tuple.v`, added Canonical tuple for sort.

- in `interval.v`, new lemmas: `ge_pinfty`, `le_ninfty`, `gt_pinfty`, `lt_ninfty`.

- in `finset.v`, new lemmas: `bigcup0P`, `bigcup_disjointP`, `imset_cover`,
  `cover1`, `trivIset1`, `trivIsetD`, `trivIsetU`, `coverD1`, `partition0`,
  `partiton_neq0`, `partition_trivIset`, `partitionS`, `partitionD1`,
  `partitionU1`, `partition_set0`, `partition_pigeonhole`, `indexed_partition`,
  `imset_inj`, `imset_disjoint`, `imset_trivIset`, `imset0mem`,
  `imset_partition`.

- in `order.v`
  + we provide a canonical total order on ordinals and lemmas
    `leEord`, `ltEord`, `botEord`, and `topEord` to translate generic
    symbols to the concrete ones. Because of a shortcoming of the
    current interface, which requires `finOrderType` structures to be
    nonempty, the `finOrderType` is only defined for ordinal which are
    manifestly nonempty (i.e. `'I_n.+1`).
  + new notation `Order.enum A` for `sort <=%O (enum A)`, with new
    lemmas in module `Order`: `cardE`, `mem_enum`, `enum_uniq`,
    `cardT`, `enumT`, `enum0`, `enum1`, `eq_enum`, `eq_cardT`,
    `set_enum`, `enum_set0`, `enum_setT`, `enum_set1`, `enum_ord`,
    `val_enum_ord`, `size_enum_ord`, `nth_enum_ord`, `nth_ord_enum`,
    `index_enum_ord`, `mono_sorted_enum`, and `mono_unique`.
  + a new module `Order.EnumVal` (which can be imported locally), with
    definitions `enum_rank_in`, `enum_rank`, `enum_val` on a finite
    partially ordered type `T`, which are the same as the one from
    `fintype.v`, except they are monotonous when `Order.le T` is
    total. We provide the following lemmas: `enum_valP`,
    `enum_val_nth`, `nth_enum_rank_in`, `nth_enum_rank`,
    `enum_rankK_in`, `enum_rankK`, `enum_valK_in`, `enum_valK`,
    `enum_rank_inj`, `enum_val_inj`, `enum_val_bij_in`,
    `eq_enum_rank_in`, `enum_rank_in_inj`, `enum_rank_bij`,
    `enum_val_bij`, `le_enum_val`, `le_enum_rank_in`, and
    `le_enum_rank`.  They are all accessible via module `Order` if one
    chooses not to import `Order.EnumVal`.
  + a new module `tagnat` which provides a monotonous bijection
    between the finite ordered types `{i : 'I_n & 'I_(p_ i)}`
    (canonically ordered lexicographically), and `'I_(\sum_i p_ i)`,
    via the functions `sig` and `rank`. We provide direct access to
    the components of the former type via the functions `sig1`, `sig2`
    and `Rank`. We provide the following lemmas on these definitions:
    `card`, `sigK`, `sig_inj`, `rankK`, `rank_inj`, `sigE12`,
    `rankE`, `sig2K`, `Rank1K`, `Rank2K`, `rank_bij`, `sig_bij `,
    `rank_bij_on`, `sig_bij_on`, `le_sig`, `le_sig1`, `le_rank`,
    `le_Rank`, `lt_sig`, `lt_rank`, `lt_Rank`, `eq_Rank`, `rankEsum`,
    `RankEsum`, `rect`, and `eqRank`.
  + lemmas `joins_le` and `meets_ge`.
  + new lemmas `le_sorted_ltn_nth`, `le_sorted_leq_nth`,
    `lt_sorted_leq_nth`, `lt_sorted_ltn_nth`, `filter_lt_nth`,
    `count_lt_nth`, `filter_le_nth`, `count_le_nth`,
    `count_lt_le_mem`, `sorted_filter_lt`, `sorted_filter_le`,
    `nth_count_le`, `nth_count_lt`, `count_le_gt`,
    `count_lt_ge`, `sorted_filter_gt`, `sorted_filter_ge`,
    `nth_count_ge`, `nth_count_lt` and `nth_count_eq`
  + new lemmas `(le|lt)_path_min`, `(le|lt)_path_sortedE`,
    `(le|lt)_(path|sorted)_pairwise`, `(le|lt)_(path|sorted)_(mask|filter)`,
    `subseq_(le|lt)_(path|sorted)`, `lt_sorted_uniq`, `sort_lt_id`,
    `perm_sort_leP`, `filter_sort_le`, `(sorted_)(mask|subseq)_sort_le`,
    `mem2_sort_le`.

- in `matrix.v`, seven new definitions:
  + `mxblock`, `mxcol`, `mxrow` and `mxdiag` with notations
    `\mxblock_(i < m, j < n) B_ i j`, `\mxcol_(i < m) B_ i`,
    `\mxrow_(j < n) B_ j`, and `\mxdiag_(i < n) B_ i` (and variants
    without explicit `< n`), to form big matrices described by blocks.
  + `submxblock`, `submxcol` and `submxrow` to extract blocks from the
    former constructions. There is no analogous for `mxdiag` because
    one can simply apply `submxblock A i i`.
  + We provide the following lemmas on these definitions:
    `mxblockEh`, `mxblockEv`, `submxblockEh`, `submxblockEv`,
    `mxblockK`, `mxrowK`, `mxcolK`, `submxrow_matrix`,
    `submxcol_matrix`, `submxblockK`, `submxrowK`, `submxcolK`,
    `mxblockP`, `mxrowP`, `mxcolP`, `eq_mxblockP`, `eq_mxblock`,
    `eq_mxrowP`, `eq_mxrow`, `eq_mxcolP`, `eq_mxcol`, `row_mxrow`,
    `col_mxrow`, `row_mxcol`, `col_mxcol`, `row_mxblock`,
    `col_mxblock`, `tr_mxblock`, `tr_mxrow`, `tr_mxcol`,
    `tr_submxblock`, `tr_submxrow`, `tr_submxcol`, `mxsize_recl`,
    `mxrow_recl`, `mxcol_recu`, `mxblock_recl`, `mxblock_recu`,
    `mxblock_recul`, `mxrowEblock`, `mxcolEblock`, `mxEmxrow`,
    `mxEmxcol`, `mxEmxblock`, `mxrowD`, `mxrowN`, `mxrowB`, `mxrow0`,
    `mxrow_const`, `mxrow_sum`, `submxrowD`, `submxrowN`, `submxrowB`,
    `submxrow0`, `submxrow_sum`, `mul_mxrow`, `mul_submxrow`,
    `mxcolD`, `mxcolN`, `mxcolB`, `mxcol0`, `mxcol_const`,
    `mxcol_sum`, `submxcolD`, `submxcolN`, `submxcolB`, `submxcol0`,
    `submxcol_sum`, `mxcol_mul`, `submxcol_mul`, `mxblockD`,
    `mxblockN`, `mxblockB`, `mxblock0`, `mxblock_const`,
    `mxblock_sum`, `submxblockD`, `submxblockN`, `submxblockB`,
    `submxblock0`, `submxblock_sum`, `mul_mxrow_mxcol`,
    `mul_mxcol_mxrow`, `mul_mxrow_mxblock`, `mul_mxblock_mxrow`,
    `mul_mxblock`, `is_trig_mxblockP`, `is_trig_mxblock`,
    `is_diag_mxblockP`, `is_diag_mxblock`, `submxblock_diag`,
    `eq_mxdiagP`, `eq_mxdiag`, `mxdiagD`, `mxdiagN`, `mxdiagB`,
    `mxdiag0`, `mxdiag_sum`, `tr_mxdiag`, `row_mxdiag`, `col_mxdiag`,
    `mxdiag_recl`, `mxtrace_mxblock`, `mxdiagZ`, `diag_mxrow`,
    `mxtrace_mxdiag`, `mul_mxdiag_mxcol`, `mul_mxrow_mxdiag`,
    `mul_mxblock_mxdiag`, and `mul_mxdiag_mxblock`.
   + adding missing lemmas `trmx_conform` and `eq_castmx`.

- in `mxalgegra.v`,
  + Lemmas about rank of block matrices with `0`s inside
    `rank_col_mx0`, `rank_col_0mx`, `rank_row_mx0`, `rank_row_0mx`,
    `rank_diag_block_mx`, and `rank_mxdiag`.
  + we provide an equality of spaces `eqmx_col` between `\mxcol_i V_
    i` and the sum of spaces `\sum_i <<V_ i>>)%MS`.

- in `bigop.v`:
  + Lemmas `big_nat_widenl`, `big_geq_mkord`
- in `ssrint.v`,
  + Lemmas: `mulr_absz`, `natr_absz`, `lez_abs`

- In `ssralg.v`
  + new lemma `fmorph_eq`
  + Canonical additive, linear and rmorphism for `fst` and `snd`

- In `rat.v`
  + new lemmas `minr_rat`, `maxr_rat`

- In `intdiv.v`
  + new definition `lcmz`
  + new lemmas `dvdz_lcmr`, `dvdz_lcml`, `dvdz_lcm`, `lcmzC`, `lcm0z`,
    `lcmz0`, `lcmz_ge0`, `lcmz_neq0`
  + new lemma `lez_pdiv2r`

- In `ssrnum.v`:
  + new lemma `eqNr`
- Added intro pattern ltac views for rewrite:
  `/[1! rules]`, `/[! rules]`.


- In `mxpoly.v`: developed the theory of diagonalization. To that
  effect, we define `conjmx`, `restrictmx`, and notations `A ~_P B`,
  `A ~_P {in S'}`, `A ~_{in S} B`, `A ~_{in S} {in S'}`,
  `all_simmx_in`, `diagonalizable_for`, `diagonalizable_in`,
  `diagonalizable`, `codiagonalizable_in`, and `codiagonalizable`; and
  their theory: `stablemx_comp`, `stablemx_restrict`, `conjmxM`,
  `conjMmx`, `conjuMmx`, `conjMumx`, `conjuMumx`, `conjmx_scalar`,
  `conj0mx`, `conjmx0`, `conjumx`, `conj1mx`, `conjVmx`, `conjmxK`,
  `conjmxVK`, `horner_mx_conj`, `horner_mx_uconj`, `horner_mx_uconjC`,
  `mxminpoly_conj`, `mxminpoly_uconj`, `sub_kermxpoly_conjmx`,
  `sub_eigenspace_conjmx`, `eigenpoly_conjmx`, `eigenvalue_conjmx`,
  `conjmx_eigenvalue`, `simmxPp`, `simmxW`, `simmxP`, `simmxRL`,
  `simmxLR`, `simmx_minpoly`, `diagonalizable_for_row_base`,
  `diagonalizable_forPp`, `diagonalizable_forP`,
  `diagonalizable_forPex`, `diagonalizable_forLR`,
  `diagonalizable_for_mxminpoly`, `diagonalizable_for_sum`,
  `codiagonalizable1`, `codiagonalizable_on`, `diagonalizable_diag`,
  `diagonalizable_scalar`, `diagonalizable0`, `diagonalizablePeigen`,
  `diagonalizableP`, `diagonalizable_conj_diag`, and
  `codiagonalizableP`.

- in `bigop.v`, added lemma `big_bool`.

### Changed

- In `ssralg.v` and `ssrint.v`, the nullary ring notations `-%R`, `+%R`, `*%R`,
  `*:%R`, and `*~%R` are now declared in `fun_scope`.

- across the library, the deprecation mechanism to use has been changed from the
  `deprecate` notation to the `deprecated` attribute (cf. Removed section).

- in `finalg.v`, `finFieldType` now inherits from `countDecFieldType`.

### Renamed

- in `path.v`,
  + `sub_(path|cycle|sorted)_in` -> `sub_in_(path|cycle|sorted)`
  + `eq_(path|cycle)_in` -> `eq_in_(path|cycle)`

- in `order.v`
  + `join_(|sup_|min_)seq` -> `joins_(|sup_|min_)seq`
  + `meet_(|sup_|min_)seq` -> `meets_(|sup_|min_)seq`
  + `join_(sup|min)` -> `joins_(sup|min)`

- in `matrix.v`, `card_matrix` -> `card_mx`

- in `ssralg.v`, `prodr_natmul` ->  `prodrMn`

- in `bigop.v`, `big_uncond` -> ` big_rmcond`

- in `finset`
  + `mem_imset_eq`  -> `mem_imset`
  + `mem_imset2_eq` -> `mem_imset2`

### Removed

- in `ssreflect.v`, the `deprecate` notation has been deprecated. Use the
  `deprecated` attribute instead (cf. Changed section).

- in `seq.v`, `iota_add` has been deprecated. Use `iotaD` instead.

- in `ssrnat.v` and `ssrnum.v`, deprecation aliases and the `mc_1_10`
  compatibility modules introduced in MathComp 1.11+beta1 have been removed.

- in `seq.v`, remove the following deprecation aliases introduced in MathComp
  1.9.0: `perm_eq_rev`, `perm_eq_flatten`, `perm_eq_all`, `perm_eq_small`,
  `perm_eq_nilP`, `perm_eq_consP`, `leq_size_perm`, `uniq_perm_eq`,
  `perm_eq_iotaP`, and `perm_undup_count`.

- in `path.v`, remove the deprecation aliases `eq(_in)_sorted` introduced in
  MathComp 1.12.0. These names of lemmas are now taken by new lemmas
  (cf. Added section).

- in `order.v`, remove the deprecation aliases `eq_sorted_(le|lt)`.

### Infrastructure

- The way `hierachy.ml` recognizes inheritance has been changed: `S1` inherits
  from `S2` when there is a coercion path from `S1.sort` to `S2.sort` and there
  is a canonical structure instance that unifies `S1.sort` and `S2.sort`,
  regardless of where (which module) these constants are declared.
  As a result, it recognizes non-forgetful inheritance and checks the uniqueness
  of join and exhaustiveness of canonical declarations involving it.

### Misc
