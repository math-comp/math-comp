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

- in `path.v`, new lemmas: `sorted_pairwise(_in)`, `path_pairwise(_in)`,
  `cycle_all2rel(_in)`, `pairwise_sort`, and `sort_pairwise_stable`.

- in `tuple.v`, added Canonical tuple for sort.

- in `interval.v`, new lemmas: `ge_pinfty`, `le_ninfty`, `gt_pinfty`, `lt_ninfty`.

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

- new file `mxred.v` which contains the theory of diagonalization. To
  that effect, we define `conjmx`, `restrictmx`, `similar_to`,
  `similar`, `similar_in`, `similar_in_to`, `all_similar_to`,
  `similar_diag`, `diagonalizable_in`, `diagonalizable`,
  `codiagonalizable_in`, `codiagonalizable`, `similar_trig`,
  `trigonalizable_in`, `trigonalizable`, `cotrigonalizable_in`, and
  `cotrigonalizable`; and their theory: `stablemx_comp`,
  `stablemx_restrict`, `conjmxM`, `conjMmx`, `conjuMmx`, `conjMumx`,
  `conjuMumx`, `conjmx_scalar`, `conj0mx`, `conjmx0`, `conjumx`,
  `conj1mx`, `conjVmx`, `conjmxK`, `conjmxVK`, `horner_mx_conj`,
  `horner_mx_uconj`, `horner_mx_uconjC`, `mxminpoly_conj`,
  `mxminpoly_uconj`, `sub_kermxpoly_conjmx`, `sub_eigenspace_conjmx`,
  `eigenpoly_conjmx`, `eigenvalue_conjmx`, `conjmx_eigenvalue`,
  `similarPp`, `similarW`, `similarP`, `similarRL`, `similarLR`,
  `similar_mxminpoly`, `similar_diag_row_base`, `similar_diagPp`,
  `similar_diagP`, `similar_diagPex`, `similar_diagLR`,
  `similar_diag_mxminpoly`, `similar_diag_sum`, `codiagonalizable1`,
  `codiagonalizable_on`, `diagonalizable_diag`,
  `diagonalizable_scalar`, `diagonalizable0`, `diagonalizablePeigen`,
  `diagonalizableP`, `diagonalizable_conj_diag`, and
  `codiagonalizableP`.

Remark that even though `trigonalization` is defined, its theory is
not here yet.

### Changed

- In `ssralg.v` and `ssrint.v`, the nullary ring notations `-%R`, `+%R`, `*%R`,
  `*:%R`, and `*~%R` are now declared in `fun_scope`.

- across the library, the deprecation mechanism to use has been changed from the
  `deprecate` notation to the `deprecated` attribute (cf. Removed section).

### Renamed

- in `path.v`,
  + `sub_(path|cycle|sorted)_in` -> `sub_in_(path|cycle|sorted)`
  + `eq_(path|cycle)_in` -> `eq_in_(path|cycle)`

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

### Infrastructure

### Misc
