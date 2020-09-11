# Changelog (unreleased)

To avoid having old PRs put changes into the wrong section of the CHANGELOG,
new entries now go to the present file as discussed
[here](https://github.com/math-comp/math-comp/wiki/Agenda-of-the-April-23rd-2019-meeting-9h30-to-12h30#avoiding-issues-with-changelog).

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

### Added

- Added contraposition lemmas involving propositions: `contra_not`, `contraPnot`, `contraTnot`, `contraNnot`, `contraPT`, `contra_notT`, `contra_notN`, `contraPN`, `contraFnot`, `contraPF` and `contra_notF` in ssrbool.v and `contraPeq`, `contra_not_eq`, `contraPneq`, and `contra_neq_not` in eqtype.v
- Contraposition lemmas involving inequalities:
  + in `order.v`:
    `comparable_contraTle`, `comparable_contraTlt`, `comparable_contraNle`, `comparable_contraNlt`, `comparable_contraFle`, `comparable_contraFlt`,
    `contra_leT`, `contra_ltT`, `contra_leN`, `contra_ltN`, `contra_leF`, `contra_ltF`,
    `comparable_contra_leq_le`, `comparable_contra_leq_lt`, `comparable_contra_ltn_le`, `comparable_contra_ltn_lt`,
    `contra_le_leq`, `contra_le_ltn`, `contra_lt_leq`, `contra_lt_ltn`,
    `comparable_contra_le`, `comparable_contra_le_lt`, `comparable_contra_lt_le`, `comparable_contra_lt`,
    `contraTle`, `contraTlt`, `contraNle`, `contraNlt`, `contraFle`, `contraFlt`,
    `contra_leq_le`, `contra_leq_lt`, `contra_ltn_le`, `contra_ltn_lt`,
    `contra_le`, `contra_le_lt`, `contra_lt_le`, `contra_lt`,
    `contra_le_not`, `contra_lt_not`,
    `comparable_contraPle`, `comparable_contraPlt`, `comparable_contra_not_le`, `comparable_contra_not_lt`,
    `contraPle`, `contraPlt`, `contra_not_le`, `contra_not_lt`
  + in `ssrnat.v`:
    `contraTleq`, `contraTltn`, `contraNleq`, `contraNltn`, `contraFleq`, `contraFltn`,
    `contra_leqT`, `contra_ltnT`, `contra_leqN`, `contra_ltnN`, `contra_leqF`, `contra_ltnF`,
    `contra_leq`, `contra_ltn`, `contra_leq_ltn`, `contra_ltn_leq`,
    `contraPleq`, `contraPltn`, `contra_not_leq`, `contra_not_ltn`, `contra_leq_not`, `contra_ltn_not`
- in `ssralg.v`, new lemma `sumr_const_nat` and `iter_addr_0`
- in `ssrnum.v`, new lemma `ler_sum_nat`

- in `seq.v`, new lemmas: `take_uniq`, `drop_uniq`
- in `fintype.v`, new lemmas: `card_geqP`, `card_gt1P`, `card_gt2P`,
  `card_le1_eqP` (generalizes `fintype_le1P`),
- in `finset.v`, neq lemmas: `set_enum`, `cards_eqP`, `cards2P`
- in `fingraph.v`, new lemmas: `fcard_gt0P`, `fcard_gt1P`
- in `finset.v`, new lemmas: `properC`, `properCr`, `properCl`
- in `ssrnat.v`, new lemmas: `subn_minl`, `subn_maxl`
- in `ssrnat.v`, new lemma: `oddS`


- Added a factory `distrLatticePOrderMixin` in order.v to build a
  `distrLatticeType` from a `porderType`.

- in `bigop.v` new lemma `sig_big_dep`, analogous to `pair_big_dep`
  but with an additional dependency in the index types `I` and `J`.
- in `fintype.v` adds lemma `split_ordP`, a variant of `splitP` which
  introduces ordinal equalities between the index and
  `lshift`/`rshift`, rather than equalities in `nat`, which in some
  proofs makes the reasoning easier (cf `matrix.v`), especially
  together with the new lemma `eq_shift` (which is a multi-rule for new
  lemmas `eq_lshift`, `eq_rshift`, `eq_lrshift` and `eq_rlshift`).

- in `matrix.v` new definitions `is_diag_mx` and `is_trig_mx`
  characterizing respectively diagonal and lower triangular matrices.
  We provide the new lemmas `row_diag_mx`, `is_diag_mxP`, `diag_mxP`,
  `diag_mx_is_diag`, `mx0_is_diag`, `is_trig_mxP`,
  `is_diag_mx_is_trig`, `diag_mx_trig`, `mx0_is_trig`,
  `scalar_mx_is_diag`, `is_scalar_mx_is_diag`, `scalar_mx_is_trig` and
  `is_scalar_mx_is_trig`.
- in `matrix.v`, new lemmas `matrix_eq0`, `matrix0Pn`, `rV0Pn` and
  `cV0Pn` to characterize nonzero matrices and find a nonzero
  coefficient.
- in `mxalgebra.v`, completed the theory of `pinvmx` in corner cases,
  using lemmas: `mulmxVp`, `mulmxKp`, `pinvmxE`, `mulVpmx`,
  `pinvmx_free`, and `pinvmx_full`.

- in `poly.v`, new lemma `commr_horner`.
- in `seq.v`, new lemma `mkseqP` to abstract a sequence `s` with
  `mkseq f n`, where `f` and `n` are fresh variables.

- in `seq.v`, new high-order predicate `allrel r s` which
  asserts that a relation `r` holds on all pairs of elements of `s`, and
  + lemmas `allrel_map`, `allrelP` and `allrel0`.
  + lemmas `allrel1`, `allrel2` and `allrel_cons`,
    under assumptions of reflexivity and symmetry of `r`.
- in `mxpoly.v`, new lemmas `mxminpoly_minP` and `dvd_mxminpoly`.
- in `mxalgebra.v` new lemmas `row_base0`, `sub_kermx`, `kermx0` and
  `mulmx_free_eq0`.
- in `bigop.v` new lemma `reindex_omap` generalizes `reindex_onto`
  to the case where the inverse function to `h` is partial (i.e. with
  codomain `option J`, to cope with a potentially empty `J`.

- in `bigop.v` new lemma `bigD1_ord` takes out an element in the
  middle of a `\big_(i < n)` and reindexes the remainder using `lift`.

- in `fintype.v` new lemmas `eq_liftF` and `lift_eqF`.

- in `matrix.v` new predicate `mxOver S` qualified with `\is a`, and
  + new lemmas: `mxOverP`, `mxOverS`, `mxOver_const`, `mxOver_constE`,
    `thinmxOver`, `flatmxOver`, `mxOver_scalar`, `mxOver_scalarE`,
    `mxOverZ`, `mxOverM`, `mxOver_diag`, `mxOver_diagE`.
  + new canonical structures:
    * `mxOver S` is closed under addition if `S` is.
    * `mxOver S` is closed under negation if `S` is.
    * `mxOver S` is a sub Z-module if `S` is.
    * `mxOver S` is a semiring for square matrices if `S` is.
    * `mxOver S` is a subring for square matrices if `S` is.
- in `matrix.v` new lemmas about `map_mx`: `map_mx_id`, `map_mx_comp`,
  `eq_in_map_mx`, `eq_map_mx` and `map_mx_id_in`.
- in `matrix.v`, new lemmas `row_usubmx`, `row_dsubmx`, `col_lsubmx`,
  and `col_rsubmx`.
- in `seq.v` new lemmas `find_ltn`, `has_take`, `has_take_leq`,
  `index_ltn`, `in_take`, `in_take_leq`, `split_find_nth`,
  `split_find` and `nth_rcons_cat_find`.

- in `matrix.v` new lemma `mul_rVP`.

- in `matrix.v`:
  + new inductions lemmas: `row_ind`, `col_ind`, `mx_ind`, `sqmx_ind`,
    `ringmx_ind`, `trigmx_ind`, `trigsqmx_ind`, `diagmx_ind`,
    `diagsqmx_ind`.
  + missing lemma `trmx_eq0`
  + new lemmas about diagonal and triangular matrices: `mx11_is_diag`,
    `mx11_is_trig`, `diag_mx_row`, `is_diag_mxEtrig`, `is_diag_trmx`,
    `ursubmx_trig`, `dlsubmx_diag`, `ulsubmx_trig`, `drsubmx_trig`,
    `ulsubmx_diag`, `drsubmx_diag`, `is_trig_block_mx`,
    `is_diag_block_mx`, and `det_trig`.

- in `mxpoly.v` new lemmas `horner_mx_diag`, `char_poly_trig`,
   `root_mxminpoly`, and `mxminpoly_diag`
- in `mxalgebra.v`, new lemma `sub_sums_genmxP` (generalizes `sub_sumsmxP`).

- in `bigop.v` new lemma `big_uncond`. The ideal name is `big_rmcond`
  but it has just been deprecated from its previous meaning (see
  Changed section) so as to reuse it in next mathcomp release.

- in `bigop.v` new lemma `big_uncond_in` is a new alias of
  `big_rmcond_in` for the sake of uniformity, but it is already
  deprecated and will be removed two releases from now.

- in `eqtype.v` new lemmas `contra_not_neq`, `contra_eq_not`.
- in `order.v`, new notations `0^d` and `1^d` for bottom and top elements of
  dual lattices.
- in `interval.v`:
  + Intervals and their bounds of `T` now have canonical ordered type instances
    whose ordering relations are the subset relation and the left to right
    ordering respectively. They form partially ordered types if `T` is a
    `porderType`. If `T` is a `latticeType`, they also form `tbLatticeType`
    where the join and meet are intersection and convex hull respectively. If
    `T` is an `orderType`, they are distributive, and the interval bounds are
    totally ordered. (cf Changed section)
  + New lemmas: `comparable_lteifN`, `itv_total_meet3E`, `itv_total_join3E`,
    `itv_total_meetsE`, `itv_total_joinsE`

- in `matrix.v` new lemma `det_mx11`.

### Changed

- in ssrbool.v, use `Reserved Notation` for `[rel _ _ : _ | _]` to avoid warnings with coq-8.12
- in `ssrAC.v`, fix `non-reversible-notation` warnings

- In the definition of structures in order.v, displays are removed from
  parameters of mixins and fields of classes internally and now only appear in
  parameters of structures. Consequently, each mixin is now parameterized by a
  class rather than a structure, and the corresponding factory parameterized by
  a structure is provided to replace the use of the mixin. These factories have
  the same names as in the mixins before this change except that `bLatticeMixin`
  and `tbLatticeMixin` have been renamed to `bottomMixin` and `topMixin`
  respectively.

- The `dual_*` notations such as `dual_le` in order.v are now qualified with the
  `Order` module.

- Lemma `big_rmcond` is deprecated and has been renamed
  `big_rmcomd_in` (and aliased `big_uncond_in`, see Added). The
  variant which does not require an `eqType` is currently named
  `big_uncond` (cf Added) but it will be renamed `big_mkcond` in the
  next release.
- Added lemma `ord1` in `fintype`, it is the same as `zmodp.ord1`,
  except `fintype.ord1` does not rely on `'I_n` zmodType structure.


- in `order.v`, `\join^d_` and `\meet^d_` notations are now properly specialized
  for `dual_display`.
- in `interval.v`:
  + Many definitions and lemmas on intervals such as the membership test are
    generalized from numeric domains to ordered types.
  + `x <= y ?< if c` (`lersif`) has also been generalized to `porderType` and
    replaced with `x < y ?<= if c'` (`lteif`) where `c'` is negation of `c`.
  + Interval bounds `itv_bound : T -> Type` are redefined with two constructors
    `BRight_if of bool & T` and `BRInfty_if of bool`. `BRight_if true x` and
    `BRight_if close x` respectively mean open and close bounds as left bounds,
    and their meanings as right bounds are opposite. `BRInfty_if true` and
    `BRInfty_if false` respectively means positive and negative infinity. This
    change gives us the canonical "left to right" ordering of interval bounds.

### Renamed

- `big_rmcond` -> `big_rmcond_in` (cf Changed section)

- in `interval.v`, we deprecate and rename the following:
  + `subr_lersif(r0|0r|0)` -> `subr_lteif(r0|0r|0)`
  + `lersif_(trans|anti)` -> `lteif_(trans|anti)`
  + `lersif(01|xx|NF|S|T|F|W)` -> `lteif(01|xx|NF|S|T|F|W)`
  + `lersif_(oppl|oppr|0oppr|oppr0|opp2|oppE)` -> `lteif_(oppl|oppr|0oppr|oppr0|opp2|oppE)`
  + `lersif_add2(|l|r)` -> `lteif_add2(|l|r)`
  + `lersif_sub(l|r)_add(l|r)` -> `lteif_sub(l|r)_add(l|r)`
  + `lersif_sub_add(l|r)` -> `lteif_sub_add(l|r)`
  + `lersif_(andb|orb|imply)` -> `lteif_(andb|orb|imply)`
  + `ltrW_lersif` -> `ltrW_lteif`
  + `lersif_(p|n)mul2(l|r)` -> `lteif_(p|n)mul2(l|r)`
  + `real_lersifN` -> `real_lteifN`
  + `real_lersif_norm(l|r)` -> `real_lteif_norm(l|r)`
  + `lersif_nnormr` -> `lteif_nnormr`
  + `lersifN` -> `lteifN`
  + `lersif_norm(l|r)` -> `lteif_norm(l|r)`
  + `lersif_distl` -> `lteif_distl`
  + `lersif_(min|max)(l|r)` -> ` lteif_(min|max)(l|r)`
  + `lersif_(p|n)div(l|r)_mul(l|r)` -> `lteif_(p|n)div(l|r)_mul(l|r)`
  + `lersif_in_itv` -> `lteif_in_itv`
  + `itv_intersection` -> `Order.meet`
  + `itv_intersection1i` -> `meet1x`
  + `itv_intersectioni1` -> `meetx1`
  + `itv_intersectionii` -> `meetxx`
  + `itv_intersectionC` -> `meetC`
  + `itv_intersectionA` -> `meetA`

### Removed

### Infrastructure

### Misc
