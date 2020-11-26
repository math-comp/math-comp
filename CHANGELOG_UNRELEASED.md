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
- in `ssralg.v`, new lemmas `iter_addr`, `iter_mulr`, `iter_mulr_1`, and `prodr_const_nat`.
- in `ssrnum.v`, new lemma `ler_sum_nat`
- in `ssrnum.v`, new lemmas `big_real`, `sum_real`, `prod_real`,
  `max_real`, `min_real`, `bigmax_real`, and `bigmin_real`.
- in `order.v`, new lemmas `comparable_bigl` and `comparable_bigr`.

- in `seq.v`, new lemmas: `take_uniq`, `drop_uniq`
- in `fintype.v`, new lemmas: `card_geqP`, `card_gt1P`, `card_gt2P`,
  `card_le1_eqP` (generalizes `fintype_le1P`),
- in `finset.v`, neq lemmas: `set_enum`, `cards_eqP`, `cards2P`
- in `fingraph.v`, new lemmas: `fcard_gt0P`, `fcard_gt1P`
- in `finset.v`, new lemmas: `properC`, `properCr`, `properCl`
- in `ssrnat.v`, new lemmas: `subn_minl`, `subn_maxl`
- in `ssrnat.v`, new lemma: `oddS`
- in `ssrnat.v`, new lemmas: `subnA`, `addnBn`, `addnCAC`, `addnACl`
- in `ssrnat.v`, new lemmas: `iterM`, `iterX`
- in `finset.v`, new lemmas: `mem_imset_eq`, `mem_imset2_eq`.
  These lemmas will lose the `_eq` suffix in the next release, when the shortende names will become available (cf. Renamed section)

- in `ssrbool.v`
  + generic lemmas about interaction between `{in _, _}` and `{on _,  _}`:
    `in_on1P`, `in_on1lP`, `in_on2P`, `on1W_in`, `on1lW_in`, `on2W_in`,
    `in_on1W`, `in_on1lW`, `in_on2W`, `on1S`, `on1lS`, `on2S`,
    `on1S_in`, `on1lS_in`, `on2S_in`, `in_on1S`, `in_on1lS`, `in_on2S`.
  + lemmas about interaction between `{in _, _}` and `sig`:
    `in1_sig`, `in2_sig`, and `in3_sig`.

- Added a factory `distrLatticePOrderMixin` in order.v to build a
  `distrLatticeType` from a `porderType`.

- Added intro pattern ltac views for dup, swap, apply:
  `/[apply]`, `/[swap]` and `/[dup]`.

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

- in `seq.v`, new high-order relation `allrel r xs ys` which asserts that
  `r x y` holds whenever `x` is in `xs` and `y` is in `ys`, new notation
  `all2rel r xs (:= allrel r xs xs)` which asserts that `r` holds on all
  pairs of elements of `xs`, and
  + lemmas `allrel0(l|r)`, `allrel_cons(l|r|2)`, `allrel1(l|r)`,
    `allrel_cat(l|r)`, `allrel_allpairsE`, `eq_in_allrel`, `eq_allrel`,
    `allrelC`, `allrel_map(l|r)`, `allrelP`,
  + lemmas `all2rel1`, `all2rel2`, and `all2rel_cons`
    under assumptions of symmetry of `r`.

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
- in `finset.v` new lemma `disjoints1`
- in `fintype.v` new lemmas: `disjointFr`, `disjointFl`, `disjointWr`, `disjointW`
- in `fintype.v`, new (pigeonhole) lemmas `leq_card_in`, `leq_card`,
  and `inj_leq`.

- in `matrix.v`, new definition `mxsub`, `rowsub` and `colsub`,
  corresponding to arbitrary submatrices/reindexation of a matrix.
  + We provide the theorems `x?(row|col)(_perm|')?Esub`, `t?permEsub`
    `[lrud]submxEsub`, `(ul|ur|dl|dr)submxEsub` for compatibility with
    ad-hoc submatrices/permutations.
  + We provide a new, configurable, induction lemma `mxsub_ind`.
  + We provide the basic theory `mxsub_id`, `eq_mxsub`, `eq_rowsub`,
    `eq_colsub`, `mxsub_eq_id`, `mxsub_eq_colsub`, `mxsub_eq_rowsub`,
    `mxsub_ffunl`, `mxsub_ffunr`, `mxsub_ffun`, `mxsub_const`,
    `mxsub_comp`, `rowsub_comp`, `colsub_comp`, `mxsubrc`, `mxsubcr`,
    `trmx_mxsub`, `row_mxsub`, `col_mxsub`, `row_rowsub`,
    `col_colsub`, and `map_mxsub`, `pid_mxErow` and `pid_mxEcol`.
  + Interaction with `castmx` through lemmas `rowsub_cast`,
    `colsub_cast`, `mxsub_cast`, and `castmxEsub`.
  + `(mx|row|col)sub` are canonically additive and linear.
  + Interaction with `mulmx` through lemmas `mxsub_mul`,
    `mul_rowsub_mx`, `mulmx_colsub`, and `rowsubE`.

- in `mxalgebra.v`, new lemma `rowsub_sub`, `eq_row_full`,
  `row_full_castmx`, `row_free_castmx`, `rowsub_comp_sub`,
  `submx_rowsub`, `eqmx_rowsub_comp_perm`, `eqmx_rowsub_comp`,
  `eqmx_rowsub`, `row_freePn`, and `negb_row_free`.


- in `interval.v`:
  + Intervals and their bounds of `T` now have canonical ordered type instances
    whose ordering relations are the subset relation and the left to right
    ordering respectively. They form partially ordered types if `T` is a
    `porderType`. If `T` is a `latticeType`, they also form `tbLatticeType`
    where the join and meet are intersection and convex hull respectively. If
    `T` is an `orderType`, they are distributive, and the interval bounds are
    totally ordered. (cf Changed section)
  + New lemmas: `bound_ltxx`, `subitvE`, `in_itv`, `itv_ge`, `in_itvI`,
    `itv_total_meet3E`, and `itv_total_join3E`.
- in `order.v`:
  + new definition `lteif` and notations `<?<=%O`, `<?<=^d%O`, `_ < _ ?<= if _`,
    and `_ <^d _ ?<= if _` (cf Changed section).
  + new lemmas `lteifN`, `comparable_lteifNE`, and
    `comparable_lteif_(min|max)(l|r)`.
- in `ssrnum.v`, new lemma `real_lteif_distl`.

- in `matrix.v` new lemma `det_mx11`.
- in `ssralg.v`, new lemma `raddf_inj`, characterizing injectivity for
  additive maps.
- in `mxalgebra.v`, new lemma `row_free_injr` which duplicates
  `row_free_inj` but exposing `mulmxr` for compositionality purposes
  (e.g. with `raddf_eq0`), and lemma `inj_row_free` characterizing
  `row_free` matrices `A`  through `v *m A = 0 -> v = 0` for all `v`.

- in `mxpoly.v`,
  + new definitions `kermxpoly g p` (the kernel of polynomial $p(g)$).
    * new elementary theorems: `kermxpolyC`, `kermxpoly1`,
      `kermxpolyX`, `kermxpoly_min`
    * kernel lemmas: `mxdirect_kermxpoly`, `kermxpolyM`,
      `kermxpoly_prod`, and `mxdirect_sum_kermx`
    * correspondance between `eigenspace` and `kermxpoly`: `eigenspace_poly`
  + generalized eigenspace `geigenspace` and a generalization of eigenvalues
    called `eigenpoly g` (i.e. polynomials such that `kermxpoly g p`
    is nonzero, e.g. eigen polynomials of degree 1 are of the form
    `'X - a%:P` where `a` are eigenvalues), and
    * correspondance with `kermx`: `geigenspaceE`,
    * application of kernel lemmas `mxdirect_sum_geigenspace`,
    * new lemmas: `eigenpolyP`, `eigenvalue_poly`, `eigenspace_sub_geigen`,
  + new `map_mx` lemmas: `map_kermxpoly`, `map_geigenspace`, `eigenpoly_map`.
- in `matrix.v`, added `comm_mx` and `comm_mxb` the propositional and
  boolean versions of matrix commutation, `comm_mx A B` is
  definitionally equal to `GRing.comm A B` when `A B : 'M_n.+1`, this
  is witnessed by the lemma `comm_mxE`.  New notation `all_comm_mx`
  stands for `allrel comm_mxb`. New lemmas `comm_mx_sym`,
  `comm_mx_refl`, `comm_mx0`, `comm0mx`, `comm_mx1`, `comm1mx`,
  `comm_mxN`, `comm_mxN1`, `comm_mxD`, `comm_mxB`, `comm_mx_sum`,
  `comm_mxP`, `all_comm_mxP`, `all_comm_mx1`, `all_comm_mx2P`,
  `all_comm_mx_cons`, `comm_mx_scalar`, and `comm_scalar_mx`. The
  common arguments of these lemmas `R` and `n` are maximal implicits.

- in `seq.v`, added `drop_index`, `in_mask`, `cons_subseq`,
  `undup_subseq`, `leq_count_mask`, `leq_count_subseq`,
  `count_maskP`, `count_subseqP`, `count_rem`, `count_mem_rem`,
  `rem_cons`, `remE`, `subseq_rem`, `leq_uniq_countP`, and
  `leq_uniq_count`.
- in `fintype.v`, added `mask_enum_ord`.
- in `bigop.v`, added `big_mask_tuple` and `big_mask`.
- in `mxalgebra.v`, new notation `stablemx V f` asserting that `f`
  stabilizes `V`, with new theorems: `eigenvectorP`, `eqmx_stable`,
  `stablemx_row_base`, `stablemx_full`, `stablemxM`, `stablemxD`,
  `stablemxN`, `stablemxC`, `stablemx0`, `stableDmx`, `stableNmx`,
  `stable0mx`, `stableCmx`, `stablemx_sums`, and `stablemx_unit`.

- in `mxpoly.v`, new lemma `horner_mx_stable`.
- in `mxalgebra.v`, added `comm_mx_stable`, `comm_mx_stable_ker`, and
  `comm_mx_stable_eigenspace`.
- in `mxpoly.v`, added `comm_mx_horner`, `comm_horner_mx`,
  `comm_horner_mx2`, `horner_mx_stable`, `comm_mx_stable_kermxpoly`,
  and `comm_mx_stable_geigenspace`.

- in `ssralg.v`:
   + Lemma `expr_sum` : equivalent for ring of `expn_sum`
   + Lemma `prodr_natmul` : generalization of `prodrMn_const`.
   Its name will become `prodrMn` in the next release when this name will become available (cf. Renamed section)

- in `polydiv.v`, new lemma `dvdpNl`.
- in `perm.v` new lemma `permS01`.

- in `seq.v`, new definition `rot_add` and new lemmas `rot_minn`,
  `leq_rot_add`, `rot_addC`, `rot_rot_add`.

- in `seq.v`, new lemmas `perm_catACA`, `allpairs0l`, `allpairs0r`,
  `allpairs1l`, `allpairs1r`, `allpairs_cons`, `eq_allpairsr`,
  `allpairs_rcons`, `perm_allpairs_catr`, `perm_allpairs_consr`,
  `mem_allpairs_rconsr`, and `allpairs_rconsr` (with the alias
  `perm_allpairs_rconsr` for the sake of uniformity, but which is
  already deprecated in favor of `allpairs_rconsr`, cf renamed
  section).

- in `seq.v`, new lemmas `allss`, `all_mask`, and `all_sigP`.
  `allss` has also been declared as a hint.

- in `path.v`, new lemmas `sub_cycle(_in)`, `eq_cycle_in`,
  `(path|sorted)_(mask|filter)_in`, `rev_cycle`, `cycle_map`,
  `(homo|mono)_cycle(_in)`.

- in `path.v`, new lemma `sort_iota_stable`.

- in `path.v`, new lemmas `order_path_min_in`, `path_sorted_inE`,
  `sorted_(leq|ltn)_nth_in`, `subseq_path_in`, `subseq_sorted_in`,
  `sorted_(leq|ltn)_index_in`, `sorted_uniq_in`, `sorted_eq_in`,
  `irr_sorted_eq_in`, `sort_sorted_in`, `sorted_sort_in`, `perm_sort_inP`,
  `all_sort`, `sort_stable_in`, `filter_sort_in`, `(sorted_)mask_sort_in`,
  `(sorted_)subseq_sort_in`, and `mem2_sort_in`.

- in `seq.v` new lemmas `index_pivot`, `take_pivot`, `rev_pivot`,
  `eqseq_pivot2l`, `eqseq_pivot2r`, `eqseq_pivotl`, `eqseq_pivotr`
  `uniq_eqseq_pivotl`, `uniq_eqseq_pivotr`, `mask_rcons`, `rev_mask`,
  `subseq_rev`, `subseq_cat2l`, `subseq_cat2r`, `subseq_rot`, and
  `uniq_subseq_pivot`.

- in `mxalgebra.v`, new definitions `maxrankfun`, `fullrankfun` which
  are "subset function" to be plugged in `rowsub`, with lemmas:
  `maxrowsub_free`, `eq_maxrowsub`, `maxrankfun_inj`,
  `maxrowsub_full`, `fullrowsub_full`, `fullrowsub_unit`,
  `fullrowsub_free`, `mxrank_fullrowsub`, `eq_fullrowsub`, and
  `fullrankfun_inj`.

- in `path.v`, added `size_merge_sort_push`, which documents an
  invariant of `merge_sort_push`.

- in `seq.v ` added lemma `mask0s`.

### Changed

- in `ssrbool.v`, use `Reserved Notation` for `[rel _ _ : _ | _]` to avoid warnings with coq-8.12
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
- in `fintype.v`, rename `disjoint_trans` to `disjointWl`

- in `interval.v`:
  + `x <= y ?< if c` (`lersif`) has been generalized to `porderType`, relocated
    to `order.v`, and replaced with `x < y ?<= if c'` (`lteif`) where `c'` is
    negation of `c`.
  + Many definitions and lemmas on intervals such as the membership test are
    generalized from numeric domains to ordered types.
  + Interval bounds `itv_bound : Type -> Type` are redefined with two constructors
    `BSide : bool -> T -> itv_bound T` and `BInfty : bool -> itv_bound T`.
    New notations `BLeft` and `BRight` are aliases for `BSide true` and `BSide false` respectively.
    `BInfty false` and `BInfty true` respectively means positive and negative infinity.
    `BLeft x` and `BRight x` respectively mean close and open bounds as left bounds,
    and they respectively mean open and close bounds as right bounds.
    This change gives us the canonical "left to right" ordering of interval bounds.
- In `matrix.v`, generalized `diag_mx_comm` and `scalar_mx_comm` to
  all `n`, instead of `n'.+1`, thanks to `commmmx`.

- in `interval.v`:
  + Lemmas `mid_in_itv(|oo|cc)` have been generalized from `realFieldType` to
    `numFieldType`.

- The `class_of` records of structures are turned into primitive records to
  prevent prevent potential issues of ambiguous paths and convertibility of
  structure instances.
- In `order.v`, rephrased `comparable_(min|max)[rl]` in terms of
  `{in _, forall x y, _}`, hence reordering the arguments. Made them
  hints for smoother combination with `comparable_big[lr]`.

- In `order.v`,
  + `>=< y` stands for `[pred x | x >=< y]`
  + `>< y`  stands for `[pred x | x >< y]`
  + and the same holds for the dual `>=<^d`, `><^d`, the product
  `>=<^p`, `><^p`, and lexicographic `>=<^l`, `><^l`.
  The previous meanings can be obtained through `>=<%O x` and `><%O x`.
- In `srnum.v`,
  + `>=< y` stands for `[pred x | x >=< y]`

- in `ssrint.v`, generalized `mulpz` for any `ringType`.
- In `fintype.v`, lemmas `inj_card_onto` and `inj_card_bij` take a
  weaker hypothesis (i.e. `#|T| >= #|T'|` instead of `#|T| = #|T'|`
  thanks to `leq_card` under injectivity assumption).

- in `path.v`, generalized lemmas `sub_path_in`, `sub_sorted_in`, and
  `eq_path_in` for non-`eqType`s.

- in `path.v`, generalized lemmas `sorted_ltn_nth` and `sorted_leq_nth`
  (formerly `sorted_lt_nth` and `sorted_le_nth`, cf Renamed section) for
  non-`eqType`s.

- in `order.v`, generalized `sort_le_id` for any `porderType`.

- in `order.v`, the names of lemmas `join_idPl` and `join_idPr` are transposed
  to follow the naming convention.

- the following constants have been tuned to only reduce when they do
  not expose a match: `subn_rec`, `decode_rec`, `nth` (thus avoiding a
  notorious problem of ``p`_0`` expanding too eagerly), `set_nth`,
  `take`, `drop`, `eqseq`, `incr_nth`, `elogn2`, `binomial_rec`,
  `sumpT`.

- in `seq.v`, `mask` will only expand if both arguments are
  constructors, the case `mask [::] s` can be dealt with using
  `mask0s` or explicit conversion.

- in `ssrnum.v`, fixed notations `@minr` and `@maxr` to point `Order.min` and
  `Order.max` respectively.

### Renamed

- `big_rmcond` -> `big_rmcond_in` (cf Changed section)
- `mem_imset` -> `imset_f` (with deprecation alias, cf. Added section)
- `mem_imset2` -> `imset2_f` (with deprecation alias, cf. Added section)

- in `interval.v`, we deprecate, rename, and relocate to `order.v` the following:
  + `lersif_(trans|anti)` -> `lteif_(trans|anti)`
  + `lersif(xx|NF|S|T|F|W)` -> `lteif(xx|NF|S|T|F|W)`
  + `lersif_(andb|orb|imply)` -> `lteif_(andb|orb|imply)`
  + `ltrW_lersif` -> `ltrW_lteif`
  + `lersifN` -> `lteifNE`
  + `lersif_(min|max)(l|r)` -> ` lteif_(min|max)(l|r)`

- in `interval.v`, we deprecate, rename, and relocate to `ssrnum.v` the following:
  + `subr_lersif(r0|0r|0)` -> `subr_lteif(r0|0r|0)`
  + `lersif01` -> `lteif01`
  + `lersif_(oppl|oppr|0oppr|oppr0|opp2|oppE)` -> `lteif_(oppl|oppr|0oppr|oppr0|opp2|oppE)`
  + `lersif_add2(|l|r)` -> `lteif_add2(|l|r)`
  + `lersif_sub(l|r)_add(l|r)` -> `lteif_sub(l|r)_add(l|r)`
  + `lersif_sub_add(l|r)` -> `lteif_sub_add(l|r)`
  + `lersif_(p|n)mul2(l|r)` -> `lteif_(p|n)mul2(l|r)`
  + `real_lersifN` -> `real_lteifNE`
  + `real_lersif_norm(l|r)` -> `real_lteif_norm(l|r)`
  + `lersif_nnormr` -> `lteif_nnormr`
  + `lersif_norm(l|r)` -> `lteif_norm(l|r)`
  + `lersif_distl` -> `lteif_distl`
  + `lersif_(p|n)div(l|r)_mul(l|r)` -> `lteif_(p|n)div(l|r)_mul(l|r)`

- in `interval.v`, we deprecate and replace the following:
  + `lersif_in_itv` -> `lteif_in_itv`
  + `itv_gte` -> `itv_ge`
  + `l(t|e)r_in_itv` -> `lt_in_itv`

- in `ssrnat.v`
  + `iter_add` -> `iterD`
  + `maxn_mul(l|r)` -> `maxnM(l|r)`
  + `minn_mul(l|r)` -> `minnM(l|r)`
  + `odd_(opp|mul|exp)` -> `odd(N|M|X)`
  + `sqrn_sub` -> `sqrnB`

- in `seq.v`,
  + `iota_add(|l)` -> `iotaD(|l)`
  + `allpairs_(cons|cat)r` -> `mem_allpairs_(cons|cat)r`
    (`allpairs_consr` and `allpairs_catr` are now deprecated alias,
    and will be attributed to the new `perm_allpairs_catr`).

- in `path.v`,
  + `eq_sorted(_irr)` -> `(irr_)sorted_eq`
  + `sorted_(lt|le)_nth` -> `sorted_(ltn|leq)_nth`
  + `(ltn|leq)_index` -> `sorted_(ltn|leq)_index`
  + `subseq_order_path` -> `subseq_path`

- in `div.v`
  + `coprime_mul(l|r)` -> `coprimeM(l|r)`
  + `coprime_exp(l|r)` -> `coprimeX(l|r)`

- in `fintype.v`
  + `bump_addl` -> `bumpDl`
  + `unbump_addl` -> `unbumpDl`

- in `bigop.v`, `mulm_add(l|r)` -> `mulmD(l|r)`

- in `prime.v`
  + `primes_(mul|exp)` -> `primes(M|X)`
  + `pnat_(mul|exp)` -> `pnat(M|X)`

- in `order.v`, `eq_sorted_(le|lt)` -> `(le|lt)_sorted_eq`

- in `ssralg.v`
  + `prodrMn` has been renamed `prodrMn_const` (with deprecation alias, cf. Added section)

- in `poly.v`
  + `polyC_(add|opp|sub|muln|mul|inv)` -> `polyC(D|N|B|Mn|M|V)`
  + `lead_coef_opp` -> `lead_coefN`
  + `derivn_sub` -> `derivnB`

- in `polydiv.v`
  + `rdivp_add(l|r)` -> `rdivpD(l|r)`
  + `rmodp_add` -> `rmodpD`
  + `dvdp_scale(l|r)` -> `dvdpZ(l|r)`
  + `dvdp_opp` -> `dvdpNl`
  + `coprimep_scale(l|r)` -> `coprimepZ(l|r)`
  + `coprimep_mul(l|r)` -> `coprimepM(l|r)`
  + `modp_scale(l|r)` -> `modpZ(l|r)`
  + `modp_(opp|add|scalel|scaler)` -> `modp(N|D|Zl|Zr)`
  + `divp_(opp|add|scalel|scaler)` -> `divp(N|D|Zl|Zr)`

- in `matrix.v`, `map_mx_sub` -> `map_mxB`

- in `mxalgebra.v`, `mulsmx_add(l|r)` -> `mulsmxD(l|r)`

- in `vector.v`, `limg_add` -> `limgD`

- in `ssrint.v`, `polyC_mulrz` -> `polyCMz`

- in `intdiv.v`
  + `coprimez_mul(l|r)` -> `coprimezM(l|r)`
  + `coprimez_exp(l|r)` -> `coprimezX(l|r)`

- in `finset.v`, fixed printing of notation `[set E | x in A , y in B & P ]`

### Removed

- in `interval.v`, we remove the following:
  + `le_bound(l|r)` (use `Order.le` instead)
  + `le_bound(l|r)_refl` (use `lexx` instead)
  + `le_bound(l|r)_anti` (use `eq_le` instead)
  + `le_bound(l|r)_trans` (use `le_trans` instead)
  + `le_bound(l|r)_bb` (use `bound_lexx` instead)
  + `le_bound(l|r)_total` (use `le_total` instead)

- in `interval.v`, we deprecate the following:
  + `itv_intersection` (use `Order.meet` instead)
  + `itv_intersection1i` (use `meet1x` instead)
  + `itv_intersectioni1` (use `meetx1` instead)
  + `itv_intersectionii` (use `meetxx` instead)
  + `itv_intersectionC` (use `meetC` instead)
  + `itv_intersectionA` (use `meetA` instead)

- in `mxpoly.v`, we deprecate `scalar_mx_comm`, and advise to use
  `comm_mxC` instead (with maximal implicit arguments `R` and `n`).

- in `ssrnat.v`, we remove the compatibility module `mc_1_9`.

### Infrastructure

### Misc
