# Changelog
All notable changes to this project will be documented in this file.

Last releases: [[1.11.0+beta1] - 2020-04-15](#1110beta1---2020-04-15) and [[1.10.0] - 2019-11-29](#1100---2019-11-29).

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [1.11.0+beta1] - 2020-04-15

This release is compatible with Coq versions 8.7, 8.8, 8.9 and 8.10.

### Added

- Arithmetic theorems in ssrnat, div and prime about `logn`,
    `coprime`, `gcd`, `lcm` and `partn`: `logn_coprime`, `logn_gcd`,
    `logn_lcm`, `eq_partn_from_log` and `eqn_from_log`.

- Lemmas `ltnNleqif`, `eq_leqif`, `eqTleqif` in `ssrnat`

- Lemmas `eqEtupe`, `tnthS` and `tnth_nseq` in `tuple`

- Ported `order.v` from the finmap library, which provides structures of ordered
  sets (`porderType`, `latticeType`, `distrLatticeType`, `orderType`, etc.) and
  its theory.

- Lemmas `path_map`, `eq_path_in`, `sub_path_in`, `path_sortedE`,
  `sub_sorted` and `sub_sorted_in` in `path` (and refactored related proofs)

- Added lemmas `hasNfind`, `memNindex` and `findP` in `seq`

- Added lemmas `foldr_rcons`, `foldl_rcons`, `scanl_rcons` and
  `nth_cons_scanl` in `seq`

- ssrAC tactics, see header of `ssreflect/ssrAC.v` for documentation
  of `(AC patternshape reordering)`, `(ACl reordering)` `(ACof
  reordering reordering)`, `op.[AC patternshape reordering]`, `op.[ACl
  reordering]` and `op.[ACof reordering reordering]`.

- Added definition `cast_perm` with a group morphism canonical
  structure, and lemmas `permX_fix`, `imset_perm1`, `permS0`,
  `permS1`, `cast_perm_id`, `cast_ord_permE`, `cast_permE`,
  `cast_perm_comp`, `cast_permK`, `cast_permKV`, `cast_perm_inj`,
  `cast_perm_sym`,`cast_perm_morphM`, and `isom_cast_perm` in `perm`
  and `restr_perm_commute` in `action`.

- Added `card_porbit_neq0`, `porbitP`, and `porbitPmin` in `perm`

- Added definition `Sym` with a group set canonical structure and
  lemmas `card_Sn` and `card_Sym` in `perm` and `SymE` in `action`

### Changed

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

      Replacing `minrP` and `maxrP` with `leP` and `ltP` may require to provide some arguments explicitly.
      The former ones respectively try to match with `minr` and `maxr` first but the latter ones try that in the order of `<`, `<=`, `maxr`, and `minr`.
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
  + The compatibility layer for the version 1.10 is provided as the
    `ssrnum.mc_1_10` module. One may compile proofs compatible with the version
    1.10 in newer versions by using the `mc_1_10.Num` module instead of the
    `Num` module. However, instances of the number structures may require
    changes.

- Extended comparison predicates `leqP`, `ltnP`, and `ltngtP` in ssrnat to
  allow case analysis on `minn` and `maxn`.
  + The compatibility layer for the version 1.10 is provided as the
    `ssrnat.mc_1_10` module. One may compile proofs compatible with the version
    1.10 in newer versions by using this module.

- The definition of `all2` was slightly altered for a better interaction with
  the guard condition (#469)

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
  + `homo_inj_lt(_in)` -> `inj_homo_ltn(_in)`
  + `(inc|dec)r_inj(_in)` -> `(inc|dec)n_inj(_in)`
- switching long suffixes to short suffixes
  + `odd_add` -> `oddD`
  + `odd_sub` -> `oddB`
  + `take_addn` -> `takeD`
  + `rot_addn` -> `rotD`
  + `nseq_addn` -> `nseqD`
- Replaced `cycle` by `orbit` in `perm/action`:
  + `pcycle` -> `porbit`
  + `pcycles` -> `porbits`
  + `pcycleE` -> `porbitE`
  + `pcycle_actperm` -> `porbit_actperm`
  + `mem_pcycle` -> `mem_porbit`
  + `pcycle_id` -> `porbit_id`
  + `uniq_traject_pcycle` -> `uniq_traject_porbit`
  + `pcycle_traject` -> `porbit_traject`
  + `iter_pcycle` -> `iter_porbit`
  + `eq_pcycle_mem` -> `eq_porbit_mem`
  + `pcycle_sym` -> `porbit_sym`
  + `pcycle_perm` -> `porbit_perm`
  + `ncycles_mul_tperm` -> `porbits_mul_tperm`

### Removed

The following were deprecated since release 1.9.0
- `tuple_perm_eqP` (use `tuple_permP` instead, from `perm.v`)
- `eq_big_perm` (use `perm_big` instead, from `bigop.v`)
- `perm_eqP` (use `permP` instead, from seq.v)
- `perm_eqlP` (use `permPl` instead)
- `perm_eqrP` (use `permPr` instead)
- `perm_eqlE` (use `permEl` instead)
- `perm_eq_refl` (use `perm_refl` instead)
- `perm_eq_sym` (use `perm_sym` instead)
- `perm_eq_trans` (use `perm_trans` instead)
- `perm_eq_size` (use `perm_size` instead)
- `perm_eq_mem` (use `perm_mem` instead)
- `perm_eq_uniq` (use `perm_uniq` instead)

## [1.10.0] - 2019-11-29

This release is compatible with Coq versions 8.9 and 8.10.

### Added

- Added a `void` notation for the `Empty_set` type of the standard library, the
  canonical injection `of_void` and its cancellation lemma `of_voidK`, and
  `eq`, `choice`, `count` and `fin` instances.

- Added `ltn_ind` general induction principle for `nat` variables, helper lemmas `ubnP`, `ltnSE`, ubnPleq, ubnPgeq and ubnPeq, in support of a generalized induction idiom for `nat` measures that does not rely on the `{-2}` numerical occurrence selector, and purged this idiom from the `mathcomp` library (see below).

- Added fixpoint and cofixpoint constructions to `finset`: `fixset`,
  `cofixset` and `fix_order`, with a few theorems about them

- Added functions `tuple_of_finfun`, `finfun_of_tuple`, and their
  "cancellation" lemmas.

- Added theorems `totient_prime` and `Euclid_dvd_prod` in `prime.v`

- Added theorems `ffact_prod`, `prime_modn_expSn` and `fermat_little`
  in `binomial.v`

- Added theorems `flatten_map1`, `allpairs_consr`, `mask_filter`,
  `all_filter`, `all_pmap`, and `all_allpairsP` in `seq.v`.

- Added theorems `nth_rcons_default`, `undup_rcons`, `undup_cat` and
  `undup_flatten_nseq` in `seq.v`

- Fintype theorems: `fintype0`, `card_le1P`, `mem_card1`,
  `card1P`, `fintype_le1P`, `fintype1`, `fintype1P`,
  `existsPn`, `exists_inPn`, `forallPn`, `forall_inPn`,
  `eq_enum_rank_in`, `enum_rank_in_inj`, `lshift_inj`, and
  `rshift_inj`.

- Bigop theorems: `index_enum_uniq`, `big_rmcond`, `bigD1_seq`,
  `big_enum_val_cond`, `big_enum_rank_cond`,
  `big_enum_val`, `big_enum_rank`, `big_set`,
  `big_enumP`, `big_enum_cond`, `big_enum`

- Arithmetic theorems in ssrnat and div:
  - some trivial results in ssrnat: `ltn_predL`, `ltn_predRL`,
    `ltn_subrR`, `leq_subrR`, `ltn_subrL` and `predn_sub`,
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

- Added `sort_rec1` and `sortE` to help inductive reasoning on `sort`.

- Added map/parametricity theorems about `path`, `sort`, and `sorted`:
  `homo_path`, `mono_path`, `homo_path_in`, `mono_path_in`,
  `homo_sorted`, `mono_sorted`, `map_merge`, `merge_map`, `map_sort`,
  `sort_map`, `sorted_map`, `homo_sorted_in`, `mono_sorted_in`.

- Extracting lemma `fpathE` from `fpathP`, and shortening the proof of
  the latter.

- Added the theorem `perm_iota_sort` to express that the sorting of
  any sequence `s` is equal to a mapping of `iota 0 (size s)` to the
  nth elements of `s`, so that one can still reason on `nat`, even
  though the elements of `s` are not in an `eqType`.

- Added stability theorems about `merge` and `sort`: `sorted_merge`,
  `merge_stable_path`, `merge_stable_sorted`, `sorted_sort`, `sort_stable`,
  `filter_sort`, `mask_sort`, `sorted_mask_sort`, `subseq_sort`,
  `sorted_subseq_sort`, and `mem2_sort`.

- New algebraic interfaces in `ssralg.v`: comAlgebra and
  comUnitAlgebra for commutative and commutative-unitary algebras.

- Initial property for polynomials in algebras:
  New canonical lrMoprphism `horner_alg` evaluating a polynomial in an element
  of an algebra. The theory include the lemmas `in_alg_comm`, `horner_algC`,
  `horner_algX`, `poly_alg_initial`.

- Added lemmas on commutation with difference, big sum and prod:
  `commrB`, `commr_sum`, `commr_prod`.

- Added a few basic seq lemmas about `nseq`, `take` and `drop`:
  `nseq_addn`, `take_take`, `take_drop`, `take_addn`, `takeC`,
  `take_nseq`, `drop_nseq`, `rev_nseq`, `take_iota`, `drop_iota`.

- Added ssrfun theorem `inj_compr`.

- Added theorems `mem2E`, `nextE`, `mem_fcycle`, `inj_cycle`,
  `take_traject`, `trajectD` and `cycle_catC` in `path.v`

- Added lemmas about `cycle`, `connect`, `fconnect`, `order` and
  `orbit` in `fingraph.v`:
  - lemma `connect_cycle`,
  - lemmas `in_orbit`, `order_gt0`, `findex_eq0`, `mem_orbit`,
    `image_orbit`,
  - lemmas `fcycle_rconsE`, `fcycle_consE`, `fcycle_consEflatten` and
    `undup_cycle_cons` which operate under the precondition that the
    sequence `x :: p` is a cycle for f (i.e. `fcycle f (x :: p)`).
  - lemmas which operate under the precondition there is a sequence
    `p` which is a cycle for `f` (i.e. `fcycle f p`):
    `order_le_cycle`, `finv_cycle`, `f_finv_cycle`, `finv_f_cycle`,
    `finv_inj_cycle`, `iter_finv_cycle`, `cycle_orbit_cycle`,
    `fpath_finv_cycle`, `fpath_finv_f_cycle`, `fpath_f_finv_cycle`,
    `prevE`, `fcycleEflatten`, `fcycle_undup`, `in_orbit_cycle`,
    `eq_order_cycle`, `iter_order_cycle`,
  - lemmas `injectivePcycle`, `orbitPcycle`, `fconnect_eqVf`,
    `order_id_cycle`, `orderPcycle`, `fconnect_f`, `fconnect_findex`.

- Added lemma `rot_index` which explicits the index given by `rot_to`.

- Added tactic `tfae` to split an equivalence between n+1 propositions
  into n+1 goals, and referenced orbitPcycle as a reference of use.

### Changed

- Replaced the legacy generalised induction idiom with a more robust one
that does not rely on the `{-2}` numerical occurrence selector, using
new `ssrnat` helper lemmas `ltn_ind`, `ubnP`, `ubnPleq`,  ...., (see above). The new idiom is documented in `ssrnat`.
   This change anticipates an expected evolution of `fintype` to integrate `finmap`. It is likely that the new definition of the `#|A|` notation will hide multiple occurrences of `A`, which will break the `{-2}` induction idiom. Client libraries should update before the 1.11 release (see [PR #434](https://github.com/math-comp/math-comp/pull/434) for examples).

 - Replaced the use of the accidental convertibility between `enum A` and
   `filter A (index_enum T)` with more explicit lemmas `big_enumP`, `big_enum`, `big_enum_cond`, `big_image` added to the `bigop` library, and deprecated the `filter_index_enum` lemma that states the corresponding equality. Both convertibility and equality may no longer hold in future `mathcomp` releases when sets over `finType`s are generalised to finite sets over `choiceType`s, so client libraries should stop relying on this identity. File `bigop.v` has some boilerplate to help with the port; also see [PR #441](https://github.com/math-comp/math-comp/pull/441) for examples.

 - Restricted `big_image`, `big_image_cond`, `big_image_id` and `big_image_cond_id`
 to `bigop`s over _abelian_ monoids, anticipating the change in the definition of `enum`. This may introduce some incompatibilities - non-abelian instances should be dealt with a combination of `big_map` and `big_enumP`.

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

- Moved `iter_in` to ssrnat and reordered its arguments.

- Notation `[<-> P0 ; .. ; Pn]` now forces `Pi` to be of type `Prop`.

### Removed

- `fin_inj_bij` lemma is removed as a duplicate of `injF_bij` lemma
  from `fintype` library.

### Infrastructure

- `Makefile` now supports the `test-suite` and `only` targets. Currently,
  `make test-suite` will verify the implementation of mathematical structures
  and their inheritances of MathComp automatically, by using the `hierarchy.ml`
  utility. One can use the `only` target to build the sub-libraries of MathComp
  specified by the `TGTS` variable, e.g.,
  `make only TGTS="ssreflect/all_ssreflect.vo fingroup/all_fingroup.vo"`.

- `Makefile`now supports a `doc` target to build the documentation as made
   available on https://mathcomp.github.io/htmldoc/index.html

## [1.9.0] - 2019-05-22

MathComp 1.9.0 is compatible with Coq 8.7, 8.8, 8.9 and 8.10beta1.
Minor releases will remain compatible with Coq 8.9 and 8.10; compatibility with earlier
versions may be dropped.

### Added

- `nonPropType`, an interface for non-`Prop` types, and `{pred T}` and
   `relpre f r`, all of which will be in the Coq 8.10 core SSreflect library.

- `deprecate old_id new_id`, notation for `new_id` that prints a deprecation
  warning for `old_id`; `Import Deprecation.Silent` turns off those warnings,
  `Import Deprecation.Reject` raises errors instead of only warning.

- `filter_nseq`, `count_nseq`, `mem_nseq`,
  `rcons_inj`, `rcons_injl`, `rcons_injr`, `nthK`, `sumn_rot`.

- some `perm_eq` lemmas: `perm_cat[lr]`, `perm_nilP`,
  `perm_consP`, `perm_has`, `perm_flatten`, `perm_sumn`.

- computing (efficiently) (item, multiplicity) tallies of sequences over an
  `eqType`: `tally s`, `incr_tally bs x`, `bs \is a wf_tally`, `tally_seq bs`.

### Changed

- definition of `PredType` which now takes only a `P -> pred T` function;
  definition of `simpl_rel` to improve simplification by `inE`. Both these
  changes will be in the Coq 8.10 SSReflect core library.

- definition of `permutations s` now uses an optimal algorithm (in space _and_
  time) to generate all permutations of s back-to-front, using `tally s`.

### Renamed

- `perm_eqP` -> `permP` (`seq.permP` if `perm.v` is also imported)
- `perm_eqlP` -> `permPl`
- `perm_eqrP` -> `permPr`
- `perm_eqlE` -> `permEl`
- `perm_eq_refl` -> `perm_refl`
- `perm_eq_sym` -> `perm_sym`
- `perm_eq_trans` -> `perm_trans`
- `perm_eq_size` -> `perm_size`
- `perm_eq_mem` -> `perm_mem`
- `perm_eq_uniq` -> `perm_uniq`
- `perm_eq_rev` -> `perm_rev`
- `perm_eq_flatten` -> `perm_flatten`
- `perm_eq_all` -> `perm_all`
- `perm_eq_small` -> `perm_small_eq`
- `perm_eq_nilP` -> `perm_nilP`
- `perm_eq_consP` -> `perm_consP`
- `leq_size_perm` -> `uniq_min_size` (permuting conclusions)
- `perm_uniq` -> `eq_uniq` (permuting assumptions)
  --> beware `perm_uniq` now means `perm_eq_uniq`
- `uniq_perm_eq` -> `uniq_perm`
- `perm_eq_iotaP` -> `perm_iotaP`
- `perm_undup_count` -> `perm_count_undup`
- `tuple_perm_eqP` -> `tuple_permP`
- `eq_big_perm` -> `perm_big`
- `perm_eq_abelian_type` -> `abelian_type_pgroup`

### Misc

- removed Coq prelude hints `plus_n_O` `plus_n_Sm` `mult_n_O` `mult_n_Sm`,
  to improve robustness of `by ...`; scripts may need to invoke
  `addn0`, `addnS`, `muln0` or `mulnS`
  explicitly where these hints were used accidentally.

## [1.8.0] - 2019-04-08

Drop compatibility with Coq 8.6 (OCaml plugin removed).
MathComp 1.8.0 is compatible with Coq 8.7, 8.8 and 8.9.

### Added

- Companion matrix of a polynomial `companionmx p` and the
  theorems: `companionmxK`, `map_mx_companion` and `companion_map_poly`

- `homoW_in`, `inj_homo_in`, `mono_inj_in`, `anti_mono_in`,
  `total_homo_mono_in`, `homoW`, `inj_homo`, `monoj`, `anti_mono`,
  `total_homo_mono`

- `sorted_lt_nth`, `ltn_index`, `sorted_le_nth`, `leq_index`.

- `[arg minr_( i < n | P ) F]` and `[arg maxr_( i < n | P ) F]`
  with all their variants, following the same convention as for `nat`

- `contra_neqN`, `contra_neqF`, `contra_neqT`, `contra_neq_eq`, `contra_eq_neq`

- `take_subseq`, `drop_subseq`

- `big_imset_cond`,`big_map_id`, `big_image_cond`
  `big_image`, `big_image_cond_id` and `big_image_id`

- `foldrE`, `foldlE`, `foldl_idx` and `sumnE`
  to turn "seq statements" into "bigop statements"

- `all_iff` with notation `[<-> P0; P1; ..; Pn]` to talk about
  circular implication `P0 -> P1 -> ... -> Pn -> P0`.
  Related theorems are `all_iffLR` and `all_iffP`

- support for casts in map comprehension notations, e.g.,
  `[seq E : T | s <- s]`.

- a predicate `all2`, a parallel double `seq` version of `all`.

- some `perm_eq` lemmas: `perm_cat[lr]`, `perm_eq_nilP`,
  `perm_eq_consP`, `perm_eq_flatten`.

- a function `permutations` that computes a duplicate-free list
  of all permutations of a given sequence `s` over an `eqType`, along
  with its theory: `mem_permutations`, `size_permutations`,
  `permutations_uniq`, `permutations_all_uniq`, `perm_permutations`.

- `eq_mktuple`, `eq_ffun`, `eq_finset`, `eq_poly`, `ex_mx` that can be
  used with the `under` tactic from the Coq 8.10 SSReflect plugin
  (cf. [coq/coq#9651](https://github.com/coq/coq/pull/9651))

### Changed

- Theory of `lersif` and intervals:
  + Many `lersif` related lemmas are ported from `ssrnum`
  + Changed: `prev_of_itv`, `itv_decompose`, and `itv_rewrite`
  + New theory of intersections of intervals

- Generalized `extremum_spec` and its theory, added `extremum` and
  `extremumP`, generalizing `arg_min` for an arbitrary `eqType` with an
  order relation on it (rather than `nat`). Redefined `arg_min` and
  `arg_max` with it.

- Reshuffled theorems inside files and packages:
  + `countalg` goes from the field to the algebra package
  + `finalg` inherits from countalg
  + `closed_field` contains the construction of algebraic closure
    for countable fields that used to be in the file `countalg`.

- Maximal implicits applied to reflection, injectivity and cancellation
  lemmas so that they are easier to pass to combinator lemmas such as
  `sameP`, `inj_eq` or `canLR`.

- Added `reindex_inj s` shorthand for reindexing a bigop with a
  permutation `s`.

- Added lemma `eqmxMunitP`: two matrices with the same shape
  represent the same subspace iff they differ only by a change of
  basis.

- Corrected implicits and documentation of `MatrixGenField`.

- Rewritten proof of quantifier elimination for closed field in a
  monadic style.

- Specialized `bool_irrelevance` so that the statement reflects
  the name.

- Changed the shape of the type of `FieldMixin` to allow one-line
  in-proof definition of bespoke `fieldType` structure.

- Refactored and extended Arguments directives to provide more
  comprehensive signature information.

- Generalized the notation `[seq E | i <- s, j <- t]` to the case
  where `t` may depend on `i`. The notation is now primitive and
  expressed using `flatten` and `map` (see documentation of seq).
  `allpairs` now expands to this notation when fully applied.
  + Added `allpairs_dep` and made it self-expanding as well.
  + Generalized some lemmas in a backward compatible way.
  + Some strictly more general lemmas now have suffix `_dep`.
  + Replaced `allpairs_comp` with its converse `map_allpairs`.
  + Added `allpairs` extensionality lemmas for the following cases:
    non-localised (`eq_allpairs`), dependent localised
    (`eq_in_allpairs_dep`) and non-dependent localised
    (`eq_in_allpairs`); as per `eq_in_map`, the latter two are
    equivalences.

- Generalized `{ffun A -> R}` to handle dependent functions, and to be
  structurally positive so it can be used in recursive inductive type
  definitions.

  Minor backward incompatibilities: `fgraph f` is no longer
  a field accessor, and no longer equal to `val f` as `{ffun A -> R}` is no
  longer a `subType`; some instances of `finfun`, `ffunE`, `ffunK` may not unify
  with a generic non-dependent function type `A -> ?R` due to a bug in
  Coq version 8.9 or below.

- Renamed double `seq` induction lemma from `seq2_ind` to `seq_ind2`,
  and weakened its induction hypothesis.

- Replaced the `nosimpl` in `rev` with a `Arguments simpl never`
  directive.

- Many corrections in implicits declarations.

- fixed missing joins in `ssralg`, `ssrnum`, `finalg` and `countalg`

### Renamed

Renamings also involve the `_in` suffix counterpart when applicable

- `mono_inj` -> `incr_inj`
- `nmono_inj` -> `decr_inj`
- `leq_mono_inj` -> `incnr_inj`
- `leq_nmono_inj` -> `decnr_inj`
- `homo_inj_ltn_lt` -> `incnr_inj`
- `nhomo_inj_ltn_lt` -> `decnr_inj`
- `homo_inj_in_lt` -> `inj_homo_ltr_in`
- `nhomo_inj_in_lt` -> `inj_nhomo_ltr_in`
- `ltn_ltrW_homo` -> `ltnrW_homo`
- `ltn_ltrW_nhomo` -> `ltnrW_nhomo`
- `leq_lerW_mono` -> `lenrW_mono`
- `leq_lerW_nmono` -> `lenrW_nmono`
- `homo_leq_mono` -> `lenr_mono`
- `nhomo_leq_mono` -> `lenr_nmono`
- `homo_inj_lt` -> `inj_homo_ltr`
- `nhomo_inj_lt` -> `inj_nhomo_ltr`
- `homo_inj_ltn_lt` -> `inj_homo_ltnr`
- `nhomo_inj_ltn_lt` -> `inj_nhomo_ltnr`
- `homo_mono` -> `ler_mono`
- `nhomo_mono` -> `ler_nmono`
- `big_setIDdep` -> `big_setIDcond`
- `sum_nat_dep_const` -> `sum_nat_cond_const`

### Misc

- Removed trailing `_ : Type` field from packed classes. This performance
  optimization is not strictly necessary with modern Coq versions.

- Removed duplicated definitions of `tag`, `tagged` and `Tagged`
  from `eqtype.v`. They are already in `ssrfun.v`.

- Miscellaneous improvements to proof scripts and file organisation.

## [1.7.0] - 2018-04-24

Compatibility with Coq 8.8 and lost compatibility with
Coq <= 8.5. This release is compatible with Coq 8.6, 8.7 and 8.8.

- Integration in Coq startng from version 8.7 of:
  + OCaml plugin (plugin for 8.6 still in the archive for backward compatibility)
  + `ssreflect.v`, `ssrbool.v`, `ssrfun.v` and `ssrtest/`

- Cleaning up the github repository: the math-comp repository is
  now dedicated to the released material (as in the present
  release). For instance, directories `real-closed/` and `odd-order/` now
  have their own repository.

### Changed

- Library refactoring: `algC` and `ssrnum`.
  Library `ssrnum.v` provides an interface `numClosedFieldType`, which abstracts the
  theory of algebraic numbers. In particular, `Re`, `Im`, `'i`,
  `conjC`, `n.-root` and `sqrtC`, previously defined in library `algC.v`,
  are now part of this generic interface. In case of ambiguity,
  a cast to type `algC`, of complex algebraic numbers, can be used to
  disambiguate via  typing constraints. Some theory was thus made
  more generic, and the corresponding lemmas, previously defined in
  library `algC.v` (e.g. `conjCK`) now feature an extra, non maximal
  implicit, parameter of type `numClosedFieldType`. This could break
  some proofs.
  Every theorem from `ssrnum` that used to be in `algC` changed statement.

- `ltngtP`, `contra_eq`, `contra_neq`, `odd_opp`, `nth_iota`

### Added

- `iter_in`, `finv_in`, `inv_f_in`, `finv_inj_in`, `fconnect_sym_in`, `iter_order_in`,
  `iter_finv_in`, `cycle_orbit_in`, `fpath_finv_in`, `fpath_finv_f_in`, `fpath_f_finv_in`
- `big_allpairs`
- `uniqP, uniqPn`
- `dec_factor_theorem`, `mul_bin_down`, `mul_bin_left`
- `abstract_context` (`in ssreflect.v`, now merged in Coq proper)

### Renamed

- Lemma `dvdn_fact` was moved from library `prime.v` to library `div.v`
- `mul_Sm_binm -> mul_bin_diag
- `divn1` -> `divz1` (in intdiv)
- `rootC` -> `nthroot`
- `algRe` -> `Re`
- `algIm` -> `Im`
- `algCi` -> `imaginaryC`
- `reshape_index_leq` -> `reshape_leq`

## [1.6.0] - 2015-11-24 (ssreflect + mathcomp)

Major reorganization of the archive.

- Files split into sub-directories: `ssreflect/`, `algebra/`, `fingroup/`,
  `solvable/`, `field/` and `character/`. In this way the user can decide
  to compile only the subset of the Mathematical Components library
  that is relevant to her. Note that this introduces a possible
  incompatibility for users of the previous version. A replacement
  scheme is suggested in the installation notes.

- The archive is now open and based on git. Public mirror at:
  https://github.com/math-comp/math-comp

- Sources of the reference manual of the Ssreflect tactic language are
  also open and available at: https://github.com/math-comp/ssr-manual
  Pull requests improving the documentation are welcome.

### Renamed
- `conjC_closed` -> `cfConjC_closed`
- `class_transr` -> `class_eqP`
- `cfclass_transl` -> `cfclass_transr`
- `nontrivial_ideal` -> `proper_ideal`
- `zchar_orthonormalP` -> `vchar_orthonormalP`

### Changed
- `seq_sub`
- `orbit_in_transl`, `orbit_sym`, `orbit_trans`, `orbit_transl`, `orbit_transr`,
  `cfAut_char`, `cfConjC_char`, `invg_lcosets`, `lcoset_transl`, `lcoset_transr`,
  `rcoset_transl`, `rcoset_transr`, `mem2_last`, `bind_unless`, `unless_contra`, `all_and2`,
  `all_and3`, `all_and4`, `all_and5`, `ltr0_neq0`, `ltr_prod`, `Zisometry_of_iso`

### Added
- `adhoc_seq_sub_choiceMixin`, `adhoc_seq_sub_[choice|fin]Type`
- `orbit_in_eqP`, `cards_draws`, `cfAut_lin_char`, `cfConjC_lin_char`,
  `extend_cfConjC_subset`, `isometry_of_free`, `cfAutK`, `cfAutVK`,
  `lcoset_eqP`, `rcoset_eqP`, `class_eqP`, `gFsub_trans`, `gFnorms`,
  `gFchar_trans`, `gFnormal_trans`, `gFnorm_trans`, `mem2_seq1`,
  `dvdn_fact`, `prime_above`, `subKr`, `subrI`, `subIr`, `subr0_eq`,
  `divrI`, `divIr`, `divKr`, `divfI`, `divIf`, `divKf`, `impliesP`, `impliesPn`,
  `unlessL`, `unlessR`, `unless_sym`, `unlessP` (coercion), `classicW`,
  `ltr_prod_nat`
- Notation `\unless C, P`

## [1.5.0] - 2014-03-12 (ssreflect + mathcomp)

Split the archive in SSReflect and MathComp

- With this release "ssreflect" has been split into two packages.
  The Ssreflect one contains the proof language (plugin for Coq) and a
  small set of core theory libraries about boolean, natural numbers,
  sequences, decidable equality  and finite types. The Mathematical
  Components one contains advanced theory files covering a wider
  spectrum of mathematics.

- With respect to version 1.4 the proof language got a few new
  features related to forward reasoning and some bug fixes. The
  Mathematical Components library features 16 new theory files and in
  particular: some field and Galois theory, advanced character theory
  and a construction of algebraic numbers.

## [1.4.0] - 2012-09-05 (ssreflect)

- With this release the plugin code received many bug fixes and the
  existing libraries relevant updates.  This release also includes
  some new libraries on the following topics: rational numbers,
  divisibility of integers, F-algebras, finite dimensional field
  extensions and Euclidean division for polynomials over a ring.

- The release includes a major code refactoring of the plugin for Coq
  8.4.  In particular a documented ML API to access the pattern matching
  facilities of Ssreflect from third party plugins has been introduced.

## [1.3.0] - 2011-03-14 (ssreflect)

- The tactic language has been extended with several new features, inspired by
  the five years of intensive use in our project. However we have kept
  the core of the language unchanged; the new library compiles with
  Ssreflect 1.2.  Users of a Coq 8.2 toplevel statically linked with
  Ssreflect 1.2 need to comment the Declare ML Module "ssreflect" line
  in ssreflect.v to properly compile the 1.3 library.  We will continue
  supporting new releases of Coq in due course.

- The new library adds general linear algebra (matrix rank, subspaces)
  and all of the advanced finite group that was developed in the
  course of completing the Local Analysis part of the Odd Order Theorem,
  starting from the Sylow and Hall theorems and including full structure
  theorems for abelian, extremal and extraspecial groups, and general
  (modular) linear representation theory.

## [1.2.0] - 2009-08-14 (ssreflect)

No change log

## [1.1.0] - 2008-03-18 (ssreflect)

First public release
