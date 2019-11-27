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

- New algebraic interfaces : comAlgebra and comUnitAlgebra for
  commutative and commutative-unitary algebras.

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
