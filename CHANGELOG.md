# Changelog
All notable changes to this project will be documented in this file.

Last releases: [[1.8.0] - 2019-04-08](#180---2019-04-08) and [[1.7.0] - 2018-04-24](#170---2018-04-24).

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

### Added

- `nonPropType`, an interface for non-`Prop` types, and `{pred T}` and
   `relpre f r`, all of which will be in the Coq 8.11 core SSreflect library.

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
  changes will be in the Coq 8.11 SSReflect core library.

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
- `perm_eq_uniq` -> perm_uniq`
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
