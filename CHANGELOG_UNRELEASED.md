# Changelog (unreleased)

To avoid having old PRs put changes into the wrong section of the CHANGELOG,
new entries now go to the present file as discussed
[here](https://github.com/math-comp/math-comp/wiki/Agenda-of-the-April-23rd-2019-meeting-9h30-to-12h30#avoiding-issues-with-changelog).

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

### Added

- Added contrapostion lemmas involving propositions: `contra_not`, `contraPnot`, `contraTnot`, `contraNnot`, `contraPT`, `contra_notT`, `contra_notN`, `contraPN`, `contraFnot`, `contraPF` and `contra_notF` in ssrbool.v and `contraPeq`, `contra_not_eq`, `contraPneq`, and `contra_neq_not` in eqtype.v
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

- in `poly.v`, new lemma `commr_horner`.

- in `bigop.v` new lemma `big_uncond`. The ideal name is `big_rmcond`
  but it has just been deprecated from its previous meaning (see
  Changed section) so as to reuse it in next mathcomp release.

- in `bigop.v` new lemma `big_uncond_in` is a new alias of
  `big_rmcond_in` for the sake of uniformity, but it is already
  deprecated and will be removed two releases from now.

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


### Renamed

- `big_rmcond` -> `big_rmcond_in` (cf Changed section)

### Removed

### Infrastructure

### Misc
