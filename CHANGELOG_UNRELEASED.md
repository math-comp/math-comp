# Changelog (unreleased)

To avoid having old PRs put changes into the wrong section of the CHANGELOG,
new entries now go to the present file as discussed
[here](https://github.com/math-comp/math-comp/wiki/Agenda-of-the-April-23rd-2019-meeting-9h30-to-12h30#avoiding-issues-with-changelog).

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

### Added

- in `finset.v`
  + lemmas `big_set1E`, `big_imset_idem`.

- in `order.v`
  + lemmas `bigmin_mkcondl`, `bigmin_mkcondr`, `bigmax_mkcondl`,
    `bigmax_mkcondr`, `bigmin_le_id`, `bigmax_ge_id`, `bigmin_eq_id`,
    `bigmax_eq_id`, `bigminUl`, `bigminUr`, `bigmaxUl`, `bigmaxUr`,
    `bigminIl`, `bigminIr`, `bigmaxIl`, `bigmaxIr`, `bigminD`,
    `bigmaxD`, `bigminU`, `bigmaxU`, `bigmin_set1`, `bigmax_set1`,
    `bigmin_imset`, `bigmax_imset`.

### Changed

- in `finset.v`
  + generalized lemmas `big_set0` and `big_set` from semigroups
    to arbitrary binary operators

- in `ssrnum.v`
  + generalize `ler_sqrt`
  + generalize `ler_psqrt` to use `nneg` instead of `pos`

### Renamed

### Removed

### Deprecated

### Infrastructure

### Misc

