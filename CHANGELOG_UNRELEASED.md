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

- in `finset.v`
  + definitions `set_of` and `setTfor`
    (phantom trick now useless with reverse coercions)

- in `generic_quotient.v`
  + `pi_phant` -> `pi_subdef`
  + `quot_type_subdef` -> `quot_type_of`

- in `fingroup.v`
  + definitions `group_of`, `group_setT`, `setT_group`
    (phantom trick now useless with reverse coercions)

- in `perm.v`
  + definition `perm_of` (phantom trick now useless with reverse coercions)

- in `ssralg.v`
  + definitions `char`, `null_fun_head`, `in_alg_head`
    (phantom trick now useless with reverse coercions)

- in `finalg.v`
  + definitions `unit_of`
    (phantom trick now useless with reverse coercions)

- in `matrix.v`
  + definitions `GLtype`, `GLval`, `GLgroup` and `GLgroup_group`
    (phantom trick now useless with reverse coercions)
- in `alt.v`
  + definitions `Sym`, `Sym_group`, `Alt`, `Alt_group`
    (phantom trick now useless with reverse coercions)

- in `qpoly.v`
  + definitions `polyn`
    (phantom trick now useless with reverse coercions)

- in `vector.v`
  + definitions `vector_axiom_def`, `space`, `vs2mx`, `pred_of_vspace`
    (phantom trick now useless with reverse coercions)

- in `fieldext.v`
  + definition `baseField_type`
    (phantom trick now useless with reverse coercions)

### Renamed

- in `ring_quotient.v`
  + `Quotient.type` -> `Quotient.quot`

- in `qpoly.v`
  + `npoly_of` -> `npoly` (and removed phantom)
  + `NPoly_of` -> `NPoly` (and removed phantom)
  + `npoly` -> `mk_npoly`

### Removed

- in `poly.v`
  + definition `poly_of` (phantom trick now useless with reverse coercions)

- in `eqtype.v`
  + definition `sub_type_of` (phantom trick now useless with reverse coercions)

- in `order.v`
  + definition `SetSubsetOrder.type_of` (phantom trick now useless with reverse coercions)

- in `fraction.v`
  + definition `ratio_of` (phantom trick now useless with reverse coercions)
  + definition `FracField.type_of` (phantom trick now useless with reverse coercions)

- in `ring_quotient.v`
  + definition `Quotient.type_of` (phantom trick now useless with reverse coercions)

- in `falgebra.v`
  + definition `aspace_of` (phantom trick now useless with reverse coercions)

### Deprecated

- in `vector.v`
  + notation `vector_axiom`, use `Vector.axiom` instead

### Infrastructure

### Misc

