# Changelog (unreleased)

To avoid having old PRs put changes into the wrong section of the CHANGELOG,
new entries now go to the present file as discussed
[here](https://github.com/math-comp/math-comp/wiki/Agenda-of-the-April-23rd-2019-meeting-9h30-to-12h30#avoiding-issues-with-changelog).

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

### Added

- in `perm.v`
  + lemmas `perm_on_id`, `perm_onC`, `tperm_on`

- in `bigop.v`
  + lemma `big_if`

- in `seq.v`
  + lemmas `sumn_ncons`, `sumn_set_nth`, `sumn_set_nth_ltn`,
    `sumn_set_nth0`

- in `finset.v`
  + lemma `bigA_distr`

- in `poly.v`
  + lemmas `coef_prod_XsubC`, `coefPn_prod_XsubC`, `coef0_prod_XsubC`

- in `ssralg.v`
  + `bool` is now canonically a `fieldType` with additive law `addb` and
    multiplicative law `andb`

- in `finalg.v`
  + `bool` is now canonically a `finFieldType` and a `decFieldType`.

### Changed

- in `order.v`
  + fix lemmas `eq_bigmax` and `eq_bigmin` to respect given predicates

- in `order.v`
  + fix `\meet^p_` and `\join^p_` notations
  + fix the scope of `n.-tuplelexi` notations

- in `intdiv.v`
  + `zcontents` is now of type `{poly int} -> int`
  + `divz` is now of type `int -> int -> int`

- in `order.v`
  + fix the definition of `max_fun` (notation `\max`)
    which was equal to `min_fun`

- in `ssrnat.v`
  + change the doubling and halving operators to be left-associative

- in `seq.v`,
  + notations `[seq x <- s | C ]`, `[seq x <- s | C1 & C2 ]`, `[seq E
    | i <- s ]`, `[seq E | i <- s & C ]`, `[seq E : R | i <- s ]`,
    `[seq E : R | i <- s & C ]`, `[seq E | x <- s, y <- t ]`, `[seq
    E : R | x <- s, y <- t ]` now support destructuring patterns in
    binder positions.

- in `fintype.v`,
  + notations `[seq F | x in A ]` and `[seq F | x ]` now support destructuring
    patterns in binder positions.  In the case of `[seq F | x ]` and `[seq F |
    x : T ]`, type inference on `x` now occurs earlier, meaning that implicit
    types and typeclass resolution in `T` will take precedence over unification
    constraints arising from typechecking `x` in `F`.  This may result in
    occasional incompatibilities.

### Renamed

### Removed

### Infrastructure

### Misc

