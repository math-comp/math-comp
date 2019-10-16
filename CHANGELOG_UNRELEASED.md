# Changelog (unreleased)

To avoid having old PRs put changes into the wrong section of the CHANGELOG,
new entries now go to the present file as discussed
[here](https://github.com/math-comp/math-comp/wiki/Agenda-of-the-April-23rd-2019-meeting-9h30-to-12h30#avoiding-issues-with-changelog).

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

### Added

- Added fixpoint and cofixpoint constructions to `finset`: `fixset`,
  `cofixset` and `fix_order`, with a few theorems about them

- Added functions `tuple_of_finfun`, `finfun_of_tuple`, and their
  "cancellation" lemmas.

- Added theorems `totient_prime` and `Euclid_dvd_prod` in `prime.v`

- Added theorems `ffact_prod`, `prime_modn_expSn` and `fermat_little`
  in `binomial.v`

- Added theorems `flatten_map1` and `allpairs_consr` in `seq.v`.

- Fintype theorems: `fintype0`, `card_le1P`, `mem_card1`,
  `card1P`, `fintype_le1P`, `fintype1`, `fintype1P`.

- Bigop theorems: `big_rmcond`, `bigD1_seq`,
  `big_enum_val_cond`, `big_enum_rank_cond`,
  `big_enum_val`, `big_enum_rank`, `big_set`.

### Changed

- `eqVneq` lemma is changed from `{x = y} + {x != y}` to
  `eq_xor_neq x y (y == x) (x == y)`, on which a case analysis performs
  simultaneous replacement of expressions of the form `x == y` and `y == x`
  by `true` or `false`, while keeping the ability to use it in the way
  it was used before.

- Generalized the `allpairs_catr` lemma to the case where the types of `s`,
  `t1`, and `t2` are non-`eqType`s in `[seq E | i <- s, j <- t1 ++ t2]`.

### Infrastructure

- `Makefile` now supports the `test-suite` and `only` targets. Currently,
  `make test-suite` will verify the implementation of mathematical structures
  and their inheritances of MathComp automatically, by using the `hierarchy.ml`
  utility. One can use the `only` target to build the sub-libraries of MathComp
  specified by the `TGTS` variable, e.g.,
  `make only TGTS="ssreflect/all_ssreflect.vo fingroup/all_fingroup.vo"`.

