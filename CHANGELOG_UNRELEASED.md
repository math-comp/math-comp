# Changelog (unreleased)

To avoid having old PRs put changes into the wrong section of the CHANGELOG,
new entries now go to the present file as discussed
[here](https://github.com/math-comp/math-comp/wiki/Agenda-of-the-April-23rd-2019-meeting-9h30-to-12h30#avoiding-issues-with-changelog).

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

### Added

- Added fixpoint and cofixpoint constructions to `finset`: `fixset`,
  `cofixset` and `fix_order`, with a few theorems about them

- Added library `finmap` which contains finite sets on a `choiceType`,
  finite maps and finitely supported functions with domain in a
  `choiceType` and codomain in an `eqType`.
  See the header of `ssreflect/finmap.v` for a detailed documentation.

- Added library `multiset` which contains multiset on a `choiceType`.
  See the header of `ssreflect/multiset.v` for a detailed documentation.

### Changed

- `eqVneq` lemma is changed from `{x = y} + {x != y}` to
  `eq_xor_neq x y (y == x) (x == y)`, on which a case analysis performs
  simultaneous replacement of expressions of the form `x == y` and `y == x`
  by `true` or `false`, while keeping the ability to use it in the way
  it was used before.
