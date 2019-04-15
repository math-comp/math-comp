# Changelog (unreleased)

To avoid having old PRs put changes into the wrong section of the CHANGELOG,
new entries now go to the present file as discussed
[here](https://github.com/math-comp/math-comp/wiki/Agenda-of-the-April-23rd-2019-meeting-9h30-to-12h30#avoiding-issues-with-changelog).

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

### Added

- Added map/parametricity theorems about `path`, `sort` and `sorted`:
  `homo_path`, `mono_path`, `homo_path_in`, `mono_path_in`,
  `homo_sorted`, `mono_sorted`, `map_merge`, `merge_map`, `map_sort`,
  `sort_map`, `sorted_map`, `homo_sorted_in`, `mono_sorted_in`,
  `sort_map_in`/

- Added the theorem `perm_iota_sort` to express that the sorting of
  any sequence `s` is equal to a mapping of `iota 0 (size s)` to the
  nth elements of `s`, so that one can still reason on `nat`, even
  though the elements of `s` are not in an `eqType`.

- Added a comment in the documentation to explain `sort` is stable,
  without proving it formally, for now.

### Changed

- Generalized `sort` to non-`eqType`s (as well as `merge`,
  `merge_sort_push`, `merge_sort_pop`), together with all the lemmas
  that did not really rely on an `eqType`: `size_merge`, `size_sort`,
  `merge_path`, `merge_sorted`, `sort_sorted`, `path_min_sorted`
  (which statement was modified to remove the dependency in `eqType`),
  and `order_path_min`.

- `eqVneq` lemma is changed from `{x = y} + {x != y}` to
  `eq_xor_neq x y (y == x) (x == y)`, on which a case analysis performs
  simultaneous replacement of expressions of the form `x == y` and `y == x`
  by `true` or `false`, while keeping the ability to use it in the way
  it was used before.
