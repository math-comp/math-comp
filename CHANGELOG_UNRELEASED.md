# Changelog (unreleased)

To avoid having old PRs put changes into the wrong section of the CHANGELOG,
new entries now go to the present file as discussed
[here](https://github.com/math-comp/math-comp/wiki/Agenda-of-the-April-23rd-2019-meeting-9h30-to-12h30#avoiding-issues-with-changelog).

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

### Added

- in `path.v`, added lemma `sortedP`
- in `seq.v`, added statement `size_take_min`.

- in `ssralg.v`
  + number notation in scope ring_scope, numbers such as `12` or `42`
    are now read as `12%:R` or `42%:R`

- in `rat.v`
  + Number Notation for numbers of the form `-? [0-9][0-9_]* ([.][0-9_]+)?`
    in scope `rat_scope` (for instance 12%Q or 3.14%Q)

- in `ssrint.v`
  + number notation in scope ring_scope, numbers such as `-12` are now
    read as `(-12)%:~R`

### Changed

- in `rat.v`
  + `zeroq` and `oneq` (hence `0%Q` and `1%Q`) are now the evaluation
    of terms `fracq (0, 1)` and `fracq (1, 1)` (and not the term
    themselves), the old and new values are convertible and can be
    easily converted with `rewrite -[0%Q]valqK -[1%Q]valqK`

### Renamed

### Removed

### Infrastructure

### Misc
