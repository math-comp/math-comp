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

- in `ssrint.v`
  + number notation in scope ring_scope, numbers such as `-12` are now
    read as `(-12)%:~R`

### Changed

### Renamed

### Removed

### Infrastructure

### Misc
