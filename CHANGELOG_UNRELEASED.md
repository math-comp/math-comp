# Changelog (unreleased)

To avoid having old PRs put changes into the wrong section of the CHANGELOG,
new entries now go to the present file as discussed
[here](https://github.com/math-comp/math-comp/wiki/Agenda-of-the-April-23rd-2019-meeting-9h30-to-12h30#avoiding-issues-with-changelog).

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

### Added

- in `prime.v` 
  + theorems `trunc_log0`, `trunc_log1`, `trunc_log_eq0`,
    `trunc_log_gt0`, `trunc_log0n`, `trunc_log1n`, `leq_trunc_log`,
    `trunc_log_eq`, `trunc_lognn`, `trunc_expnK`,  `trunc_logMp`,
    `trunc_log2_double`, `trunc_log2S`
  + definition `up_log` 
  + theorems `up_log0`, `up_log1`, `up_log_eq0`, `up_log_gt0`, 
    `up_log_bounds` , `up_logP`, `up_log_gtn`, `up_log_min`,
    `leq_up_log`, `up_log_eq`, `up_lognn`, `up_expnK`, `up_logMp`,
    `up_log2_double`, `up_log2S`, `up_log_trunc_log`, `trunc_log_up_log`
     
### Changed

- in `prime.v` 
  + definition `trunc_log` now it is 0 when p <= 1 

- in `order.v`
  + fix `[distrLatticeType of T with disp]` notation

### Renamed

### Removed

### Infrastructure

### Misc
