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

### Renamed

- in `ssrnum.v`:
  + `ler_opp2` -> `lerN2`
  + `ltr_opp2` -> `ltrN2`
  + `lter_opp2` -> `lterN2`
  + `ler_oppr` -> `lerN`
  + `ltr_oppr` -> `ltrN`
  + `lter_oppr` -> `lterN`
  + `ler_oppl` -> `leNr`
  + `ltr_oppl` -> `ltNr`
  + `lter_oppl` -> `lteNr`
  + `lteif_opp2` -> `lteifN2`
  + `ler_add2l` -> `lerD2`
  + `ler_add2r` -> `leD2r`
  + `ltr_add2l` -> `ltrD2`
  + `ltr_add2r` -> `ltD2r`
  + `ler_add2` -> `lerD2r`
  + `ltr_add2` -> `ltrD2r`
  + `lter_add2` -> `lterD2r`
  + `ler_add` -> `lerD`
  + `ler_lt_add` -> `ler_ltD`
  + `ltr_le_add` -> `ltr_leD`
  + `ltr_add` -> `ltrD`
  + `ler_sub` -> `lerB`
  + `ler_lt_sub` -> `ler_ltB`
  + `ltr_le_sub` -> `ltr_leB`
  + `ltr_sub` -> `ltrB`
  + `ler_subl_addr` -> `lerBDr`
  + `ltr_subl_addr` -> `ltrBDr`
  + `ler_subr_addr` -> `leBrDr`
  + `ltr_subr_addr` -> `ltBrDr`
  + `ler_sub_addr` -> `leBDr`
  + `ltr_sub_addr` -> `ltBDr`
  + `lter_sub_addr` -> `lteBDr`
  + `ler_subl_addl` -> `lerBrD`
  + `ltr_subl_addl` -> `ltrBrD`
  + `ler_subr_addl` -> `leBrrd`
  + `ltr_subr_addl` -> `ltBrrD`
  + `ler_sub_addl` -> `leBrD`
  + `ltr_sub_addl` -> `ltBrD`
  + `lter_sub_addl` -> `lteBrD`

  + `ler_addl` -> `lerDl`
  + `ltr_addl` -> `ltrDl`
  + `ler_addr` -> `lerDr`
  + `ltr_addr` -> `ltrDr`
  + `ger_addl` -> `gerDl`
  + `gtr_addl` -> `gtrDl`
  + `ger_addr` -> `gerDr`
  + `gtr_addr` -> `gtrDr`
  + `cpr_add` -> `cprD`
  + `lteif_add2l` -> `lteifD2l`
  + `lteif_add2r` -> `lteifD2r`
  + `lteif_add2` -> `lteifD2`
  + `lteif_subl_addr` -> `lteifBlDr`
  + `lteif_subr_addr` -> `lteifBrDr`
  + `lteif_sub_addr` -> `lteifBDr`
  + `lteif_subl_addl` -> `lteifBlDl`
  + `lteif_subr_addl` -> `lteifBrDl`
  + `lteif_sub_addl` -> `lteifBDl`

### Removed

### Infrastructure

### Misc

