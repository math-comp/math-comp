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
  + `ler_oppr` -> `lerNr`
  + `ltr_oppr` -> `ltrNr`
  + `lter_oppr` -> `lterNr`
  + `ler_oppl` -> `lerNl`
  + `ltr_oppl` -> `ltrNl`
  + `lter_oppl` -> `lterNl`
  + `lteif_opp2` -> `lteifN2`
  + `ler_add2l` -> `lerD2l`
  + `ler_add2r` -> `lerD2r`
  + `ltr_add2l` -> `ltrD2l`
  + `ltr_add2r` -> `ltD2r`
  + `ler_add2` -> `lerD2`
  + `ltr_add2` -> `ltrD2`
  + `lter_add2` -> `lterD2r`
  + `ler_add` -> `lerD`
  + `ler_lt_add` -> `ler_ltD`
  + `ltr_le_add` -> `ltr_leD`
  + `ltr_add` -> `ltrD`
  + `ler_sub` -> `lerB`
  + `ler_lt_sub` -> `ler_ltB`
  + `ltr_le_sub` -> `ltr_leB`
  + `ltr_sub` -> `ltrB`
  + `ler_subl_addr` -> `lerBlDr`
  + `ltr_subl_addr` -> `ltrBlDr`
  + `ler_subr_addr` -> `lerBrDr`
  + `ltr_subr_addr` -> `ltrBrDr`
  + `ler_sub_addr` -> `lerBDr`
  + `ltr_sub_addr` -> `ltrBDr`
  + `lter_sub_addr` -> `lterBDr`
  + `ler_subl_addl` -> `lerBlDl`
  + `ltr_subl_addl` -> `ltrBlDl`
  + `ler_subr_addl` -> `lerBrDl`
  + `ltr_subr_addl` -> `ltrBrDl`
  + `ler_sub_addl` -> `lerBDl`
  + `ltr_sub_addl` -> `ltrBDl`
  + `lter_sub_addl` -> `lterBDl`
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
  + `ler_norm_add` -> `ler_normD`
  + `ler_norm_sub` -> `ler_normB`
  + `leif_add` -> `leifD`
  + `gtr_opp` -> `gtrN`
  + `lteif_oppl` -> `lteifNl`
  + `lteif_oppr` -> `lteifNr`
  + `lteif_0oppr` -> `lteif0Nr`
  + `lteif_oppr0` -> `lteifNr0`
  + `lter_oppE` -> `lterNE`
  + `ler_dist_add` -> `ler_distD`
  + `ler_dist_norm_add` -> `ler_dist_normD`
  + `ler_sub_norm_add` -> `lerB_normD`
  + `ler_sub_dist` -> `lerB_dist`
  + `ler_sub_real` -> `lerB_real`
  + `ger_sub_real` -> `gerB_real`
  + `ltr_expn2r` -> `ltrX2r`
  + `ler_expn2r` -> `lerX2r`
  + `lter_expn2r` -> `lterX2r`
  + `ler_pmul` -> `lerpM`
  + `ltr_pmul` -> `ltrpM`
  + `ler_pinv` -> `lerpV2`
  + `ler_ninv` -> `lernV2`
  + `ltr_pinv` -> `ltrpV2`
  + `ltr_ninv` -> `ltrnV2`
  + `ler_pmul2l` -> `lerpM2l`
  + `ltr_pmul2l` -> `ltrpM2l`
  + `lter_pmul2l` -> `lterpM2l`
  + `ler_pmul2r` -> `lerpM2r`
  + `ltr_pmul2r` -> `ltrpM2r`
  + `lter_pmul2r` -> `lterpM2r`
  + `ler_nmul2l` -> `lernM2l`
  + `ltr_nmul2l` -> `ltrnM2l`
  + `lter_nmul2l` -> `lternM2l`
  + `ler_nmul2r` -> `lernM2r`
  + `ltr_nmul2r` -> `ltrnM2r`
  + `lter_nmul2r` -> `lternM2r`
  + `lef_pinv` -> `lefpV2`
  + `lef_ninv` -> `lefnV2`
  + `ltf_pinv` -> `ltfpV2`
  + `ltf_ninv` -> `ltfnV2`
  + `ltef_pinv` -> `ltefpV2`
  + `ltef_ninv` -> `ltefnV2`
  + `minr_pmulr` -> `minrpMr`
  + `maxr_pmulr` -> `maxrpMr`
  + `minr_pmull` -> `minrpMl`
  + `maxr_pmull` -> `maxrpMl`
  + `ltr_wpexpn2r` -> `ltrwpX2r`
  + `ler_pexpn2r` -> `lerpX2r`
  + `ltr_pexpn2r` -> `ltrpX2r`
  + `lter_pexpn2r` -> `lterpX2r`
  + `ger_pmull` -> `gerpMl`
  + `gtr_pmull` -> `gtrpMl`
  + `ger_pmulr` -> `gerpMr`
  + `gtr_pmulr` -> `gtrpMr`
  + `ler_pmull` -> `lerpMl`
  + `ltr_pmull` -> `ltrpMl`
  + `ler_pmulr` -> `lerpMr`
  + `ltr_pmulr` -> `ltrpMr`
  + `ger_nmull` -> `gernMl`
  + `gtr_nmull` -> `gtrnMl`
  + `ger_nmulr` -> `gernMr`
  + `gtr_nmulr` -> `gtrnMr`
  + `ler_nmull` -> `lernMl`
  + `ltr_nmull` -> `ltrnMl`
  + `ler_nmulr` -> `lernMr`
  + `ltr_nmulr` -> `ltrnMr`
  + `leif_pmul` -> `leifpM`
  + `leif_nmul` -> `leifnM`
  + `eqr_expn2` -> `eqrX2`
  + `real_maxr_nmulr` -> `real_maxrnMr`
  + `real_minr_nmulr` -> `real_minrnMr`
  + `real_minr_nmull` -> `real_minrnMl`
  + `real_maxr_nmull` -> `real_maxrnMl`
  + `real_ltr_distl_addr` -> `real_ltr_distlDr`
  + `real_ler_distl_addr` -> `real_ler_distlDr`
  + `real_ltr_distlC_addr` -> `real_ltr_distlCDr`
  + `real_ler_distlC_addr` -> `real_ler_distlCDr`
  + `real_ltr_distl_subl` -> `real_ltr_distlBl`
  + `real_ler_distl_subl` -> `real_ler_distlBl`
  + `real_ltr_distlC_subl` -> `real_ltr_distlCBl`
  + `real_ler_distlC_subl` -> `real_ler_distlCBl`
  + `ltr_distl_addr` -> `ltr_distlDr`
  + `ler_distl_addr` -> `ler_distlDr`
  + `ltr_distlC_addr` -> `ltr_distlCDr`
  + `ler_distlC_addr` -> `ler_distlCDr`
  + `ltr_distl_subl` -> `ltr_distlBl`
  + `ler_distl_subl` -> `ler_distlBl`
  + `ltr_distlC_subl` -> `ltr_distlCBl`
  + `ler_distlC_subl` -> `ler_distlCBl`
  + `maxr_nmulr` -> `maxrnMr`
  + `minr_nmulr` -> `minrnMr`
  + `minr_nmull` -> `minrnMl`
  + `maxr_nmull` -> `maxrnMl`
- in `ssrint.v`:
  + `leq_add_dist` -> `leqD_dist`
  + `lez_add1r` -> `lez1D`
  + `lez_addr1` -> `lezD1`
  + `ltz_add1r` -> `ltz1D`
  + `ltz_addr1` -> `ltzD1`

### Removed

### Infrastructure

### Misc

