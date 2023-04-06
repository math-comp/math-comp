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

- in `ssralg.v`:
  + `rmorphX` -> `rmorphXn`
- in `fraction.v`:
  + `tofracX` -> `tofracXn`
- in `mxrepresentation.v`:
  + `mxval_grootX` -> `mxval_grootXn`
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
  + `ltr_expn2r` -> `ltrXn2r`
  + `ler_expn2r` -> `lerXn2r`
  + `lter_expn2r` -> `lterXn2r`
  + `ler_pmul` -> `ler_pM`
  + `ltr_pmul` -> `ltr_pM`
  + `ler_pinv` -> `ler_pV2`
  + `ler_ninv` -> `ler_nV2`
  + `ltr_pinv` -> `ltr_pV2`
  + `ltr_ninv` -> `ltr_nV2`
  + `ler_pmul2l` -> `ler_pM2l`
  + `ltr_pmul2l` -> `ltr_pM2l`
  + `lter_pmul2l` -> `lter_pM2l`
  + `ler_pmul2r` -> `ler_pM2r`
  + `ltr_pmul2r` -> `ltr_pM2r`
  + `lter_pmul2r` -> `lter_pM2r`
  + `ler_nmul2l` -> `ler_nM2l`
  + `ltr_nmul2l` -> `ltr_nM2l`
  + `lter_nmul2l` -> `lter_nM2l`
  + `ler_nmul2r` -> `ler_nM2r`
  + `ltr_nmul2r` -> `ltr_nM2r`
  + `lter_nmul2r` -> `lter_nM2r`
  + `lef_pinv` -> `lef_pV2`
  + `lef_ninv` -> `lef_nV2`
  + `ltf_pinv` -> `ltf_pV2`
  + `ltf_ninv` -> `ltf_nV2`
  + `ltef_pinv` -> `ltef_pV2`
  + `ltef_ninv` -> `ltef_nV2`
  + `minr_pmulr` -> `minr_pMr`
  + `maxr_pmulr` -> `maxr_pMr`
  + `minr_pmull` -> `minr_pMl`
  + `maxr_pmull` -> `maxr_pMl`
  + `ltr_wpexpn2r` -> `ltr_wpXn2r`
  + `ler_pexpn2r` -> `ler_pXn2r`
  + `ltr_pexpn2r` -> `ltr_pXn2r`
  + `lter_pexpn2r` -> `lter_pXn2r`
  + `ger_pmull` -> `ger_pMl`
  + `gtr_pmull` -> `gtr_pMl`
  + `ger_pmulr` -> `ger_pMr`
  + `gtr_pmulr` -> `gtr_pMr`
  + `ler_pmull` -> `ler_pMl`
  + `ltr_pmull` -> `ltr_pMl`
  + `ler_pmulr` -> `ler_pMr`
  + `ltr_pmulr` -> `ltr_pMr`
  + `ger_nmull` -> `ger_nMl`
  + `gtr_nmull` -> `gtr_nMl`
  + `ger_nmulr` -> `ger_nMr`
  + `gtr_nmulr` -> `gtr_nMr`
  + `ler_nmull` -> `ler_nMl`
  + `ltr_nmull` -> `ltr_nMl`
  + `ler_nmulr` -> `ler_nMr`
  + `ltr_nmulr` -> `ltr_nMr`
  + `leif_pmul` -> `leif_pM`
  + `leif_nmul` -> `leif_nM`
  + `eqr_expn2` -> `eqrXn2`
  + `real_maxr_nmulr` -> `real_maxr_nMr`
  + `real_minr_nmulr` -> `real_minr_nMr`
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
  + `maxr_nmulr` -> `maxr_nMr`
  + `minr_nmulr` -> `minr_nMr`
  + `minr_nmull` -> `minr_nMl`
  + `maxr_nmull` -> `maxr_nMl`
  + `ler_iexpn2l` -> `ler_iXn2l`
  + `ltr_iexpn2l` -> `ltr_iXn2l`
  + `lter_iexpn2l` -> `lter_iXn2l`
  + `ler_eexpn2l` -> `ler_eXn2l`
  + `ltr_eexpn2l` -> `ltr_eXn2l`
  + `lter_eexpn2l` -> `lter_eXn2l`
  + `ler_wpmul2l` -> `ler_wpM2l`
  + `ler_wpmul2r` -> `ler_wpM2r`
  + `ler_wnmul2l` -> `ler_wnM2l`
  + `ler_wnmul2r` -> `ler_wnM2r`
  + `ler_pemull` -> `ler_peMl`
  + `ler_nemull` -> `ler_neMl`
  + `ler_pemulr` -> `ler_peMr`
  + `ler_nemulr` -> `ler_neMr`
  + `ler_iexpr` -> `ler_iXnr`
  + `ltr_iexpr` -> `ltr_iXnr`
  + `lter_iexpr` -> `lter_iXnr`
  + `ler_eexpr` -> `ler_eXnr`
  + `ltr_eexpr` -> `ltr_eXnr`
  + `lter_eexpr` -> `lter_eXnr`
  + `lter_expr` -> `lter_Xnr`
  + `ler_wiexpn2l` -> `ler_wiXn2l`
  + `ler_weexpn2l` -> `ler_weXn2l`
  + `ler_pimull` -> `ler_piMl`
  + `ler_nimull` -> `ler_niMl`
  + `ler_pimulr` -> `ler_piMr`
  + `ler_nimulr` -> `ler_niMr`
  + `lteif_pdivl_mulr` -> `lteif_pdivlMr`
  + `lteif_pdivr_mulr` -> `lteif_pdivrMr`
  + `lteif_pdivl_mull` -> `lteif_pdivlMl`
  + `lteif_pdivr_mull` -> `lteif_pdivrMl`
  + `lteif_ndivl_mulr` -> `lteif_ndivlMr`
  + `lteif_ndivr_mulr` -> `lteif_ndivrMr`
  + `lteif_ndivl_mull` -> `lteif_ndivlMl`
  + `lteif_ndivr_mull` -> `lteif_ndivrMl`
  + `ler_pdivl_mulr` -> `ler_pdivlMr`
  + `ltr_pdivl_mulr` -> `ltr_pdivlMr`
  + `lter_pdivl_mulr` -> `lter_pdivlMr`
  + `ler_pdivr_mulr` -> `ler_pdivrMr`
  + `ltr_pdivr_mulr` -> `ltr_pdivrMr`
  + `lter_pdivr_mulr` -> `lter_pdivrMr`
  + `ler_pdivl_mull` -> `ler_pdivlMl`
  + `ltr_pdivl_mull` -> `ltr_pdivlMl`
  + `lter_pdivl_mull` -> `lter_pdivlMl`
  + `ler_pdivr_mull` -> `ler_pdivrMl`
  + `ltr_pdivr_mull` -> `ltr_pdivrMl`
  + `lter_pdivr_mull` -> `lter_pdivrMl`
  + `ler_ndivl_mulr` -> `ler_ndivlMr`
  + `ltr_ndivl_mulr` -> `ltr_ndivlMr`
  + `lter_ndivl_mulr` -> `lter_ndivlMr`
  + `ler_ndivr_mulr` -> `ler_ndivrMr`
  + `ltr_ndivr_mulr` -> `ltr_ndivrMr`
  + `lter_ndivr_mulr` -> `lter_ndivrMr`
  + `ler_ndivl_mull` -> `ler_ndivlMl`
  + `ltr_ndivl_mull` -> `ltr_ndivlMl`
  + `lter_ndivl_mull` -> `lter_ndivlMl`
  + `ler_ndivr_mull` -> `ler_ndivrMl`
  + `ltr_ndivr_mull` -> `ltr_ndivrMl`
  + `lter_ndivr_mull` -> `lter_ndivrMl`
  + `eqr_pmuln2r` -> `eqr_pMn2r`
  + `ler_muln2r` -> `lerMn2r`
  + `ler_pmuln2r` -> `ler_pMn2r`
  + `ler_pmuln2l` -> `ler_pMn2l`
  + `ltr_pmuln2r` -> `ltr_pMn2r`
  + `ltr_wmuln2r` -> `ltr_wMn2r`
  + `ler_wmuln2r` -> `ler_wMn2r`
  + `ltr_wpmuln2r` -> `ltr_wpMn2r`
  + `ler_wpmuln2l` -> `ler_wpMn2l`
  + `ler_wnmuln2l` -> `ler_wnMn2l`
  + `ltr_muln2r` -> `ltrMn2r`
  + `eqr_muln2r` -> `eqrMn2r`
  + `ltr_pmuln2l` -> `ltr_pMn2l`
  + `ler_nmuln2l` -> `ler_nMn2l`
  + `ltr_nmuln2l` -> `ltr_nMn2l`
  + `normC_add_eq` -> `normCDeq`
  + `normC_sub_eq` -> `normCBeq`
  + `leif_subLR` -> `leifBLR`
  + `leif_subRL` -> `leifBRL`
- in `ssrint.v`:
  + `leq_add_dist` -> `leqD_dist`
  + `lez_add1r` -> `lez1D`
  + `lez_addr1` -> `lezD1`
  + `ltz_add1r` -> `ltz1D`
  + `ltz_addr1` -> `ltzD1`
  + `oppz_add` -> `oppzD`
  + `leqif_add_distz` -> `leqifD_distz`
  + `leqif_add_dist` -> `leqifD_dist`
  + `ler_pmulz2r` -> `ler_pMz2r`
  + `ler_pmulz2l` -> `ler_pMz2l`
  + `ler_wpmulz2r` -> `ler_wpMz2r`
  + `ler_wpmulz2l` -> `ler_wpMz2l`
  + `ler_wnmulz2l` -> `ler_wnMz2l`
  + `ler_nmulz2r` -> `ler_nMz2r`
  + `ltr_pmulz2r` -> `ltr_pMz2r`
  + `ler_nmulz2l` -> `ler_nMz2l`
  + `ltr_pmulz2l` -> `ltr_pMz2l`
  + `ltr_nmulz2r` -> `ltr_nMz2r`
  + `ltr_nmulz2l` -> `ltr_nMz2l`
  + `ler_wnmulz2r` -> `ler_wnMz2r`
  + `ler_wpexpz2r` -> `ler_wpXz2r`
  + `ler_wnexpz2r` -> `ler_wnXz2r`
  + `ler_pexpz2r` -> `ler_pXz2r`
  + `ltr_pexpz2r` -> `ltr_pXz2r`
  + `ler_nexpz2r` -> `ler_nXz2r`
  + `ltr_nexpz2r` -> `ltr_nXz2r`
  + `ler_wpiexpz2l` -> `ler_wpiXz2l`
  + `ler_wniexpz2l` -> `ler_wniXz2l`
  + `ler_wpeexpz2l` -> `ler_wpeXz2l`
  + `ler_wneexpz2l` -> `ler_wneXz2l`
  + `ler_weexpz2l` -> `ler_weXz2l`
  + `ler_piexpz2l` -> `ler_piXz2l`
  + `ltr_piexpz2l` -> `ltr_piXz2l`
  + `ler_niexpz2l` -> `ler_niXz2l`
  + `ltr_niexpz2l` -> `ltr_niXz2l`
  + `ler_eexpz2l` -> `ler_eXz2l`
  + `ltr_eexpz2l` -> `ltr_eXz2l`
  + `eqr_expz2` -> `eqrXz2`
  + `exprz_pmulzl` -> `exprz_pMzl`
  + `lteif_pmul2l` -> `lteif_pM2l`
  + `lteif_pmul2r` -> `lteif_pM2r`
  + `lteif_nmul2l` -> `lteif_nM2l`
  + `lteif_nmul2r` -> `lteif_nM2r`
  + `ler_paddl` -> `ler_wpDl`
  + `ltr_paddl` -> `ltr_wpDl`
  + `ltr_spaddl` -> `ltr_pwDl`
  + `ltr_spsaddl` -> `ltr_pDl`
  + `ler_naddl` -> `ler_wnDl`
  + `ltr_naddl` -> `ltr_wnDl`
  + `ltr_snaddl` -> `ltr_nwDl`
  + `ltr_snsaddl` -> `ltr_nDl`
  + `ler_paddr` -> `ler_wpDr`
  + `ltr_paddr` -> `ltr_wpDr`
  + `ltr_spaddr` -> `ltr_pwDr`
  + `ltr_spsaddr` -> `ltr_pDr`
  + `ler_naddr` -> `ler_wnDr`
  + `ltr_naddr` -> `ltr_wnDr`
  + `ltr_snaddr` -> `ltr_nwDr`
  + `ltr_snsaddr` -> `ltr_nDr`
- in `interval.v`:
  + `in_segment_addgt0Pr` -> `in_segmentDgt0Pr`
  + `in_segment_addgt0Pl` -> `in_segmentDgt0Pl`

### Removed

### Infrastructure

### Misc

