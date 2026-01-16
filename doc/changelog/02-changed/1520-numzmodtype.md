- in `orderedzmod.v`
  + definition `pos_num_pred`, `pos_num`, `neg_num_pred`, `neg_num`,
    `nneg_num_pred`, `nneg_num`, `npos_num_pred`, `npos_num`,
    `real_num_pred` and `real_num` generalized from `porderZmodType`
    to `porderNmodeType`
  + lemmas `subr_ge0`, `oppr_ge0`, `le0r`, `addr_ge0`, `posrE`,
    `nnegrE`, `realE`, `negrE`, `nposrE`, `lt0r`, `lt0r_neq0`,
    `ltr0_neq0`, `big_real`, `subr_gt0`, `subr_le0`, `subr_lt0`,
    `comparable0r`, `comparabler0`, `subr_comparable0`,
    `comparablerE`, `lerN2`, `lerNr`, `ltrNr`, `lerNl`, `ltrNl`,
    `oppr_gt0`, `oppr_le0`, `oppr_lt0`, `gtrN`, `ge0_cp`, `gerN`,
    `gt0_cp`, `le0_cp`, `lt0_cp`, `ger0_real`, `ler0_real`,
    `gtr0_real`, `ltr0_real`, `real0`, `lerD2l`, `lerD2r`, `ltrD2l`,
    `ltrD2r`, `lerD`, `ler_ltD`, `ltr_leD`, `ltrD`, `lerB`, `ler_ltB`,
    `ltr_leB`, `ltrB`, `lerBlDr`, `ltrBlDr`, `lerBrDr`, `ltrBrDr`,
    `lerBlDl`, `ltrBlDl`, `lerBrDl`, `ltrBrDl`, `lerDl`, `ltrDl`,
    `lerDr`, `ltrDr`, `gerDl`, `gerBl`, `gtrDl`, `gtrBl`, `gerDr`,
    `gtrDr`, `ler_wpDl`, `ltr_wpDl`, `ltr_pwDl`, `ltr_pDl`,
    `ler_wnDl`, `ltr_wnDl`, `ltr_nwDl`, `ltr_nDl`, `ler_wpDr`,
    `ltr_wpDr`, `ltr_pwDr`, `ltr_pDr`, `ler_wnDr`, `ltr_wnDr`,
    `ltr_nwDr`, `ltr_nDr`, `paddr_eq0`, `naddr_eq0`, `addr_ss_eq0`,
    `sumr_ge0`, `sumr_le0`, `ler_sum`, `ler_sum_nat`, `ltr_sum`,
    `ltr_sum_nat`, `psumr_eq0`, `psumr_eq0P`, `psumr_neq0`,
    `psumr_neq0P`, `ler_pMn2l`, `ltr_pMn2l`, `ler_nMn2l`, `ltr_nMn2l`,
    `ler_wpMn2l`, `ler_wnMn2l`, `ltr_wpMn2r`, `ler_wMn2r`,
    `mulrn_wge0`, `mulrn_wle0`, `lteifNl`, `lteifNr`, `lteif0Nr`,
    `lteifNr0`, `lteifN2`, `lteifD2l`, `lteifD2r`, `lteifBlDr`,
    `lteifBrDr`, `lteifBlDl`, `lteifBrDl`, `addr_min_max`,
    `addr_max_min`, `minr_to_max` and `maxr_to_min` generalized from
    `numDomainType` to `porderedZmodType`
  + multirules `subr_lte0`, `subr_gte0`, `subr_cp0`, `lterNr`,
    `lterNl`, `oppr_gte0`, `oppr_lte0`, `oppr_cp0`, `lterNE`, `lerD2`,
    `ltrD2`, `lterD2`, `lerBDr`, `ltrBDr`, `lterBDr`, `lerBDl`,
    `ltrBDl`, `lterBDl`, `cprD`, `lteifD2`, `lteifBDr` and `lteifBDl`
    generalized from `numDomainType` to `porderedZmodType`
  + lemmas `sum_real`, `comparabler_trans`, `ler_leVge`, `real_leVge`,
    `real_comparable`, `realB`, `realN`, `realBC`, `realD`,
    `real_ltNge`, `real_leNgt`, `max_real`, `min_real`, `bigmax_real`,
    `bigmin_real`, `real_neqr_lt`, `lerB_real`, `gerB_real`,
    `ler_real`, `ger_real`, `Nreal_leF`, `Nreal_geF`, `Nreal_ltF`,
    `Nreal_gtF`, `real_wlog_ler`, `real_wlog_ltr`, `real_mono`,
    `real_nmono`, `real_mono_in`, `real_nmono_in`, `realn_mono`,
    `realn_nmono`, `realn_mono_in`, `realn_nmono_in`, `ger_leVge`,
    `real_oppr_max`, `real_oppr_min`, `real_addr_minl`,
    `real_addr_minr`, `real_addr_maxl` and `real_addr_maxr`
    generalized from `numDomainType` to `numZmodType`
    ([#1520](https://github.com/math-comp/math-comp/pull/1520)).
