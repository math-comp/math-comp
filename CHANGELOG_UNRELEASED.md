# Changelog (unreleased)

To avoid having old PRs put changes into the wrong section of the CHANGELOG,
new entries now go to the present file as discussed
[here](https://github.com/math-comp/math-comp/wiki/Agenda-of-the-April-23rd-2019-meeting-9h30-to-12h30#avoiding-issues-with-changelog).

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

### Added

- in `seq.v`
  + lemma `foldl_foldr`

- in `poly.v`
  + multirule `coefE`
  + lemmas `deg2_poly_canonical`, `deg2_poly_factor`,
    `deg2_poly_root1`, `deg2_poly_root2`,
    `FieldMonic.deg2_poly_canonical`, `FieldMonic.deg2_poly_factor`,
    `FieldMonic.deg2_poly_root1`, `FieldMonic.deg2_poly_root2`

- in `ssrnum.v`
  + lemmas `NumClosed.deg2_poly_factor`, `NumClosed.deg2_poly_root1`,
    `NumClosed.deg2_poly_root2`, `NumClosedMonic.deg2_poly_factor`,
    `NumClosedMonic.deg2_poly_root1`,
    `NumClosedMonic.deg2_poly_root2`, `Real.deg2_poly_min`,
    `Real.deg2_poly_minE`, `Real.deg2_poly_gt0`, `Real.deg2_poly_ge0`,
    `Real.deg2_poly_max`, `Real.deg2_poly_maxE`, `Real.deg2_poly_lt0`,
    `Real.deg2_poly_le0`, `Real.deg2_poly_factor`,
    `Real.deg2_poly_root1`, `Real.deg2_poly_root2`,
    `Real.deg2_poly_noroot`, `Real.deg2_poly_gt0l`,
    `Real.deg2_poly_gt0r`, `Real.deg2_poly_lt0m`,
    `Real.deg2_poly_ge0l`, `Real.deg2_poly_ge0r`,
    `Real.deg2_poly_le0m`, `Real.deg2_poly_lt0l`,
    `Real.deg2_poly_lt0r`, `Real.deg2_poly_gt0m`,
    `Real.deg2_poly_le0l`, `Real.deg2_poly_le0r`,
    `Real.deg2_poly_ge0m`, `RealMonic.deg2_poly_min`,
    `RealMonic.deg2_poly_minE`, `RealMonic.deg2_poly_gt0`,
    `RealMonic.deg2_poly_ge0`, `RealMonic.deg2_poly_factor`,
    `RealMonic.deg2_poly_root1`, `RealMonic.deg2_poly_root2`,
    `RealMonic.deg2_poly_noroot`, `RealMonic.deg2_poly_gt0l`,
    `RealMonic.deg2_poly_gt0r`, `RealMonic.deg2_poly_lt0m`,
    `RealMonic.deg2_poly_ge0l`, `RealMonic.deg2_poly_ge0r`,
    `RealMonic.deg2_poly_le0m`, `deg_le2_poly_delta_ge0`,
    `deg_le2_poly_delta_le0`, `deg_le2_poly_ge0`, `deg_le2_poly_le0`

- new file `archimedean.v`

- in `archimedean.v`
  + new structures `archiNumDomainType`, `archiNumFieldType`,
    `archiClosedFieldType`, `archiDomainType`, `archiRcfType`
  + structure `archiFieldType` (renamed from `archimedeanFieldType`
    from `ssrnum.v`)
  + notations `Num.trunc`, `Num.floor` `Num.ceil`, `Num.nat`,
    `Num.int`
  + notation `Num.bound` (moved from `ssrnum.v`)
  + lemmas `trunc_itv`, `natrE`, `trunc_def`, `natrK`, `truncK`,
    `trunc0`, `trunc1`, `natr_nat`, `natrP`, `truncD`, `truncM`,
    `truncX`, `rpred_nat_num`, `nat_num0`, `nat_num1`,
    `nat_num_semiring`, `Rreal_nat`, `natr_normK`, `trunc_gt0`,
    `trunc0Pn`, `natrge0`, `natrgt0`, `norm_natr`, `natrsum_eq1`,
    `natr_mul_eq1`, `natr_prod_eq1`, `floorP`, `intrE`, `floor_itv`,
    `ge_floor`, `lt_succ_floor`, `floor_def`, `floor_ge_int`,
    `floor_le`, `intrKfloor`, `intr_int`, `intrP`, `intrEfloor`,
    `floorK`, `floor0`, `floor1`, `floorD`, `floorN`, `floorM`,
    `floorX`, `ceil_itv`, `gt_pred_ceil`, `le_ceil`, `ceil_def`,
    `ceil_le_int`, `ceil_le`, `intrKceil`, `intrEceil`, `ceilK`,
    `ceil0`, `ceil1`, `ceilD`, `ceilN`, `ceilM`, `ceilX`,
    `ceil_floor`, `rpred_int_num`, `int_num0`, `int_num1`,
    `int_num_subring`, `intr_nat`, `Rreal_int`, `intr_normK`,
    `intrEsign`, `natr_norm_int`, `natrEint`, `intrEge0`,
    `natr_exp_even`, `norm_intr_ge1`, `sqr_intr_ge1`, `intr_ler_sqr`,
    `floorpK`, `floorpP`, `trunc_floor`, `raddfZ_nat`, `rpredZ_nat`,
    `raddfZ_int`, `rpredZ_int`, `aut_natr`, `aut_intr`, `natr_aut_nu`,
    `intr_aut_nu`, `conj_natr`, `conj_intr`
  + lemmas `archi_boundP`, `upper_nthrootP` (moved from `ssrnum.v`)
  + lemmas `Znat_def`, `ZnatP` (moved from `ssrint.v`)
  + instances of `SemiringClosed` for `Num.nat` and `Num.int`

- in `rat.v`
  + lemmas `floor_rat`, `ceil_rat`

- in `ssrnum.v`
  + structures `archiNumDomainType`, `archiNumFieldType`,
    `archiCLosedFieldType`, `archiDomainType`, `archiFieldType`,
    `archiRcfType`
  + factory `NumDomain_bounded_isArchimedean` (renamed from
    `RealDomain_isArchimedean`)
  + lemmas `truncP`, `trunc_itv`

- in `algC.v`
  + lemma `Implementation.archimedean`
  + instance of `archiClosedFieldType` on `Implementation.type`
- in `order.v`
  + factory `SubPOrder_isSubOrder`
  + notations `[SubPOrder_isSubOrder of U by <: with disp]` and
    `[SubPOrder_isSubOrder of U by <:]`

### Changed

### Renamed

- in `algC.v`
  + `Cint` -> `Num.int`
  + `Cnat` -> `Num.nat`
  + `floorC` -> `Num.floor`
  + `truncC` -> `Num.trunc`
  + `Creal0` -> `real0`
  + `Creal1` -> `real1`
  + `floorC_itv` -> `floor_itv`
  + `floorC_def` -> `floor_def`
  + `intCK` -> `intrKfloor`
  + `floorCK` -> `floorK`
  + `floorC0` -> `floor0`
  + `floorC1` -> `floor1`
  + `floorCpK` -> `floorpK`
  + `floorCpD` -> `floorpP`
  + `Cint_int` -> `intr_int`
  + `CintP` -> `intrP`
  + `floorCD` -> `floorD`
  + `floorCN` -> `floorN`
  + `floorCM` -> `floorM`
  + `floorCX` -> `floorX`
  + `rpred_Cint` -> `rpred_int_num`
  + `Cint0` -> `int_num0`
  + `Cint1` -> `int_num1`
  + `Creal_Cint` -> `Rreal_int`
  + `conj_Cint` -> `conj_intr`
  + `Cint_normK` -> `intr_normK`
  + `CintEsign` -> `intrEsign`
  + `truncC_itv` -> `trunc_itv`
  + `truncC_def` -> `trunc_def`
  + `natCK` -> `natRK`
  + `CnatP` -> `natrP`
  + `truncCK` -> `truncK`
  + `truncC_gt0` -> `trunc_gt0`
  + `truncC0Pn` -> `trunc0Pn`
  + `truncC0` -> `trunc0`
  + `truncC1` -> `trunc1`
  + `truncCD` -> `truncD`
  + `truncCM` -> `truncM`
  + `truncCX` -> `truncX`
  + `rpred_Cnat` -> `rpred_nat_num`
  + `Cnat_nat` -> `natr_nat`
  + `Cnat0` -> `nat_num0`
  + `Cnat1` -> `nat_num1`
  + `Cnat_ge0` -> `natr_ge0`
  + `Cnat_gt0` -> `natr_gt0`
  + `conj_Cnat` -> `conj_natr`
  + `norm_Cnat` -> `norm_natr`
  + `Creal_Cnat` -> `Rreal_nat`
  + `Cnat_sum_eq1` -> `natr_sum_eq1`
  + `Cnat_mul_eq1` -> `natr_mul_eq1`
  + `Cnat_prod_eq1` -> `natr_prod_eq1`
  + `Cint_Cnat` -> `intr_nat`
  + `CintE` -> `intrE`
  + `Cnat_norm_Cint` -> `natr_norm_int`
  + `CnatEint` -> `natrEint`
  + `CintEge0` -> `intrEge0`
  + `Cnat_exp_even` -> `natr_exp_even`
  + `norm_Cint_ge1` -> `norm_intr_ge1`
  + `sqr_Cint_ge1` -> `sqr_intr_ge1`
  + `Cint_ler_sqr` -> `intr_ler_sqr`
  + `aut_Cnat` -> `aut_natr`
  + `aut_Cint` -> `aut_intr`
  + `Cnat_aut` -> `natr_aut`
  + `Cint_aut` -> `intr_aut`
  + `raddfZ_Cnat` -> `raddfZ_nat`
  + `raddfZ_Cint` -> `raddfZ_int`
  + `rpredZ_Cnat` -> `rpredZnat`
  + `rpredZ_Cint` -> `rpredZint`

### Removed

- in `ssrint.v`
  + definition `Znat_pred`
  + lemma `Znat_semiring_closed`

- in `rat.v`
  + definition `Qint_pred`, `Qnat_pred`
  + lemmas `rat_archimedean`, `Qint_subring_closed`,
    `Qnat_semiring_closed`

- in `algC.v`
  + lemma `floorC_subproof`, `Cnat_semiring`

### Deprecated

- in `ssrint.v`
  + definition `Znat` (require `archimedean.v` and use `Num.nat`)
  + lemmas `Znat_def`, `ZnatP` (moved to `archimedean.v`)
  + lemma `polyC_mulrz` (use `polyCMz`)

- in `rat.v`
  + definitions `Qint` and `Qnat` (require `archimedean.v` and use
    `Num.int` and `Num.nat`)
  + lemma `QintP` (require `archimedean.v` and use `intrP`)
  + lemma `Qnat_def` (require `archimedean.v` and use `natrEint`)
  + lemma `QnatP` (require `archimedean.v` and use `natrP`)

- in `ssrnum.v`
  + structure `archiFieldType` (renamed `archiFieldType` and moved to
    `archimedean.v`)
  + structures `archiNumDomainType`, `archiNumFieldType`,
    `archiCLosedFieldType`, `archiDomainType`, `archiFieldType`,
    `archiRcfType` (moved to `archimedean.v`)
  + factory `RealField_isArchimedean` renamed
    `NumDomain_bounded_isArchimedean` and moved to `archimedean.v`
  + factory `NumDomain_bounded_isArchimedean` (moved to `archimedean.v`)
  + notations `Num.Def.trunc`, `Num.trunc`, `Num.Def.nat_num`, `Num.nat`,
    `Num.Def.int_num`, `Num.int`, `Num.bound` (moved to `archimedean.v`)
  + lemmas `archi_boundP`, `upper_nthrootP`, `truncP`, `trunc_itv`
    (moved to `archimedean.v`)

### Infrastructure

### Misc

