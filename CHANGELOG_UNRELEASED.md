# Changelog (unreleased)

To avoid having old PRs put changes into the wrong section of the CHANGELOG,
new entries now go to the present file as discussed
[here](https://github.com/math-comp/math-comp/wiki/Agenda-of-the-April-23rd-2019-meeting-9h30-to-12h30#avoiding-issues-with-changelog).

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

### Added

- in `seq.v`
  + lemma `foldl_foldr`
  + lemmas `find_pred0`, `find_predT`

- in `bigop.v`
  + lemma `big_if`

- in `seq.v`
  + lemmas `sumn_ncons`, `sumn_set_nth`, `sumn_set_nth_ltn`,
    `sumn_set_nth0`

- in `finset.v`
  + lemmas `bigA_distr`, `subset_cons`, `subset_cons2`, `subset_catl`,
    `subset_catr`, `subset_cat2`, `filter_subset`, `subset_filter`,
    `map_subset`.

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

- in `seq.v`
  + lemma `rem_mem`

- in `cyclic.v`
  + added lemma `units_Zp_cyclic`
- in `finalg.v`
  + lemmas `card_finRing_gt1`, `card_finField_unit` 

- in `poly.v`
  + lemmas `polyC_natr`, `char_poly`

- in `polydiv.v`
  + lemmas `rmodp_id`, `rmodpN`, `rmodpB`, `rmodpZ`, `rmodp_sum`,
    `rmodp_mulml`, `rmodpX`, `rmodp_compr`

- in `qpoly.v`
  + new file of `algebra` that defines the algebras `R[X]/<p>` and their theory.
  + definitions `{poly_n R}`, `'nX^m`, `x.-lagrange`, `x.lagrange_n`,
    `{poly %/ p }`, `'qX`, `irreducibleb`, `mk_monic, in_qpoly`
  + lemmas `size_npoly`, `npolyP`, `coef_npolyp` `big_coef_npoly`,
  `npolypK`, `coefn_sum` `npoly_enum_uniq`, `mem_npoly_enum`, 
  `card_npoly` `irreducibleP`, `dim_polyn` , `npolyXE`, `nth_npolyX`,
  `npolyX_free`, `npolyX_full`, `npolyX_coords`, `coord npolyX`,
  `npolyX_gen`, `lagrangeE`, `nth_lagrange`, `size_lagrange_`, `size_lagrange`,
  `lagrange_sample`, `lagrange_free`, `lagrange_full`, `lagrange_coords`,
  `lagrange_gen`, `monic_mk_monic`, `size_mk_monic_gt1`, `size_mk_monic_gt0`,
  `mk_monic_neq0`, `size_mk_monic`, `poly_of_size_mod`, `in_qpoly0`, 
  `in_qpolyD`, `in_qpolyZ`, `card_monic_qpoly`, `in_qpoly1`, `in_qpolyM`, 
  `in_qpoly_small`, `qpolyC_proof`, `qpolyCE`, `qpolyC0`, 
  `qpoly_mul1z`, `qpoly_mulz1`, `qpoly_nontrivial`, `qpolyXE`, `mk_monic_X`, 
  `mk_monic_Xn`, `card_qpoly`, `qpoly_mulC`, `qpoly_mulA`, `qpoly_mul_addr`, 
  `qpoly_mul_addl`, `poly_of_qpoly_sum`, `poly_of_qpolyD`, `qpolyC_natr`, 
  `char_qpoly`, `poly_of_qpolyM`, `poly_of_qpolyX`, `qpolyCN`, 
  `qpolyC`, `qpolyCD`, `qpolyCM`, `qpolyC_is_rmorphism`, 
  `poly_of_qpolyZ`, `qpoly_mulVz`, `qpoly_mulzV`, `qpoly_intro_unit`,
  `qpoly_inv_out`, `irreducible_poly_coprime`
   
in `qfpoly.v`
  + new file of `field` that extends the algebras R[X]/<p> defined in `qpoly`
    with the field when p is irreducible
  + definitions `monic_irreducible_poly`, `{poly' %/ p with mi}`, 
    `primitive_poly`, `qlogp`, `plogp`
  + lemmas `mk_monicE`,  `coprimep_unit`, `qpoly_mulVp`, `qpoly_inv0`,
  `qpoly_inv`, `in_qpoly_comp_horner`, `map_poly_div_inj`, 
  `map_fpoly_div_inj`, `card_qfpoly`, `card_qfpoly_gt1`, `primitive_polyP`, 
  `primitive_poly_in_qpoly_eq0`, `card_primitive_qpoly`, 
  `primitive_mi`, `qX_neq0` `qX_in_unit`, `dvdp_order`, `gX_order`, `gX_all`, 
  `qlogp_lt`, `qlogp_qX`, `qX_order_card`, `qX_order_dvd`, `qlogp0`, `qlogp1`, 
  `qlogp_eq0`, `qlogpD`, 
  `qX_exp_neq0`, `qX_exp_inj`, `powX_eq_mod`, `qX_expK`, `plogp_lt`, 
  `plogp_X`, `plogp0`, `plogp1`, `plogp_div_eq0`, `plogpD`
   
- in `bigop.v`
  + lemma `big_condT`

- in `fintype.v`
  + definitions `ordS`, `ord_pred`
  + lemmas `ordS_subproof`, `ord_pred_subproof`, `ordSK`, `ord_predK`,
  `ordS_bij`, `ordS_inj`, `ord_pred_bij`, `ord_pred_inj`

- in `zmodp.v`
  + lemmas `add_1_Zp`, `add_Zp_1`, `sub_Zp_1` and `add_N1_Zp`.

- in `bigop.v`
  + lemmas `sum_nat_seq_eq0`, `sum_nat_seq_neq0`, `sum_nat_seq_eq1`,
    `sum_nat_eq1`, `prod_nat_seq_eq0`, `prod_nat_seq_neq0`,
    `prod_nat_seq_eq1`, `prod_nat_seq_neq1`

- in `ssrnat.v`
  + lemma `addn_eq1`

### Changed

### Renamed

- in `polydiv.v`
  + `modp_mod` -> `modp_id`

### Removed

### Deprecated

### Infrastructure

### Misc

