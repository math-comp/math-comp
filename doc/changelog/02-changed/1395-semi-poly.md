- in `poly.v`
  + Definitions `polyX`, `horner_rec`, `horner`, `horner_eval`, `comm_coef`,
    `comm_poly`, `polyOver_pred`, `polyOver`, `deriv`, `derivn`, `nderivn`,
    `monic`, `root`, `map_poly`, `commr_rmorph`, `horner_morph`, `comp_poly`,
    `even_poly`, `odd_poly`, `take_poly`, `drop_poly` generalized to
    `nzSemiRingType`
  + Definition `horner_alg` generalized to `semiAlgType`
  + The implicit arguments of `deriv` and `derivn` are now maximally inserted.
  + `lSemiModType` and `lSemiAlgType` instances on polynomials generalized to
    `nzSemiRingType`
  + `comNzSemiRingType` and `comSemiAlgType` instance on polynomials generalized
    to `comNzSemiRingType`
  + Polynomials now inherit the `countNzSemiRingType` and
    `countComNzSemiRingType` structures of the type of coefficients.
  + N-module morphism instances on `coefp`, `polyC`, `map_poly`, `horner_morph`,
    `comp_poly`, `even_poly`, `odd_poly`, `take_poly`, `drop_poly` generalized
    to `nzSemiRingType`
  + Semiring morphism instances on `coefp 0`, `polyC`, `map_poly`, `horner_morph`
    generalized to `nzSemiRingType`
  + Semilinear function instances on `coefp`, `horner_eval`, `deriv`, `derivn`,
    `nderivn`, `horner_morph`, `comp_poly`, `even_poly`, `odd_poly`,
    `take_poly`, `drop_poly` generalized to `nzSemiRingType`
  + Semialgebra morphism instances on `horner_morph` and `comp_poly` generalized
    to `comNzSemiRingType`
  + Semiring and semialgebra morphism instances on `horner_eval` generalized to
    `comNzSemiRingType`
  + Semialgebra morphism instance on `horner_alg` generalized to `semiAlgType`
  + `addrClosed`, `mulr2Closed`, `mulrClosed`, `semiring2Closed`,
    `semiringClosed` instances on `polyOver` generalized to `nzSemiRingType`
  + `mulrClosed` instance on `monic` generalized to `nzSemiRingType`
  + Lemmas `coefMn`, `coef_sum`, `polyCMn`, `polyC_exp`, `polyC_natr`,
    `pchar_poly`, `mul_polyC`, `scale_polyC`, `alg_polyC`, `coefZ`,
    `size_scale_leq`, `polyseqX`, `size_polyX`, `polyX_eq0`, `coefX`,
    `lead_coefX`, `commr_polyX`, `coefMX`, `coefXM`, `cons_poly_def`,
    `poly_ind`, `polyseqXaddC`, `size_XaddC`, `lead_coefXaddC`, `size_MXaddC`,
    `polyseqMX`, `size_mulX`, `lead_coefMX`, `size_XmulC`, `coefXn`,
    `polyseqXn`, `size_polyXn`, `commr_polyXn`, `lead_coefXn`,
    `lead_coefXnaddC`, `size_XnaddC`, `polyseqMXn`, `coefMXn`, `size_mulXn`,
    `coefXnM`, `coef_sumMXn`, `poly_def`, `eq_poly`, `horner0`, `hornerC`,
    `hornerX`, `horner_cons`, `horner_coef0`, `hornerMXaddC`, `hornerMX`,
    `horner_Poly`, `horner_coef`, `horner_coef_wide`, `horner_poly`, `hornerD`,
    `horner_sum`, `hornerCM`, `hornerZ`, `hornerMn`, `comm_coef_poly`,
    `comm_poly0`, `comm_poly1`, `comm_polyX`, `comm_polyD`, `commr_horner`,
    `hornerM_comm`, `comm_polyM`, `horner_exp_comm`, `comm_poly_exp`,
    `hornerXn`, `polyOverS`, `polyOver0`, `polyOver_poly`, `polyOverP`,
    `polyOverC`, `polyOverZ`, `polyOverX`, `polyOverXn`, `rpred_horner`,
    `coef_deriv`, `polyOver_deriv`, `derivC`, `derivX`, `derivXn`, `deriv0`,
    `derivD`, `derivMn`, `derivZ`, `deriv_mulC`, `derivMXaddC`, `derivM`,
    `derivn0`, `derivn1`, `derivnS`, `derivSn`, `coef_derivn`,
    `polyOver_derivn`, `derivnC`, `derivnD`, `derivnMn`, `derivnZ`, `derivnXn`,
    `derivnMXaddC`, `derivn_poly0`, `lt_size_deriv`, `coef_nderivn`,
    `nderivn_def`, `polyOver_nderivn`, `nderivn0`, `nderivn1`, `nderivnC`,
    `nderivnXn`, `nderivnD`, `nderivnMn`, `nderivnZ`, `nderivnMXaddC`,
    `nderivn_poly0`, `nderiv_taylor`, `nderiv_taylor_wide`, `monicE`, `monicP`,
    `monic1`, `monicX`, `monicXn`, `monic_neq0`, `lead_coef_monicM`,
    `lead_coef_Mmonic`, `size_monicM`, `size_Mmonic`, `monicMl`, `monicMr`,
    `monic_exp`, `monic_prod`, `monicXaddC`, `monicXnaddC`, `lreg_lead0`,
    `rreg_lead0`, `lreg_size`, `lreg_polyZ_eq0`, `lead_coef_lreg`, `rreg_size`,
    `rreg_polyMC_eq0`, `rreg_div0`, `monic_comreg`, `mem_root`, `rootE`,
    `rootP`, `rootPt`, `rootPf`, `rootC`, `root0`, `root1`, `rootX`,
    `root_size_gt1`, `map_polyE`, `map_poly0`, `eq_map_poly`, `map_poly_id`,
    `coef_map_id0`, `map_Poly_id0`, `map_poly_comp_id0`, `size_map_poly_id0`,
    `map_poly_eq0_id0`, `lead_coef_map_id0`, `size_map_inj_poly`,
    `map_inj_poly`, `lead_coef_map_inj`, `map_polyK`, `eq_in_map_poly_id0`,
    `eq_in_map_poly`, `coef_map`, `map_Poly`, `map_poly_comp`, `map_polyC`,
    `lead_coef_map_eq`, `map_polyZ`, `map_polyX`, `map_polyXn`, `map_polyXaddC`,
    `monic_map`, `horner_map`, `map_comm_poly`, `map_comm_coef`, `rmorph_root`,
    `horner_morphC`, `horner_morphX`, `deriv_map`, `derivn_map`, `nderivn_map`,
    `poly_morphX_comm`, `poly_initial`, `size_map_polyC`, `map_polyC_eq0`,
    `root_polyC`, `comp_polyE`, `coef_comp_poly`, `polyOver_comp`,
    `comp_polyCr`, `comp_poly0r`, `comp_polyC`, `comp_poly0`, `comp_polyD`,
    `comp_polyZ`, `comp_polyXr`, `comp_polyX`, `comp_poly_MXaddC`,
    `size_comp_poly_leq`, `comp_Xn_poly`, `coef_comp_poly_Xn`, `comp_poly_Xn`,
    `size_even_poly`, `coef_even_poly`, `even_polyE`, `size_even_poly_eq`,
    `even_polyD`, `even_polyZ`, `even_polyC`, `size_odd_poly`, `coef_odd_poly`,
    `odd_polyE`, `odd_polyC`, `odd_polyD`, `odd_polyZ`, `size_odd_poly_eq`,
    `odd_polyMX`, `even_polyMX`, `sum_even_poly`, `sum_odd_poly`,
    `poly_even_odd`, `size_take_poly`, `coef_take_poly`, `take_poly_id`,
    `take_polyD`, `take_polyZ`, `take_poly_sum`, `take_poly0l`, `take_poly0r`,
    `take_polyMXn`, `take_polyMXn_0`, `take_polyDMXn`, `coef_drop_poly`,
    `drop_poly_eq0`, `size_drop_poly`, `sum_drop_poly`, `drop_polyD`,
    `drop_polyZ`, `drop_poly_sum`, `drop_poly0l`, `drop_poly0r`, `drop_polyMXn`,
    `drop_polyMXn_id`, `drop_polyDMXn`, `poly_take_drop`, `eqp_take_drop`
    generalized to `nzSemiRingType`
  + Lemmas `hornerM`, `horner_exp`, `horner_prod`, `comp_polyM`, `comp_polyA`,
    `horner_comp`, `root_comp`, `deriv_comp`, `deriv_exp`
    generalized to `comNzSemiRingType`
  + Lemmas `in_alg_comm`, `horner_algC`, `horner_algX`, `poly_alg_initial`
    generalized to `semiAlgType`
    ([#1395](https://github.com/math-comp/math-comp/pull/1395)).
