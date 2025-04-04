- in `matrix.v`
  + Definitions `mulmx`, `perm_mx`, `tperm_mx`, `is_perm_mx`, `pid_mx`,
    `lift0_perm`, `lift0_mx`, `comm_mx`, `comm_mxb` generalized to
    `pzSemiRingType`
  + Definitions `copid_mx`, `lin1_mx`, `lin_mx`, `mulmxr`, `lin_mulmxr`,
    `mxtrace`, `determinant`, `cofactor`, `adjugate`, `Vandermonde` generalized
    to `pzRingType`
  + Definition `lin_mul_row` generalized to `comPzRingType`
  + The `pzSemiRingType` and `pzRingType` instances on square matrices
    generalized to the case where the size is potentially zero
  + The `lmodType` instance on matrices generalized to `pzRingType`
  + The ring morphism instances on `scalar_mx` and `map_mx` generalized to
    `pzSemiRingType` and the case where the size is potentially zero
  + The linear function instances on `swizzle_mx`, `trmx`, `row`, `col`, `row'`,
    `col'`, `mxsub`, `row_perm`, `col_perm`, `xrow`, `xcol`, `lsubmx`, `rsubmx`,
    `usubmx`, `dsubmx`, `vec_mx`, `mxvec`, `diag_mx`, `mxtrace` generalized to
    `pzRingType`
  + The additive function instances on `mulmx`, `mulmxr`, `lin_mulmxr`
    generalized to `pzRingType`
  + The linear function instances on `mulmx`, `lin_mulmx`, `lin_mul_row`
    generalized to `comPzRingType`
  + The `semiringClosed` instance on `mxOver` generalized to `pzRingType`
  + Lemmas `trmx_delta`, `delta_mx_lshift`, `delta_mx_rshift`,
    `delta_mx_ushift`, `delta_mx_dshift`, `vec_mx_delta`, `mxvec_delta`,
    `trmx1`, `row1`, `col1`, `mulmxA`, `mul0mx`, `mulmx0`, `mulmxDl`, `mulmxDr`,
    `mulmx_suml`, `mulmx_sumr`, `rowE`, `colE`, `mul_rVP`, `row_mul`,
    `mxsub_mul`, `mul_rowsub_mx`, `mulmx_colsub`, `mul_delta_mx_cond`,
    `mul_delta_mx`, `mul_delta_mx_0`, `mul_diag_mx`, `mul_mx_diag`,
    `mulmx_diag`, `scalar_mxM`, `mul1mx`, `mulmx1`, `rowsubE`, `mul_col_perm`,
    `mul_row_perm`, `mul_xcol`, `col_permE`, `row_permE`, `xcolE`, `xrowE`,
    `perm_mxEsub`, `tperm_mxEsub`, `tr_perm_mx`, `tr_tperm_mx`, `perm_mx1`,
    `perm_mxM`, `is_perm_mxP`, `perm_mx_is_perm`, `is_perm_mx1`, `is_perm_mxMl`,
    `is_perm_mx_tr`, `is_perm_mxMr`, `pid_mx_0`, `pid_mx_1`, `pid_mx_row`,
    `pid_mx_col`, `pid_mx_block`, `tr_pid_mx`, `pid_mx_minv`, `pid_mx_minh`,
    `mul_pid_mx`, `pid_mx_id`, `pid_mxErow`, `pid_mxEcol`, `mul_mx_row`,
    `mul_col_mx`, `mul_row_col`, `mul_col_row`, `mul_row_block`,
    `mul_block_col`, `mulmx_block`, `mulmx_lsub`, `mulmx_rsub`, `mul_usub_mx`,
    `mul_dsub_mx`, `mxtrace1`, `mulmxE`, `idmxE`, `lift0_perm0`,
    `lift0_perm_lift`, `lift0_permK`, `lift0_perm_eq0`, `lift0_mx_perm`,
    `lift0_mx_is_perm`, `exp_block_diag_mx`, `trmx_mul_rev`, `map_mxM`,
    `map_delta_mx`, `map_diag_mx`, `map_scalar_mx`, `map_mx1`, `map_perm_mx`,
    `map_tperm_mx`, `map_pid_mx`, `trace_map_mx`, `comm_mx_sym`, `comm_mx_refl`,
    `comm_mx0`, `comm0mx`, `comm_mx1`, `comm1mx`, `comm_mxD`, `comm_mxM`,
    `comm_mx_sum`, `comm_mxP`, `all_comm_mxP`, `all_comm_mx1`, `all_comm_mx2P`,
    `all_comm_mx_cons`, `comm_mxE` generalized to `pzSemiRingType`
  + Lemmas `trmx_mul`, `diag_mxC`, `diag_mx_comm`, `scalar_mxC`,
    `comm_mx_scalar`, `comm_scalar_mx`, `mxtrace_mulC` generalized to
    `comPzSemiRingType`
  + Lemams `scalemx_const`, `matrix_sum_delta`, `row_sum_delta`, `scale_row_mx`,
    `scale_col_mx`, `scale_block_mx`, `diag_mx_sum_delta`, `row_diag_mx`,
    `scale_scalar_mx`, `scalemx1`, `scalar_mx_sum_delta`, `mx1_sum_delta`,
    `mulmxN`, `mulNmx`, `mulmxBl`, `mulmxBr`, `scalemxAl`, `mulmx_sum_row`,
    `mul_scalar_mx`, `mul_copid_mx_pid`, `mul_pid_mx_copid`, `copid_mx_id`,
    `mul_rV_lin1`, `mul_rV_lin`, `mul_vec_lin`, `mx_rV_lin`, `mx_vec_lin`,
    `mxtraceZ`, `map_mxZ`, `det_map_mx`, `cofactor_map_mx`, `map_mx_adj`,
    `map_copid_mx`, `map_lin1_mx`, `map_lin_mx`, `comm_mxN`, `comm_mxN1`,
    `comm_mxB`, `mul_mxrow`, `mul_submxrow`, `mxcol_mul`, `submxcol_mul`,
    `mul_mxrow_mxcol`, `mul_mxcol_mxrow`, `mul_mxrow_mxblock`,
    `mul_mxblock_mxrow`, `mul_mxblock`, `mxtrace_mxblock`, `mxdiagZ`,
    `diag_mxrow`, `mxtrace_mxdiag`, `mul_mxdiag_mxcol`, `mul_mxrow_mxdiag`,
    `mul_mxblock_mxdiag`, `mul_mxdiag_mxblock` generalized to `pzRingType`
  + Lemmas `scalemxAr`, `mul_vec_lin_row`, `mxvec_dotmul`, `mul_mx_scalar`,
    `determinant_multilinear`, `determinant_alternate`, `det_tr`, `det_perm`,
    `det1`, `det_mx00`, `detZ`, `det0`, `det_scalar`, `det_scalar1`, `det_mx11`,
    `det_mulmx`, `detM`, `expand_cofactor`, `expand_det_row`, `cofactor_tr`,
    `cofactorZ`, `expand_det_col`, `trmx_adj`, `adjZ`, `mul_mx_adj`,
    `mul_adj_mx`, `adj1`, `mulmx1C`, `det_ublock`, `det_lblock`, `det_trig`,
    `det_diag`, `mxOver_scalar`, `mxOver_scalarE`, `mxOverZ`, `mxOver_diag`,
    `mxOver_diagE`, `mxOverM`, `det_Vandermonde` generalized to `comPzRingType`
    ([#1385](https://github.com/math-comp/math-comp/pull/1385),
    by Kazuhiko Sakaguchi).
