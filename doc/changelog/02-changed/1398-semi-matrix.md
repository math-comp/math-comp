- in `matrix.v`
  + definition `mxdiag` generalized to `nmodType`
  + definitions `lin1_mx`, `lin_mx`, `mulmxr`, `lin_mulmxr` generalized to
    `pzSemiRingType`
  + definitions `lin_mulmx`, `lin_mul_row` generalized to `comPzSemiRingType`
  + `lSemiModType` instance on matrices generalized to `pzSemiRingType`
  + `lSemiAlgType` instance on square matrices generalized to `nzSemiRingType`
  + `pzSemiRingType` and `pzRingType` instance on square matrices generalized to
    arbitrary size
  + `semiAlgType` instance on square matrices generalized to `comNzSemiRingType`
  + semilinear function instances on `mulmxr`, `lin_mulmxr`, `mxtrace`, `trmx`,
    `row`, `col`, `row'`, `col'`, `mxsub`, `row_perm`, `col_perm`, `xrow`,
    `xcol`, `lsubmx`, `rsubmx`, `usubmx`, `dsubmx`, `vec_mx`, `mxvec`, `diag_mx`
    generalized to `pzSemiRingType`
  + semilinear function instances on `mulmx`, `lin_mulmx`, `lin_mul_row`
    generalized to `comPzSemiRingType`
  + lemmas `mxrowD`, `mxrow0`, `mxrow_const`, `mxrow_sum`, `submxrowD`,
    `submxrow0`, `submxrow_sum`, `mxcolD`, `mxcol0`, `mxcol_const`, `mxcol_sum`,
    `submxcolD`, `submxcol0`, `submxcol_sum`, `mxblockD`, `mxblock0`,
    `mxblock_const`, `mxblock_sum`, `submxblockD`, `submxblock0`,
    `submxblock_sum`, `is_trig_mxblockP`, `is_trig_mxblock`, `is_diag_mxblockP`,
    `is_diag_mxblock`, `submxblock_diag`, `eq_mxdiagP`, `eq_mxdiag`, `mxdiagD`,
    `mxdiag_sum`, `tr_mxdiag`, `row_mxdiag`, `col_mxdiag` generalized to
    `nmodType`
  + lemmas `scalemx_const`, `matrix_sum_delta`, `scalemxAl`, `mxtraceZ`,
    `row_sum_delta`, `scale_row_mx`, `scale_col_mx`, `scale_block_mx`,
    `diag_mx_sum_delta`, `row_diag_mx`, `scale_scalar_mx`, `scalemx1`,
    `scalar_mx_sum_delta`, `mx1_sum_delta`, `mulmx_sum_row`, `mul_scalar_mx`,
    `mul_rV_lin1`, `mul_rV_lin`, `mul_vec_lin`, `mx_rV_lin`, `mx_vec_lin`,
    `map_mxZ`, `map_lin1_mx`, `map_lin_mx`, `mxOver_scalar`, `mxOver_scalarE`,
    `mxOverZ`, `mxOver_diag`, `mxOver_diagE`, `mxOverM`, `mul_mxrow`,
    `mul_submxrow`, `mxcol_mul`, `submxcol_mul`, `mul_mxrow_mxcol`,
    `mul_mxcol_mxrow`, `mul_mxrow_mxblock`, `mul_mxblock_mxrow`, `mul_mxblock`,
    `mxtrace_mxblock`, `mxdiagZ`, `diag_mxrow`, `mxtrace_mxdiag`,
    `mul_mxdiag_mxcol`, `mul_mxrow_mxdiag`, `mul_mxblock_mxdiag`,
    `mul_mxdiag_mxblock` generalized to `pzSemiRingType`
  + lemmas `scalemxAr`, `mul_vec_lin_row`, `mxvec_dotmul`, `mul_mx_scalar`
    generalized to `comPzSemiRingType`
    ([#1398](https://github.com/math-comp/math-comp/pull/1398)).
