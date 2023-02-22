# Changelog (unreleased)

To avoid having old PRs put changes into the wrong section of the CHANGELOG,
new entries now go to the present file as discussed
[here](https://github.com/math-comp/math-comp/wiki/Agenda-of-the-April-23rd-2019-meeting-9h30-to-12h30#avoiding-issues-with-changelog).

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

### Added

- in `ssrint.v`
  + lemmas `intrN`, `intrB`

- in `ssrnum.v`
  + lemma `invf_pgt`, `invf_pge`, `invf_ngt`, `invf_nge`
  + lemma `invf_plt`, `invf_ple`, `invf_nlt`, `invf_nle`
- in `bigop.v`
  + lemma `big_ord1`, `big_ord1_cond`, `big_rcons_op`, `big_change_idx`,
    `big_rcons`, `big_only1`

- in `eqtype.v`
  + definition `dfwith`
  + lemmas `dfwith_in`, `dfwith_out`, `dfwithP`

- in `finset.v`
  + definition `setXn`
  + lemmas `in_setXn`, `setXnP`, `cardsXn`, `setXnS`, `eq_setXn`

- in `prime.v`
  + lemmas `primeNsig`, `all_prime_primes`, `primes_eq0`, `totient_gt1`

- in `tuple.v`
  + lemmas `tnth_lshift`, `tnth_rshift`

- in `path.v`
  + lemma `count_sort`
- in `poly.v`
  + lemmas `coef0M`, `coef0_prod`, `polyseqXaddC`, `lead_coefXaddC`,
    `lead_coefXnaddC`, `lead_coefXnsubC`, `size_XnaddC`, `size_XnsubC`,
	 `monicXaddC`, `lead_coef_prod_XsubC`, `monicXnaddC`, `monicXnsubC`,
	 `prim_root_eq0`, `polyOverXn`, `polyOverXaddC`, `polyOverXnaddC`,
	 `polyOverXnsubC`, `prim_root_charF`, `char_prim_root`, `prim_root_pi_eq0`,
	 `prim_root_dvd_eq0`, `prim_root_natf_neq0`, `eq_in_map_poly_id0`,
	 `eq_in_map_poly`, `map_polyXaddC`, `map_polyXsubC`, `map_prod_XsubC`,
	 `prod_map_poly`, `mapf_root`, `lead_coef_prod`

- in `ssralg.v`
  + lemmas `prodM_comm`, `prodMl_comm`, `prodMr_comm`, `prodrMl`, `prodrMr`


### Changed

- in `bigop.v`
  + weaken hypothesis of lemma `telescope_sumn_in`

- in `zmodp.v`
  + simpler statement of `Fp_Zcast`

- in `path.v`
  + generalized `count_merge` from `eqType` to `Type`
  + lemmas `coef_prod_XsubC`, `coefPn_prod_XsubC`, `coef0_prod_XsubC`
- in `ssralg.v`
  + lemmas `natr1`, `nat1r`, `telescope_sumr_eq`, `telescope_prodr_eq`, `telescope_prodf_eq`
  + new lemmas `prodrM_comm`, `prodrMl_comm`, `prodrMr_comm`,
    `prodrM`, `prodrMl`, and `prodrMr`.

- in `poly.v`
  + definitions `even_poly`, `odd_poly`, `take_poly`, `drop_poly`
  + lemmas `comm_polyD`, `comm_polyM`, `comm_poly_exp`, `root_exp`,
    `root_ZXsubC`, `size_mulXn`, `coef_sumMXn`, `comp_Xn_poly`,
    `coef_comp_poly_Xn`, `comp_poly_Xn`, `size_even_poly`,
    `size_even_poly_eq`, `coef_even_poly`, `even_polyE`, `even_polyD`,
    `even_polyZ`, `even_poly_is_linear`, `even_polyC`,
    `size_odd_poly`, `coef_odd_poly`, `odd_polyE`, `odd_polyC`,
    `odd_polyD`, `odd_polyZ`, `odd_poly_is_linear`, `odd_polyMX`,
    `even_polyMX`, `sum_even_poly`, `sum_odd_poly`, `poly_even_odd`,
    `size_take_poly`, `coef_take_poly`, `take_poly_id`, `take_polyD`,
    `take_polyZ`, `take_poly_is_linear`, `take_poly_sum`,
    `take_poly0l`, `take_poly0r`, `take_polyMXn`, `take_polyMXn_0`,
    `take_polyDMXn`, `size_drop_poly`, `size_drop_poly_eq`,
    `coef_drop_poly`, `drop_poly_eq0`, `sum_drop_poly`, `drop_polyD`,
    `drop_polyZ`, `drop_poly_is_linear`, `drop_poly_sum`,
    `drop_poly0l`, `drop_poly0r`, `drop_polyMXn`, `drop_polyMXn_id`,
    `drop_polyDMXn`, `poly_take_drop`, `eqp_take_drop`, `scale_polyC`
    `drop_polyDMXn`, `poly_take_drop`, `eqp_take_drop`
  + new lemmas `coef0M`, `coef0_prod`, `polyseqXaddC`,
    `lead_coefXaddC`, `lead_coef_XnaddC`, `lead_coef_XaddC`,
    `lead_coef_XnsubC`, `lead_coef_XsubC`, `size_XnaddC`,
    `size_XnsubC`, `monicXaddC`, `lead_coef_prod_XsubC`,
    `monicXnaddC`, `monicXnsubC`, `prim_root_eq0`, `polyOverXn`,
    `polyPverXnsubC`, `prim_root_charF`, `char_prim_root`,
    `prim_root_pi_eq0`, `prim_root_dvd_eq0`, `prim_root_natf_eq0`,
    `eq_in_map_poly_id0`, `eq_in_map_poly`, `map_polyXaddC`,
    `map_polyXsubC`, `map_prod_XsubC`, `prod_map_poly`, `mapf_root`,
    and `lead_coef_prod`.
  + canonical instances `even_poly_additive`, `even_poly_linear`,
    `odd_poly_additive`, `odd_poly_linear`, `take_poly_additive`,
    `take_poly_linear`, `drop_poly_additive`, `drop_poly_linear`

- in `polydiv.v`
  + lemmas `Pdiv.RingMonic.drop_poly_rdivp`,
    `Pdiv.RingMonic.take_poly_rmodp`,
    `Pdiv.IdomainMonic.drop_poly_divp`,
    `Pdiv.IdomainMonic.take_poly_modp`
  + new definition `mup`.
  + new lemmas `root_dvdp`, `eqpW`, `irredp_XaddC`, `dvdp_expXsubCP`,
    `horner_mod`, `mup_geq`, `mup_leq`, `mup_ltn`, `XsubC_dvd`,
    `mup_XsubCX`, `mupNroot`, `mupMl`, `mupM`, `mu_prod_XsubC`, and
    `prod_XsubC_eq`.

- in `bigop.v`
  + lemmas `big_ord1_eq`, `big_ord1_cond_eq`, `big_nat1_eq`,
    `big_nat1_cond_eq`

- in `eqtype.v`
  + lemmas `existsb` and `exists_inb`

- in `seq.v`
  + lemma `if_nth`

- in `ssrbool.v`
  + lemmas `if_and`, `if_or`, `if_implyb`, `if_impliybC`, `if_add`

- in `ssralg.v`
  + lemma `eqr_sum_div`

- in `ssrnum.v`
  + lemmas `psumr_neq0`, `psumr_neq0P`

- in `ssrnat.v`
  + lemma `leqVgt`
  + lemmas `ltn_half_double`, `leq_half_double`, `gtn_half_double`
  + lemma `double_pred`
  + lemmas `uphalfE`, `ltn_uphalf_double`, `geq_uphalf_double`, `gtn_uphalf_double`
  + lemmas `halfK`, `uphalfK`, `odd_halfK`, `even_halfK`, `odd_uphalfK`, `even_uphalfK`
  + lemmas `leq_sub2rE`, `leq_sub2lE`, `ltn_sub2rE`, `ltn_sub2lE`

- in `ssrint.v`
  + printing only notation for `x = y :> int`, opening `int_scope` on
    `x` and `y` to better match the already existing parsing only
    notation with the introduction of number notations in `ring_scope`

- in `bigop.v`
  + lemmas `big_seq1_id`, `big_nat1_id`, `big_pred1_eq_id`,
    `big_pred1_id`, `big_const_idem`, `big1_idem`, `big_id_idem`,
    `big_rem_AC`, `perm_big_AC`, `big_enum_cond_AC`, `bigD1_AC`,
    `bigD1_seq_AC`, `big_image_cond_AC`, `big_image_AC`,
    `big_image_cond_id_AC`, `Lemma`, `cardD1x`, `reindex_omap_AC`,
    `reindex_onto_AC`, `reindex_AC`, `reindex_inj_AC`, `bigD1_ord_AC`,
    `big_enum_val_cond_AC`, `big_enum_rank_cond_AC`, `big_nat_rev_AC`,
    `big_rev_mkord_AC`, `big_mkcond_idem`, `big_mkcondr_idem`,
    `big_mkcondl_idem`, `big_rmcond_idem`, `big_rmcond_in_idem`,
    `big_cat_idem`, `big_allpairs_dep_idem`, `big_allpairs_idem`,
    `big_cat_nat_idem`, `big_split_idem`, `big_id_idem_AC`,
    `bigID_idem`, `bigU_idem`, `partition_big_idem`,
    `sig_big_dep_idem`, `pair_big_dep_idem`, `pair_big_idem`,
    `pair_bigA_idem`, `exchange_big_dep_idem`, `exchange_big_idem`,
    `exchange_big_dep_nat_idem`, `exchange_big_nat_idem`,
    `big_undup_AC`
- in `matrix.v`
  + definitions `Vandrmonde`, `map2_mx`
  + lemma `det_Vandermonde`, `map2_trmx`, `map2_const_mx`, `map2_row`,
	 `map2_col`, `map2_row'`, `map2_col'`, `map2_mxsub`, `map2_row_perm`,
	 `map2_col_perm`, `map2_xrow`, `map2_xcol`, `map2_castmx`,
	 `map2_conform_mx`, `map2_mxvec`, `map2_vec_mx`, `map2_row_mx`,
	 `map2_col_mx`, `map2_block_mx`, `map2_lsubmx`, `map2_rsubmx`,
	 `map2_usubmx`, `map2_dsubmx`, `map2_ulsubmx`, `map2_ursubmx`,
	 `map2_dlsubmx`, `map2_drsubmx`, `eq_in_map2_mx`, `eq_map2_mx`,
	 `map2_mx_left_in`, `map2_mx_left`, `map2_mx_right_in`, `map2_mx_right`,
	 `map2_mxA`, `map2_1mx`, `map2_mx1`, `map2_mxC`, `map2_0mx`, `map2_mx0`,
	 `map2_mxDl`, `map2_mxDr`, `diag_mx_is_additive`, `mxtrace_is_additive`


- in `ssralg.v`
  + lemmas `divrN`, `divrNN`

- in file `intdiv.v`,
  + new lemmas `dvdz_charf`, and `eisenstein`.

- in file `vector.v`,
  + new lemmas `subset_limgP`, `lker0_img_cap`, and `SubvsE`.

- in file `falgebra.v`,
  + new lemmas `memv_mulP`, `big_prodv_seqP`, `adjoin_cat`, and
    `eq_adjoin`.

- in file `fieldext.v`,
  + new definition `vssub`.
  + new lemmas `aimg_cap`, `Fadjoin_seq_idP`, `vsproj_is_lrmorphism`,
    `vssub_is_lrmorphism`, `vsval_sub`, `prodv_idPl`, `prodv_idPr`,
    `big_prod_subfield_seqP`, `big_prod_subfieldP`, `prodv_Fadjoinl`,
    `prodv_Fadjoinr`, `dim_aimg`, `sub_aimgP`, `polyOver_aimgP`, and
    `mapf_polyOver`.

- in file `galois.v`,
  + new lemmas `splittingFieldFor_aimg`, and `splitting_ahom`.

- in file `separable.v`,
  + new lemma `separable_aimg`.

- in file `action.v`,
  + new lemmas `prime_atrans`, `prime_orbit`, and `prime_astab`.

- in file `fingroup.v`,
  + new lemma `prod_subG`.

- in file `gproduct.v`,
  + new definitions `extnprod_mulg`, `extnprod_invg`,
    `extnprod_groupMixin`, and `dfung1`.
  + new notation `gTn`.
  + new lemmas `extnprod_mul1g`, `extnprod_mulVg`, `extnprod_mulgA`,
    `oneg_ffun`, `mulg_ffun`, `invg_ffun`, `prodg_ffun`,
    `group_setXn`, `dfung1_id`, `dfung1_dflt`, `dfung1_morphM`,
    `dffunM`, `injm_dfung1`, `group_set_dfwith`, `group_dfwithE`,
    `morphim_dfung1`, `morphim_dffunXn`, `setXn_prod`, `setXn_dprod`,
    `isog_setXn`, `setXn_gen`, and `groupX0`.

- in file `perm.v`,
  + new lemmas `tpermJt`, and `gen_tperm`.

- in file `maximal.v`,
  + new lemmas `unsolvable_Alt`, and `unsolvable_SymF`.

- in file `nilpotent.v`,
  + new lemma `sol_setXn`.

- in file `bigop.v`,
  + new lemmas `big_rcons_op`, `big_change_idx`, `big_rcons`, and
    `big_only1`.

- in file `eqtype.v`,
  + new definition `dfwith`.
  + new lemmas `dfwithin`, `dfwithout`, and `dfwithP`.

- in file `finset.v`,
  + new definition `setXn`.
  + new lemmas `in_setXn`, `setXnP`, `cardsXn`, `setXnS`, and `eq_setXn`.

- in file `prime.v`,
  + new lemmas `primeNsig`, `prime_primes`, `primes_neq0`, and
    `totient_gt1`.

- in file `tuple.v`,
  + new lemmas `tnth_lshift`, and `tnth_rshift`.

### Changed

- in `order.v`
  + fix `\meet^p_` and `\join^p_` notations
  + fix the scope of `n.-tuplelexi` notations
- in `poly.v`:
  + generalize `eq_poly`

- in `poly.v`:
  + made hornerE preserve powers

- in `matrix.v`:
  + updated `oppmx`, `addmx`, `addmxA`, `addmxC`, `add0mx`
  + moved to an earlier section of the file `diag_mx`, 
    `tr_diag_mx`, `diag_mx_row`, `diag_mxP`, `diag_mx_is_diag`, 
    `diag_mx_is_trig`, `scalar_mx`, `diag_const_mx`, `tr_scalar_mx`, 
    `scalar_mx_is_additive`, `is_scalar_mx`, `is_scalar_mxP`, 
    `scalar_mx_is_scalar`, `mx0_is_scalar`, `scalar_mx_is_diag`, 
    `is_scalar_mx_is_diag`, `scalar_mx_is_trig`, `is_scalar_mx_is_trig`, 
    `mx11_scalar`, `scalar_mx_block`, `mxtrace`, `mxtrace_tr`, `mxtrace0`, 
    `mxtraceD`, `mxtrace_diag`, `mxtrace_scalar`, `trace_mx11`, 
    `mxtrace_block`
- in file `bigop.v`,
  + moved from `zmodp.v`: `big_ord1`, and `big_ord1_cond`.

- in file `poly.v`, deprecated `size_Xn_sub_1` (use `size_XnsubC`
  instead), and `monic_Xn_sub_1` (use `monicXnsubC` instead).

### Renamed

### Removed

- in `div.v`
  + definition `gcdn_rec`, use `gcdn` directly

- in `binomial.v`
  + definition `binomial_rec`, use `binomial` directly

- in `bigop.v`
  + definition `oAC_subdef`, use `oAC` directly

- in `fingroup.v`
  + definition `expgn_rec`, use `expgn` directly

- in `polydiv.v`
  + definition `gcdp_rec`, use `gcdp` directly

- in `nilpotent.v`
  + definition `lower_central_at_rec`, use `lower_central_at` directly
  + definition `upper_central_at_rec`, use `upper_central_at` directly

- in `commutator.v`
  + definition `derived_at_rec`, use `derived_at` directly

### Deprecated

- in `ssreflect.v`
  + notation `nosimpl` since `Arguments def : simpl never`
    does the job with Coq >= 8.18

- in `ssrfun.v`
  + notation scope `fun_scope`, use `function_scope` instead

- in `vector.v`
  + notation `vector_axiom`, use `Vector.axiom` instead

- in `ssrnat.v`
  + definition `addn_rec`, use `addn` directly
  + definition `subn_rec`, use `subn` directly
  + definition `muln_rec`, use `muln` directly
  + definition `expn_rec`, use `expn` directly
  + definition `fact_rec`, use `factorial` directly
  + definition `double_rec`, use `double` directly

- in `poly.v`
  + lemma `size_Xn_sub_1`, use `size_XnsubC` instead
  + lemma `monic_Xn_sub_1`, use `monic_XnsubC` instead

### Infrastructure

### Misc

