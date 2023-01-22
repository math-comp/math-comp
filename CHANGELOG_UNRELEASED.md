# Changelog (unreleased)

To avoid having old PRs put changes into the wrong section of the CHANGELOG,
new entries now go to the present file as discussed
[here](https://github.com/math-comp/math-comp/wiki/Agenda-of-the-April-23rd-2019-meeting-9h30-to-12h30#avoiding-issues-with-changelog).

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

### Added

- in `seq.v`
  + lemmas `subset_mapP`, `take_min`, `take_taker`, `perm_allpairs_dep`, `perm_allpairs`
          
- in `path.v` 
  + lemmas `prefix_path`, `prefix_sorted`, `infix_sorted`, `suffix_sorted` 

- in `ssrbool.v`
  + notation `[in A]`

- in `seq.v`
  + lemmas `allT`, `all_mapT`, `inj_in_map`, and `mapK_in`.

- in `ssralg.v`
  + lemmas `natr1`, `nat1r`, `telescope_sumr_eq`, `telescope_prodr_eq`, `telescope_prodf_eq`

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
  + canonical instances `even_poly_additive`, `even_poly_linear`,
    `odd_poly_additive`, `odd_poly_linear`, `take_poly_additive`,
    `take_poly_linear`, `drop_poly_additive`, `drop_poly_linear`

- in `polydiv.v`
  + lemmas `Pdiv.RingMonic.drop_poly_rdivp`,
    `Pdiv.RingMonic.take_poly_rmodp`,
    `Pdiv.IdomainMonic.drop_poly_divp`,
    `Pdiv.IdomainMonic.take_poly_modp`

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
- in `finset.v`
  + lemmas `set_nil`, `set_seq1`

- in `ssralg.v`
  + lemmas `divrN`, `divrNN`

- in `bigop.v`
  + definition `oAC`
  + lemmas `oACE`, `some_big_AC_mk_monoid`, `big_AC_mk_monoid`
  + canonical instances `oAC_law` and `oAC_com_law`
  + lemmas `sub_le_big`, `sub_le_big_seq`, `sub_le_big_seq_cond`,
    `uniq_sub_le_big`, `uniq_sub_le_big_cond`, `idem_sub_le_big`,
    `idem_sub_le_big_cond`, `sub_in_le_big`, `le_big_ord`, `subset_le_big`,
    `le_big_nat_cond`, `le_big_nat`, `le_big_ord_cond`

- in `bigop.v`
  + lemma `subset_le_big_cond`

- in `order.v`
  + lemmas `bigmax_le`, `bigmax_lt`, `lt_bigmin`, `le_bigmin`,
    `bigmin_mkcond`, `bigmax_mkcond`, `bigmin_split`, `bigmax_split`,
    `bigmin_idl`, `bigmax_idl`, `bigmin_idr`, `bigmax_idr`,
    `bigminID`, `bigmaxID`, `sub_bigmin`, `sub_bigmax`,
    `sub_bigmin_seq`, `sub_bigmax_seq`, `sub_bigmin_cond`,
    `sub_bigmax_cond`, `sub_in_bigmin`, `sub_in_bigmax`,
    `le_bigmin_nat`, `le_bigmax_nat`, `le_bigmin_nat_cond`,
    `le_bigmax_cond`, `le_bigmin_ord`, `le_bigmax_ord`,
    `le_bigmin_ord_cond`, `le_bigmax_ord_cond`, `subset_bigmin`,
    `subset_bigmax`, `subset_bigmin_cond`, `subset_bigmax_cond`,
    `bigminD1`, `bigmaxD1`, `bigmin_le_cond`, `le_bigmax_cond`,
    `bigmin_le`, `le_bigmax`, `bigmin_inf`, `bigmax_sup`,
    `bigmin_geP`, `bigmax_leP`, `bigmin_gtP`, `bigmax_ltP`,
    `bigmin_eq_arg`, `bigmax_eq_arg`, `eq_bigmin`, `eq_bigmax`,
    `le_bigmin2`, `le_bigmax2`

### Changed

- in `poly.v`:
  + generalize `eq_poly`
- in `ssrbool.v`, `eqtype.v`, `seq.v`, `path.v`, `fintype.v`, `fingraph.v`,
  `prime.v`, `binomial.v`, `fingraph.v`, `bigop.v`, `ssralg.v`, `ssrnum.v`,
  `poly.v`, `mxpoly.v`, `action.v`, `perm.v`, `presentation.v`, `abelian.v`,
  `cyclic.v`, `frobenius.v`, `maximal.v`, `primitive_action.v`, `alt.v`,
  `burnside_app.v`, `mxrepresentation.v`, `mxabelian.v`, `character.v`,
  `inertia.v`, `integral_char.v`, `separable.v`, `galois.v`,
  `algebraics_fundamental.v`, changed `mem XXX` and `[mem XXX]` to `[in XX]`.
- Regressions: now redundanrt instances of `inE` rewriting `mem A x` to
  `x \in A` must be deleted or made optional, as `[in A] x` directly
  beta-reduces to `x \in A`.

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

- in `seq.v`:
  + changed names of implicit arguments of `map_id`, `eq_map`,
    `map_comp`, `mapK`, `eq_in_map`

### Renamed

- in `eqtype.v` and `gseries.v`, renamed `rel_of_simpl_rel` to `rel_of_simpl`,
  the actual name used in the coq `ssr.ssrbool.v` file.

### Removed

- in `matrix.v`:
  + notation `card_matrix` (deprecated in 1.13.0)

- in `rat.v`:
  + notation `divq_eq` (deprecated in 1.13.0)

- in `ssralg.v`:
  + notation `prodr_natmul` (deprecated in 1.13.0)

- in `bigop.v`:
  + notation `big_uncond` (deprecated in 1.13.0)

- in `finset.v`:
  + notations `mem_imset_eq` and `mem_imset2_eq` (deprecated in 1.13.0)

- in `order.v`:
  + notations `join_sup_seq`, `join_min_seq`, `join_sup`, `join_min`,
    `join_seq`, `meet_inf_seq`, `meet_max_seq`, `meet_seq` (deprecated
    in 1.13.0)

- in `path.v`:
  + notations `sup_path_in`, `sub_cycle_in`, `sub_sorted_in`,
    `eq_path_in`, `eq_cycle_in` (deprecated in 1.13.0)

- in `seq.v`:
  + notation `iota_add` (deprecated in 1.13.0)

- in `ssreflect.v`:
  + module `Deprecation` (deprecated in 1.13.0)
  + notatin `deprecate` (deprecated in 1.13.0)

- in `ssrnat.v`:
  + notatin `fact_smonotone` (deprecated in 1.13.0)

- in `ssrbool.v`, removed outdated `Coq 8.10` compatibility code.

### Infrastructure

### Misc

