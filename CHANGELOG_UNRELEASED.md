# Changelog (unreleased)

To avoid having old PRs put changes into the wrong section of the CHANGELOG,
new entries now go to the present file as discussed
[here](https://github.com/math-comp/math-comp/wiki/Agenda-of-the-April-23rd-2019-meeting-9h30-to-12h30#avoiding-issues-with-changelog).

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

### Added

- in `ssrnat.v`
  + lemmas `ltn_mull`, `ltn_mulr`

- in `ssrint.v`
  + lemmas `intrN`, `intrB`

- in `ssrnum.v`
  + lemma `invf_pgt`, `invf_pge`, `invf_ngt`, `invf_nge`
  + lemma `invf_plt`, `invf_ple`, `invf_nlt`, `invf_nle`

- in `bigop.v`
  + lemma `big_ord1`, `big_ord1_cond`, `big_rcons_op`, `big_change_idx`,
    `big_rcons`, `big_only1`, `big_mknat`
  + lemmas `big_rev`, `rev_big_rev` and `big_morph_in`

- in `eqtype.v`
  + definition `dfwith`
  + lemmas `dfwith_in`, `dfwith_out`, `dfwithP`

- in `seq.v`
  + lemmas `has_undup`, `all_undup`, `zip_uniql`, `zip_uniqr`

- in `finset.v`
  + definition `setXn`
  + lemmas `in_setXn`, `setXnP`, `cardsXn`, `setXnS`, `eq_setXn`, `enum_setU`,
    `enum_setI`, `has_set1`, `has_setU`, `all_set1`, `all_setU`,
    `big_subset_idem_cond`, `big_subset_idem`, `big_setU_cond`, `big_setU`

- in `prime.v`
  + lemmas `primeNsig`, `all_prime_primes`, `primes_eq0`, `totient_gt1`

- in `tuple.v`
  + lemmas `tnth_lshift`, `tnth_rshift`

- in `path.v`
  + lemmas `count_sort`, `sorted_cat_cons`, `gtn_sorted_uniq_geq`

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
    `rev_prodr`, `unitr_prod`, `unitr_prod_in`, `rev_prodrV`,
    `unitr_prodP`, `prodrV`

- in `ssrbool.v`
  + lemmas `classic_sigW`, `classic_ex`
- in `intdiv.v`
  + lemmas `dvdz_charf`, `eisenstein_crit`

- in `mxalgebra.v`
  + lemma `mulmxP`

- in `polydiv.v`
  + lemmas `root_dvdP`, `eqpW`, `irredp_XaddC`, `dvdp_exp_XsubCP`, `horner_mod`,
  + definition `mup`
  + lemmas `mup_geq`, `mup_leq`, `mup_ltn`, `XsubC_dvd`, `mup_XsubCX`,
    `mupNroot`, `mupMr`, `mupMl`, `mupM`, `mu_prod_XsubC`, `prod_XsubC_eq`

- in `vector.v`
  + lemmas `subset_limgP`, `lker0_img_cap`, `SubvsE`, `span_lfunP`,
    `fullv_lfunP`
  + definition `rVof`
  + lemmas `rVof_linear`, `coord_rVof`
  + definition `vecof`
  + lemmas `vecof_delta`, `vecof_linear`, `rVofK`, `vecofK`, `rVofE`,
    `coord_vecof`, `rVof_eq0`, `vecof_eq0`, 
  + definition `mxof`
  + lemma `mxof_linear`
  + definition `funmx`
  + lemma `funmx_linear`
  + definition `hommx`
  + lemmas `hommx_linear`, `mxofK`, `hommxK`, `mul_mxof`, `hommxE`,
    `rVof_mul`, `hom_vecof`, `rVof_app`, `vecof_mul`, `mxof_eq0`,
	 `hommx_eq0`, `mxof_comp`, `hommx_mul`
  + definitions `msof`, `vsof`
  + lemmas `mxof1`, `hommx1`, `msofK`, `mem_vecof`, `rVof_sub`, `vsof_sub`,
    `msof_sub`, `vsofK`, `sub_msof`, `sub_vsof`, `msof0`, `vsof0`, `msof_eq0`,
	 `vsof_eq0`
  + definitions `leigenspace`, `leigenvalue`
  + lemmas `lker_ker`, `limgE`, `leigenspaceE`

- in `action.v`
  + lemmas `perm_prime_atrans`, `perm_prime_orbit`, `perm_prime_astab`

- in `fingroup.v`
  + lemma `prod_subG`

- in `gproduct.v`
  + lemma `comm_prodG`
  + definitions `extnprod_mulg`, `extnprod_invg`
  + lemmas `extnprod_mul1g`, `extnprod_mulVg`, `extnprod_mulgA`, `oneg_ffun`,
    `mulg_ffun`, `invg_ffun`, `prodg_ffun`, `group_setXn`
  + definition `dfung1`
  + lemmas `dfung1_id`, `dfung1_dflt`, `dfung1_morphM`, `dffunM`, `injm_dfung1`,
    `group_set_dfwith`, `group_dfwithE`
  + definition `set1gXn`
  + lemmas `set1gXnE`, `set1gXnP`, `morphim_dfung1`, `morphim_dffunXn`,
    `set1gXn_group_set`, `setXn_prod`, `set1gXn_commute`, `setXn_dprod`,
	 `isog_setXn`, `setXn_gen`, `groupX0`

- in `perm.v`
  + lemmas `tpermJ_tperm`, `gen_tperm`

- in `order.v`
  + structures `meetSemilatticeType`, `bMeetSemilatticeType`,
    `tMeetSemilatticeType`, `tbMeetSemilatticeType`,
    `joinSemilatticeType`, `bJoinSemilatticeType`,
    `tJoinSemilatticeType`, `tbJoinSemilatticeType`,
    `tDistrLatticeType`, `bOrderType`, `tOrderType`, `tbOrderType`,
    `cDistrLatticeType` (relatively complemented distributive lattices),
    `ctDistrLatticeType` (dually sectionally complemented distributive lattices),
    `finBPOrderType`, `finTPOrderType`, `finTBPOrderType`,
    `finMeetSemilatticeType`, `finBMeetSemilatticeType`,
    `finJoinSemilatticeType`, and `finTJoinSemilatticeType`.
  + factories `isDuallyPOrder`, `Lattice_isDistributive`,
    `POrder_isMeetSemilattice`, `POrder_isJoinSemilattice`,
    `POrder_Meet_isSemilattice`, `POrder_Join_isSemilattice`,
    `DistrLattice_hasRelativeComplement`,
    `CDistrLattice_hasSectionalComplement`,
    `CDistrLattice_hasDualSectionalComplement`,
    `CDistrLattice_hasComplement`,
    `BDistrLattice_hasSectionalComplement`,
    `TDistrLattice_hasDualSectionalComplement`,
    `CBDistrLattice_hasComplement`, `CTDistrLattice_hasComplement`,
    `TBDistrLattice_hasComplement`
  + `rcompl x y z` is the relative complement of `z` in `[x, y]` defined for any
    `cDistrLatticeType` instance.
  + `codiff x y` is the dual sectional complement of `y` in `[x, \top]` defined
    for any `ctDistrLatticeType` instance.
  + lemmas `lt1x`, `ltx1`, `rcomplPmeet`, `rcomplPjoin`, `rcomplKI`,
    `rcomplKU`, `diffErcompl`, `codiffErcompl`, `complEdiff`,
    `complEcodiff`, `complErcompl`

- in `archimedean.v`
  + lemmas `floor_itv`, ` ge_floor`, `lt_succ_floor x`, `floor_ge_int`,
    `ceil_itv`, `gt_pred_ceil`, `le_ceil`, `ceil_le_int`, `ceil_floor`
  + lemmas `real_floorDrz`, `real_ceilDrz`, `floorDzr`, `floorDrz`, `ceilDzr`,
    `ceilDrz`
  + `archiRealDomainType` instance for `int` (moved from `ssrint.v`)
- in `intdiv.v`
  + lemma `irreducible_rat_int`

- new file `mxred.v`
  + definition `conjmx`
  + lemmas `stablemx_comp`, `stablemx_restrict`, `conjmxM`, `conjMmx`,
    `conjuMmx`, `conjMumx`, `conjuMumx`, `conjmx_scalar`, `conj0mx`,
    `conjmx0`, `conjumx`, `conj1mx`, `conjVmx`, `conjmxK`, `conjmxVK`,
    `horner_mx_conj`, `horner_mx_uconj`, `horner_mx_uconjC`, `mxminpoly_conj`,
    `mxminpoly_uconj`, `sub_kermxpoly_conjmx`, `sub_eigenspace_conjmx`,
    `eigenpoly_conjmx`, `eigenvalue_conjmx`, `conjmx_eigenvalue`
  + notation `restrictmx`
  + definition `similar_to`
  + notations `similar`, `similar_in`, `similar_in_to`, `all_similar_to`,
    `similar_diag`, `diagonalizable_in`, `diagonalizable`,
    `codiagonalizable_in`, `codiagonalizable`, `similar_trig`,
    `trigonalizable_in`, `trigonalizable`, `cotrigonalizable_in`,
    `cotrigonalizable`
  + lemmas `similarPp`, `similarW`, `similarP`, `similarRL`, `similarLR`,
    `similar_mxminpoly`, `similar_diag_row_base`, `similar_diagPp`,
    `similar_diagP`, `similar_diagPex`, `similar_diagLR`,
    `similar_diag_mxminpoly`, `similar_diag_sum`, `codiagonalizable1`,
    `codiagonalizablePfull`, `codiagonalizable_on`, `diagonalizable_diag`,
    `diagonalizable_scalar`, `diagonalizable0`, `diagonalizablePeigen`,
    `diagonalizableP`, `diagonalizable_conj_diag`, `codiagonalizableP`.

- new file `sesquilinear.v`
  + notations ``` ``_ ```, `e_`, `^`, `^t`
  + lemma `eq_map_mx_id`
  + mixin `InvolutiveRMorphism`
  + lemma `rmorphK`
  + definition `conjC`
  + lemma `map_mxCK`
  + mixin `isBilinear`
  + structure `Bilinear`
  + definition `bilinear_for`
  + factory `bilinear_isBilinear`
  + module `Bilinear` (contents not documented in the changelog)
  + notations `{bilinear _ -> _ -> _ | _ & _}`,
    `{bilinear _ -> _ -> _ | _}`, `{bilinear _ -> _ -> _}`,
    `{biscalar _}`
  + definition `applyr_head`, notation `applyr`
  + (coercions and canonicals not documented in the changelog)
  + lemmas `linear0r`, `linearNr`, `linearDr`, `linearBr`, `linearMnr`,
    `linearMNnr`, `linear_sumr`, `linearZr_LR`, `linearPr`
  + lemma `applyrE`
  + lemmas `linear0l`, `linearNl`, `linearDl`, `linearBl`, `linearMnl`,
    `linearMNnl`, `linear_sumlz`, `linearZl_LR`, `linearPl`, `linearZl`,
    `linearZr`, `linearZlr`, `linearZrl`
  + lemma `mulmx_is_bilinear`
  + definition `form`
  + lemmas `form0l`, `form0r`, `formDl`, `formDr`, `formZr`, `formZl`,
    `formNl`, `formNr`, `formee`, `form0_eq0`
  + mixin `isHermitianSesquilinear`, structure `Hermitian`, notation `{hermitian _ fo _ & _}`
  + definitions `orthomx`, `sesqui`, fact `sesqui_key`, canonical `sesqui_keyed`, notation `_.-sesqui`
  + lemmas `sesquiE`, `sesquiP`, `trmx_sesqui`, `maptrmx_sesqui`, `formC`, `form_eq0C`
  + definition `ortho`
  + lemmas `normalE`, `form_eq0P`, `normalP`, `normalC`, `normal_ortho_mx`,
    `normal_mx_ortho`, `rank_normal`
  + defintion `rad`
  + lemmas `rad_ker`, `formDd`, `formZ`, `formN`, `form_sign`, `formD`, `formB`, `formBd`
  + notations `symmetric_form`, `skew`, `hermitian`
  + mixin `isDotProduct`, structure `Dot`, notation `{dot _ for theta _}`
  + notations `{symmetric _}`, `{skew_symmetric _}`, `{hermitian_sym _ for _}`
  + definitions `is_skew`, `is_sym`, `is_hermsym`
  + lemmas `hermC`, `hnormN`, `hnorm_sign`, `hnormD`, `hnormB`, `hnormDd`, `hnormBd`
  + definition `ortho_rec`, fixpoint `pair_ortho_rec`, defintions `pairwise_orthogonal`, `orthogonal`,
    `orthonormal`
  + lemmas `orthogonal_cons`, `orthonormal_not0`, `orthonormalE`, `orthonormal_orthogonal`
  + definitions `isometry`, `isometry_from_to`
  + lemma `herm_eq0C`
  + definition `orthov`
  + lemmass `mem_orthovPn`, `mem_orthovP`, `orthov1E`, `orthovP`, `orthov_sym`, `mem_orthov1`,
    `orthov11`, `mem_orthov1_sym`, `orthov0`, `mem_orthov_sym`, `leq_dim_orthov1`, `dim_img_form_eq1`,
    `eq_dim_orthov1`, `dim_img_form_eq0`, `neq_dim_orthov1`, `leqif_dim_orthov1`, `leqif_dim_orthov1_full`,
    `orthogonal1P`, `orthogonalP`, `orthogonal_oppr`, `orthogonalE`, `orthovE`, `orthoDv`,
    `orthovD`
  + definitons `nondegenerate`, `is_symplectic`, `is_orthogonal`, `is_unitary`
  + lemmas `dnorm_geiff0`, `dnorm_ge0`, `dnorm_eq0`, `dnorm_gt0`, `sqrt_dnorm_ge0`,
    `sqrt_dnorm_eq0`, `sqrt_dnorm_gt0`, `dnormZ`, `dnormD`, `dnormB`, `pairwise_orthogonalP`,
    `pairwise_orthogonal_cat`, `orthonormal_cat`, `orthonormalP`, `sub_orthonormal`,
    `orthonormal2P`, `orthonormal2P`, `orthogonal_free`, `filter_pairwise_orthogonal`,
    `orthonormal_free`, `CauchySchwarzP`, `CauchySchwarz_sqrt`, `orthoP`, `orthoPl`,
    `orthogonal_sym`, `orthoPr`, `orthogonal_catl`, `orthogonal_catr`, `eq_pairwise_orthogonal`,
    `eq_orthonormal`, `orthogonal_oppl`, `triangle_lerif`, `span_orthogonal`, `orthogonal_split`,
  + definitions `normf1`, `normf2`
  + lemmas `isometry_of_dnorm`, `isometry_of_free`, `isometry_raddf_inj`
  + definitons `form_of_matrix`, `matrix_of_form`, `form_of_matrixr`
  + lemma `matrix_of_formE`, `form_of_matrix_is_bilinear`, `rV_formee`, `rV_form0_eq0`, `matrix_of_formK`
  + definition `hermitianmx`, fact `hermitianmx_key`, canonical `hermitianmx_keyed`, structure `hermitian_matrix`
  + lemmas `is_hermitianmxE`, `is_hermitianmxP`, `hermitianmxE`, `trmx_hermitian`, `maptrmx_hermitian`,
    `form_of_matrix_is_hermitian`, `orthomxE`, `hermmx_eq0P`, `orthomxP`, `orthomx_sym`,
    `ortho_ortho_mx`, `ortho_mx_ortho`, `rank_orthomx`, `radmxE`, `orthoNmx`, `orthomxN`, `orthoDmx`,
    `orthomxD`, `orthoZmx`, `orthomxZ`, `eqmx_ortho`, `genmx_ortho`
  + notations `symmetricmx`, `skewmx`, `hermsymmx`
  + lemma `hermitian1mx_subproof`, canonical `hermitian1mx`

- new file `spectral.v`
  + lemmas `eigenvalue_closed`, `common_eigenvector`, `common_eigenvector2`
  + notation `^t*`, `realmx`
  + lemmas `trmxCK`, `realmxC`, `realmxD`, `Remx_rect`, `Immx_rect`, `eqmx_ReiIm`,
    `realsym_hermsym`, `real_similar`
  + definition `unitarymx`, fact `unitarymx_key`, canonical `unitarymx_keyed`
  + lemmas `unitarymxP`, `mulmxtVK`, `unitarymx_unit`, `invmx_unitary`, `mulmxKtV`,
    `mxrank_unitary`, `mul_unitarymx`, `pinvmx_unitary`, `conjymx`, `trmx_unitary`,
    `conjC_unitary`, `trmxC_unitary`
  + definition `normalmx`, fact `normalmx_key`, canonical `normalmx_keyed`
  + lemmas `normalmxP`, `hermitian_normalmx`, `symmetric_normalmx`
  + definition `dotmx`
  + lemmas `dotmxE`, `row_unitarymxP`, `dotmx_is_dotmx`, `orthomx1E`, `orthomx1P`,
    `orthomx_disj`, `orthomx_ortho_disj`, `rank_ortho`, `add_rank_ortho`, `addsmx_ortho`,
    `ortho_id`, `submx_ortho`
  + definition `proj_ortho`
  + lemmas `sub_adds_genmx_ortho`, `cap_genmx_ortho`, `proj_ortho_sub`, `proj_ortho_compl_sub`,
    `proj_ortho_id`, `proj_ortho_0`, `add_proj_ortho`, `proj_ortho_proj`, `proj_orthoE`,
    `orthomx_proj_mx_ortho`
  + lemma `schmidt_subproof`, definition `schmidt`
  + lemmas `schmidt_unitarymx`, `row_schmidt_sub`, `form1_row_schmidt`, `schmidt_sub`,
    `eqmx_schmidt_full`, `eqmx_schmidt_free`
  + definiton `schmidt_complete`
  + lemmas `schmidt_complete_unitarymx`, `cotrigonalization`, `Schur`, `cotrigonalization2`
  + lemma `orthomx_spectral_subproof`, definitions `spectralmx`, `spectral_diag
  + lemmas `spectral_unitarymx`, `spectral_unit`, `orthomx_spectralP`, `hermitian_spectral_diag_real`

- in `ssrfun.v`:
  + definitions `idempotent_op`, `idempotent_fun`

### Changed

- in `seq.v`
  + fix incorrectly exported notations `'all_view` and `'has_view`

- in `bigop.v`
  + weaken hypothesis of lemma `telescope_sumn_in`

- in `zmodp.v`
  + simpler statement of `Fp_Zcast`

- in `path.v`
  + generalized `count_merge` from `eqType` to `Type`

- in `order.v`
  + `order_morphism` changed to `homo` from `mono` and renamed `nondecreasing`

- in `order.v`
  + The dual instances are now definitionally involutive, i.e., canonical
    instances of an order structure on `T^d^d` and `T` are convertible (the
    latter instance may require an eta-expansion on the type record for
    technical reasons). Similarly, canonical instances of an order structure on
    `(T1 *p T2)^d` and `T1^d *p T2^d` are convertible.
  + In order to achieve the above definitional properties on displays, the type
    of display is changed from `unit` to `Order.disp_t`, which is a primitive
    record type consisting of two fields of type `unit`.
  + The default displays for product and lexicographic orders are now defined
    separately for cartesian products and sequences. They take displays of the
    parameter types as parameters.
    * `prod_display d1 d2` is the default display for the product order of
      cartesian products of the form `T1 * T2`, where `T1` and `T2` have
      canonical orders of displays `d1` and `d2`, respectively.
    * `seqprod_display d` is the default display for the product order of
      sequences and tuples.
    * `lexi_display d1 d2` is the default display for the lexicographic order of
      cartesian products.
    * `seqlexi_display d` is the default display for the lexicographic order of
      sequences and tuples.
  + The operator notations for `seqprod_display` and `seqlexi_display` now use
    `^sp` and `^sl` in place of `^p` and `^l`, respectively.
  + `finLatticeType`, `finDistrLatticeType`, `finOrderType`, and
    `finCDistrLatticeType` now do not require the existence of top and bottom
    elements, i.e., their instances are not necessarily inhabited.
    Their counterparts with top and bottom are now `finTBLatticeType`,
    `finTBDistrLatticeType`, `finTBOrderType`, and `finCTBDistrLatticeType`,
    respectively.
  + lemmas `meetEdual`, `leUx`, `leUr`, `leUl`, `lexUl`, `lexUr`,
    `lexU2`, `leEjoin`, `eq_joinl`, `eq_joinr`, `join_idPl`,
    `join_idPr`, `join_l`, `join_r`, `leUidr`, `leU2`, `joinC`,
    `joinA`, `joinxx`, `joinAC`, `joinCA`, `joinACA`, `joinKU`,
    `joinUK`, `joinKUC`, `joinUKC` generalized from `latticeType` to
    `joinSemilatticeType`
  + lemmas `joinx0`, `join0x`, `join_eq0`, `joins_sup_seq`,
    `joins_min_seq`, `joins_sup`, `joins_min`, `joins_le`,
    `joinsP_seq`, `joinsP`, `le_joins`, `joins_setU`, `joins_seq`
    generalized from `bLatticeType` to `bJoinSemilatticeType`
  + lemmas `joinx1` and `join1x` generalized from `tLatticeType` to
    `tJoinSemilatticeType`
  + lemmas `joinEdual`, `lexI`, `leIr`, `leIl`, `leIxl`, `leIxr`,
    `leIx2`, `leEmeet`, `eq_meetl`, `eq_meetr`, `meet_idPl`,
    `meet_idPr`, `meet_l`, `meet_r`, `leIidl`, `leIidr`, `leI2`,
    `meetC`, `meetA`, `meetxx`, `meetAC`, `meetCA`, `meetACA`,
    `meetKI`, `meetIK`, `meetIKC` generalized from `latticeType` to
    `meetSemilatticeType`
  + lemmas `meet0x` and `meetx0` generalized from `bLatticeType` to
    `bMeetSemilatticeType`
  + lemmas `meetx1`, `meet1x`, `meet_eql`, `meets_inf_seq`,
    `meets_max_seq`, `meets_inf`, `meets_max`, `meets_ge`,
    `meetsP_seq`, `meetsP`, `le_meets`, `meets_setU`, `meets_seq`
    generalized from `tLatticeType` to `tMeetSemilatticeType`

- in `zmodp.v`
  + definitions `Zp_opp`, `Zp_add`, `Zp_mul`, `Zp_inv`
	 generalized from `'I_p.+1` to `'I_p`.
  + lemmas `Zp_addA`, `Zp_addC`, `Zp_mulC`, `Zp_mulA`, `Zp_mul_addr`,
	 `Zp_mul_addl`, `Zp_inv_out`
	 generalized from `'I_p.+1` to `'I_p`.

### Renamed

- in `binomial.v`
  + `triangular_sum` -> `bin2_sum`

- in `order.v` (cf. Changed section)
  + `finLatticeType` -> `finTBLatticeType`
  + `finDistrLatticeType` -> `finTBDistrLatticeType`
  + `finOrderType` -> `finTBOrderType`
  + `finCDistrLatticeType` -> `finCTBDistrLatticeType`

- in `archimedean.v`
  + `floor_itv` -> `real_floor_itv`
  + `ge_floor` -> `real_ge_floor`
  + `lt_succ_floor` -> `real_lt_succ_floor`
  + `floor_ge_int` -> `real_floor_ge_int`
  + `floorD` -> `real_floorDzr`
  + `ceil_itv` -> `real_ceil_itv`
  + `gt_pred_ceil` -> `real_gt_pred_ceil`
  + `le_ceil` -> `real_le_ceil`
  + `ceil_le_int` -> `real_ceil_le_int`
  + `ceilD` -> `real_ceilDzr`
  + `ceil_floor` -> `real_ceil_floor`

- in `ssrint.v`
  + `mulrzDr` -> `mulrzDl`
  + `mulrzDl` -> `mulrzDr`

### Removed

- in `seq.v`
  + notation `take_take` (deprecated since 1.16)

- in `order.v`
  + notations `0%O`, `1%O`, `0^d%O` and `1^d%O` (deprecated since 1.17)

- in `ssralg.v`
  + notation `rmorphX` (deprecated since 1.17)

- in `ssrnum.v`
  + notations `ler_opp2`, `ltr_opp2`, `lter_opp2`, `ler_oppr`,
    `ltr_oppr`, `lter_oppr`, `ler_oppl`, `ltr_oppl`, `lter_oppl`,
    `lteif_opp2`, `ler_add2l`, `ler_add2r`, `ler_add2`, `ltr_add2l`,
    `ltr_add2r`, `ltr_add2`, `lter_add2`, `ler_add`, `ler_lt_add`,
    `ltr_le_add`, `ltr_add`, `ler_sub`, `ler_lt_sub`, `ltr_le_sub`,
    `ltr_sub`, `ler_subl_addr`, `ler_subr_addr`, `ler_sub_addr`,
    `ltr_subl_addr`, `ltr_subr_addr`, `ltr_sub_addr`, `lter_sub_addr`,
    `ler_subl_addl`, `ltr_subl_addl`, `ler_subr_addl`,
    `ltr_subr_addl`, `ler_sub_addl`, `ltr_sub_addl`, `lter_sub_addl`,
    `ler_addl`, `ltr_addl`, `ler_addr`, `ltr_addr`, `ger_addl`,
    `gtr_addl`, `ger_addr`, `gtr_addr`, `cpr_add`, `lteif_add2l`,
    `lteif_add2r`, `lteif_add2`, `lteif_subl_addr`, `lteif_subr_addr`,
    `lteif_sub_addr`, `lteif_subl_addl`, `lteif_subr_addl`,
    `lteif_sub_addl`, `leif_add`, `gtr_opp`, `lteif_oppl`,
    `lteif_oppr`, `lteif_0oppr`, `lteif_oppr0`, `lter_oppE`,
    `ler_dist_add`, `ler_dist_norm_add`, `ler_sub_norm_add`,
    `ler_sub_dist`, `ler_sub_real`, `ger_sub_real`, `ltr_expn2r`,
    `ler_expn2r`, `lter_expn2r`, `ler_pmul`, `ltr_pmul`, `ler_pinv`,
    `ler_ninv`, `ltr_pinv`, `ltr_ninv`, `ler_pmul2l`, `ltr_pmul2l`,
    `lter_pmul2l`, `ler_pmul2r`, `ltr_pmul2r`, `lter_pmul2r`,
    `ler_nmul2l`, `ltr_nmul2l`, `lter_nmul2l`, `ler_nmul2r`,
    `ltr_nmul2r`, `lter_nmul2r`, `minr_pmulr`, `maxr_pmulr`,
    `minr_pmull`, `maxr_pmull`, `ltr_wpexpn2r`, `ler_pexpn2r`,
    `ltr_pexpn2r`, `lter_pexpn2r`, `ger_pmull`, `gtr_pmull`,
    `ger_pmulr`, `gtr_pmulr`, `ler_pmull`, `ltr_pmull`, `ler_pmulr`,
    `ltr_pmulr`, `ger_nmull`, `gtr_nmull`, `ger_nmulr`, `gtr_nmulr`,
    `ler_nmull`, `ltr_nmull`, `ler_nmulr`, `ltr_nmulr`, `leif_pmul`,
    `leif_nmul`, `eqr_expn2`, `real_maxr_nmulr`, `real_minr_nmulr`,
    `real_minr_nmull`, `real_maxr_nmull`, `real_ltr_distl_addr`,
    `real_ler_distl_addr`, `real_ltr_distlC_addr`,
    `real_ler_distlC_addr`, `real_ltr_distl_subl`,
    `real_ler_distl_subl`, `real_ltr_distlC_subl`,
    `real_ler_distlC_subl`, `ler_iexpn2l`, `ltr_iexpn2l`,
    `lter_iexpn2l`, `ler_eexpn2l`, `ltr_eexpn2l`, `lter_eexpn2l`,
    `ler_wpmul2l`, `ler_wpmul2r`, `ler_wnmul2l`, `ler_wnmul2r`,
    `ler_pemull`, `ler_nemull`, `ler_pemulr`, `ler_nemulr`,
    `ler_iexp`, `ltr_iexpr`, `lter_iexpr`, `ler_eexpr`, `ltr_eexpr`,
    `lter_eexpr`, `lter_expr`, `ler_wiexpn2l`, `ler_weexpn2l`,
    `ler_pimull`, `ler_nimull`, `ler_pimulr`, `ler_nimulr`,
    `ler_pmuln2r`, `ltr_pmuln2r`, `ler_pmuln2l`, `ler_wpmuln2l`,
    `eqr_pmuln2r`, `ltr_wmuln2r`, `ltr_wpmuln2r`, `ler_wmuln2r`,
    `ler_wnmuln2l`, `ler_muln2r`, `ltr_muln2r`, `eqr_muln2r`,
    `ltr_pmuln2l`, `ler_nmuln2l`, `ltr_nmuln2l`, `leif_subLR`,
    `leif_subRL`, `lteif_pmul2l`, `lteif_pmul2r`, `lteif_nmul2l`,
    `lteif_nmul2r`, `ler_paddl`, `ltr_paddl`, `ltr_spaddl`,
    `ltr_spsaddl`, `ler_naddl`, `ltr_naddl`, `ltr_snaddl`,
    `ltr_snsaddl`, `ler_paddr`, `ltr_paddr`, `ltr_spaddr`,
    `ltr_spsaddr`, `ler_naddr`, `ltr_naddr`, `ltr_snaddr`,
    `ltr_snsaddr`, `lef_pinv`, `lef_ninv`, `ltf_pinv`, `ltf_ninv`,
    `ltef_pinv`, `ltef_ninv`, `lteif_pdivl_mulr`, `lteif_pdivr_mulr`,
    `lteif_pdivl_mull`, `lteif_pdivr_mull`, `lteif_ndivl_mulr`,
    `lteif_ndivr_mulr`, `lteif_ndivl_mull`, `lteif_ndivr_mull`,
    `ler_pdivl_mulr`, `ltr_pdivl_mulr`, `lter_pdivl_mulr`,
    `ler_pdivr_mulr`, `ltr_pdivr_mulr`, `lter_pdivr_mulr`,
    `ler_pdivl_mull`, `ltr_pdivl_mull`, `lter_pdivl_mull`,
    `ler_pdivr_mull`, `ltr_pdivr_mull`, `lter_pdivr_mull`,
    `ler_ndivl_mulr`, `ltr_ndivl_mulr`, `lter_ndivl_mulr`,
    `ler_ndivr_mulr`, `ltr_ndivr_mulr`, `lter_ndivr_mulr`,
    `ler_ndivl_mull`, `ltr_ndivl_mull`, `lter_ndivl_mull`,
    `ler_ndivr_mull`, `ltr_ndivr_mull`, `lter_ndivr_mull`,
    `normC_add_eq`, `normC_sub_eq`, `ler_norm_add`, `ler_norm_sub`,
    `ltr_distl_addr`, `ler_distl_addr`, `ltr_distlC_addr`,
    `ler_distlC_addr`, `ltr_distl_subl`, `ler_distl_subl`,
    `ltr_distlC_subl`, `ler_distlC_subl`, `maxr_nmulr`, `minr_nmulr`,
    `minr_nmull`, `maxr_nmull` (deprecated since 1.17)
  + structures `archiNumDomainType`, `archiNumFieldType`,
    `archiClosedFieldType`, `archiDomainType`, `archiFieldType`, `archiRcfType`
    (deprecated since 2.1 and moved to `archimedean.v`)
  + factory `NumDomain_bounded_isArchimedean` (deprecated since 2.1 and moved to
    `archimedean.v`)
  + notations `Num.Def.trunc`, `Num.trunc`, `Num.Def.nat_num`, `Num.nat`,
    `Num.Def.int_num`, `Num.int`, `Num.bound` (deprecated since 2.1 and moved to
    `archimedean.v`)
  + lemmas `archi_boundP`, `upper_nthrootP`, `truncP`, `trunc_itv`
    (deprecated since 2.1)

- in `ssrint.v`
  + notations `oppz_add`, `lez_add1r`, `lez_addr1`, `ltz_add1r`,
    `ltz_addr1`, `ler_pmulz2r`, `ler_pmulz2l`, `ler_wpmulz2r`,
    `ler_wpmulz2l`, `ler_wnmulz2l`, `ler_nmulz2r`, `ler_nmulz2l`,
    `ltr_pmulz2r`, `ltr_pmulz2l`, `ltr_nmulz2r`, `ltr_nmulz2l`,
    `ler_wnmulz2r`, `ler_wpexpz2r`, `ler_wnexpz2r`, `ler_pexpz2r`,
    `ltr_pexpz2r`, `ler_nexpz2r`, `ltr_nexpz2r`, `ler_wpiexpz2l`,
    `ler_wniexpz2l`, `ler_wpeexpz2l`, `ler_wneexpz2l`, `ler_weexpz2l`,
    `ler_piexpz2l`, `ltr_piexpz2l`, `ler_niexpz2l`, `ltr_niexpz2l`,
    `ler_eexpz2l`, `ltr_eexpz2l`, `eqr_expz2`, `exprz_pmulzl`,
    `leq_add_dist`, `leqif_add_distz`, `leqif_add_dist` (deprecated
    since 1.17)
  + notation `polyC_mulrz` (deprecated since 2.1.0)
  + definition `Znat` (deprecated since 2.1)
  + lemmas `Znat_def`, `ZnatP` (deprecated since 2.1)
  + `archiDomainType` instance for `int` (moved to `archimedean.v`)

- in `fraction.v`
  + notation `tofracX` (deprecated since 1.17)

- in `interval.v`
  + notations `in_segment_addgt0Pr` and `in_segment_addgt0Pl`
    (deprecated since 1.17)

- in `mxrepresentation.v`
  + notation `mxval_grootX` (deprecated since 1.17)

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
  + notation `modp_mod` (deprecated since 2.1.0)

- in `nilpotent.v`
  + definition `lower_central_at_rec`, use `lower_central_at` directly
  + definition `upper_central_at_rec`, use `upper_central_at` directly

- in `commutator.v`
  + definition `derived_at_rec`, use `derived_at` directly

- in `binomial.v`
  + lemma `textbook_triangular_sum`

- in `eqtype.v`
  + notations `[eqType of T]`, `[eqType of T for C]`, and `[eqMixin of T by <:]`
  + notations `sub`, `subK`, `sub_spec`, and `subP`
  + notations `InjEqMixin`, `PcanEqMixin`, and `CanEqMixin`

- in `choice.v`
  + notations `[hasChoice of T]`, `[choiceType of T]`,
    `[choiceType of T for C]`, and `[choiceMixin of T by <:]`
  + notations `[isCountable of T]`, `[countType of T]`,
    `[countType of T for C]`, `[countMixin of T by <:]`, and
    `[subCountType of T]`
  + notations `CanChoiceMixin`, `PcanChoiceMixin`, `CanCountMixin`, and
    `PcanCountMixin`

- in `fintype.v`
  + notations `[finType of T]`, `[finType of T for C]`, `[subFinType of T]`,
    `[finMixin of T by <:]`
  + notations `EnumMixin`, `UniqMixin`, `CountMixin`, `FinMixin`,
    `UniqFinMixin`, `PcanFinMixin`, and `CanFinMixin`

- in `generic_quotient.v`
  + notations `[quotType of Q]` and `[eqQuotType e of Q]`

- in `order.v`
  + notations `[porderType of T]`, `[porderType of T with disp]`,
    `[porderType of T for cT]`, and `[porderType of T for cT with disp]`
  + notations `[latticeType of T]`, `[latticeType of T with disp]`,
    `[latticeType of T for cT]`, and `[latticeType of T for cT with disp]`
  + notations `[bLatticeType of T]` and `[bLatticeType of T for cT]`
  + notation `[bDistrLatticeType of T]`
  + notation `[tbDistrLatticeType of T]`
  + notation `[finPOrderType of T]`
  + notation `[finLatticeType of T]`
  + notation `[finDistrLatticeType of T]`
  + notation `[finCDistrLatticeType of T]`
  + notation `[finOrderType of T]`
  + notations `sub`, `subKI`, `subIK`, `subxx`, `subKU`, `subUK`, `subUx`,
    `sub_eq0`, `meet_eq0E_sub`, `eq_sub`, `subxU`, `subx0`, `sub0x`, `subIx`,
    `subxI`, `subBx`, `subxB`, `disj_subl`, `disj_subr`, `sub1x`, `subE`,
    `tnth_sub`, and `subEtpred`
  + notations `PcanPartial`, `CanPartial`, `PcanTotal`, `CanTotal`,
    `MonoTotalMixin`, `PcanPOrderMixin`, `CanPOrderMixin`, `PcanOrderMixin`,
    `CanOrderMixin`, `IsoLatticeMixin`, `IsoDistrLatticeMixin`
  + notations `comparable_le_minr`, `comparable_le_minl`, `comparable_lt_minl`,
    `comparable_lt_minr`, `comparable_le_maxr`, `comparable_le_maxl`,
    `comparable_lt_maxr`, `comparable_lt_maxl`, `le_maxl`, `le_maxr`,
    `lt_maxl`, `lt_maxr`, `lt_minr`, `lt_minl`, `le_minr`, `le_minl`
    (deprecated since 2.1.0)

- in `fingroup.v`
  + notations `[finGroupType of T]` and `[baseFinGroupType of T]`

- in `ssralg.v`
  + notations `[nmodType of T for cT]` and `[nmodType of T]`
  + notation ZmodMixin
  + notations `[zmodType of T for cT]` and `[zmodType of T]`
  + notations `[semiRingType of T]` and `[semiRingType of T for cT]`
  + notations `[ringType of T]` and `[ringType of T for cT]`
  + notations `[lmodType R of T]` and `[lmodType R of T for cT]`
  + notations `[lalgType R of T]` and `[lalgType R of T for cT]`
  + notations `[comSemiRingType of T]` and `[comSemiRingType of T for cT]`
  + notations `[comRingType of T]` and `[comRingType of T for cT]`
  + notations `[algType R of T]` and `[algType R of T for cT]`
  + notation `[comAlgType R of T]`
  + notations `[unitRingType of T]` and `[unitRingType of T for cT]`
  + notation `[comUnitRingType of T]`
  + notation `[unitAlgType R of T]`
  + notation `[comUnitAlgType R of T]`
  + notations `[idomainType of T]` and `[idomainType of T for cT]`
  + notations `[fieldType of T]` and `[fieldType of T for cT]`
  + notations `[decFieldType of T]` and `[decFieldType of T for cT]`
  + notations `[closedFieldType of T]` and `[closedFieldType of T for cT]`
  + definition `Additive.apply_deprecated`
  + notation `Additive.apply`
  + notations `[additive of f]` and `[additive of f as g]`
  + notations `[rmorphism of f]` and `[rmorphism of f as g]`
  + definition `Linear.apply_deprecated`
  + notation `Linear.apply`
  + notations `[linear of f]` and `[linear of f as g]`
  + definition `LRMorphism.apply_deprecated`
  + notation `LRMorphism.apply`
  + notation `[lrmorphism of f]`

- in `ring_quotient.v`
  + notation `[zmodQuotType z, o & a of Q]`
  + notation `[ringQuotType o & m of Q]`
  + notation `[unitRingQuotType u & i of Q]`

- in `countalg.v`
  + notation `[countNmodType of T]`
  + notation `[countZmodType of T]`
  + notation `[countSemiRingType of T]`
  + notation `[countRingType of T]`
  + notation `[countComSemiRingType of T]`
  + notation `[countComRingType of T]`
  + notation `[countUnitRingType of T]`
  + notation `[countComUnitRingType of T]`
  + notation `[countIdomainType of T]`
  + notation `[countFieldType of T]`
  + notation `[countDecFieldType of T]`
  + notation `[countClosedFieldType of T]`

- in `finalg.v`
  + notation `[finNmodType of T]`
  + notation `[finZmodType of T]`
  + notation `[finSemiRingType of T]`
  + notation `[finRingType of T]`
  + notation `[finComSemiRingType of T]`
  + notation `[finComRingType of T]`
  + notation `[finUnitRingType of T]`
  + notation `[finComUnitRingType of T]`
  + notation `[finIntegralDomainType of T]`
  + notation `[finFieldType of T]`
  + notation `[finLmodType R of T]`
  + notation `[finLalgType R of T]`
  + notation `[finAlgType R of T]`
  + notation `[finUnitAlgType R of T]`
  + notation `finIntegralDomainType` (deprecated since 2.1.0)

- in `ssrnum.v`
  + notations `[numDomainType of T]` and `[numDomainType of T for cT]`
  + notation `[numFieldType of T]`
  + notations `[numClosedFieldType of T]` and `[numClosedFieldType of T for cT]`
  + notation `[realDomainType of T]`
  + notation `[realFieldType of T]`
  + notations `[rcfType of T]` and `[rcfType of T for cT]`
  + notations `[archiFieldType of T]` and `[archiFieldType of T for cT]`

- in `rat.v`
  + lemma `divq_eq_deprecated`
  + definitions `Qint` and `Qnat` (deprecated since 2.1)
  + lemmas `QintP`, `Qnat_def`, `QnatP` (deprecated since 2.1)

- in `vector.v`
  + notations `[vectType R of T]` and `[vectType R of T for cT]`

- in `falgebra.v`
  + notations `[FalgType F of L]` and `[FalgType F of L for L']`
  + notation `FalgUnitRingType`

- in `fieldext.v`
  + notations `[fieldExtType F of L]` and `[fieldExtType F of L for K]`

- in `galois.v`
  + notations `[splittingFieldType F of L]` and
    `[splittingFieldType F of L for K]`

- in `order.v`
  + lemmas `dual_lt_def`, `dual_le_anti`, `dual_total`,
    `Order.BoolOrder.subKI`, `Order.BoolOrder.joinIB`
  + definition `Order.BoolOrder.sub`

- in `algC.v`
  + notations `Cint`, `Cnat`, `floorC`, `truncC` (deprecated in 2.1)
  + lemmas `Creal0`, `Creal1`, `floorC_itv`, `floorC_def`, `intCK`, `floorCK`,
    `floorC0`, `floorC1`, `floorCpK`, `floorCpP`, `Cint_int`, `CintP`,
    `floorCD`, `floorCN`, `floorCM`, `floorCX`, `rpred_Cint`, `Cint0`, `Cint1`,
    `Creal_Cint`, `conj_Cint`, `Cint_normK`, `CintEsign`, `truncC_itv`,
    `truncC_def`, `natCK`, `CnatP`, `truncCK`, `truncC_gt0`, `truncC0Pn`,
    `truncC0`, `truncC1`, `truncCD`, `truncCM`, `truncCX`, `rpred_Cnat`,
    `Cnat_nat`, `Cnat0`, `Cnat1`, `Cnat_ge0`, `Cnat_gt0`, `conj_Cnat`,
    `norm_Cnat`, `Creal_Cnat`, `Cnat_sum_eq1`, `Cnat_mul_eq1`, `Cnat_prod_eq1`,
    `Cint_Cnat`, `CintE`, `Cnat_norm_Cint`, `CnatEint`, `CintEge0`,
    `Cnat_exp_even`, `norm_Cint_ge1`, `sqr_Cint_ge1`, `Cint_ler_sqr`,
    `aut_Cnat`, `aut_Cint`, `Cnat_aut`, `Cint_aut`, `raddfZ_Cnat`,
    `raddfZ_Cint`, `rpredZ_Cnat`, `rpredZ_Cint` (deprecated in 2.1)

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

- in `binomial.v`
  + lemma `triangular_sum`, use `bin2_sum` instead
  + lemma `Pascal`, use `expnDn` instead
- in `zmodp.v`
  + lemmas `big_ord1`, `big_ord1_cond`

- in `order.v`
  + lemma `complE`,
    use `complEdiff` instead
  + factory `hasRelativeComplement`,
    use `BDistrLattice_hasSectionalComplement` instead
  + factory `hasComplement`,
    use `CBDistrLattice_hasComplement` instead

- in `ssrnum.v`:
  + lemma `mulr_sg_norm` (use `numEsg` instead)
  + lemma `eqr_norm_id` (use `ger0_def` instead)
  + lemma `eqr_normN` (use `ler0_def` instead)
  + lemma `real_mulr_sign_norm` (use `realEsign` instead)

- in `archimedean.v`
  + structure `archiDomainType` and its HB class `Num.ArchiDomain`
    (use `archiRealDomainType` and `Num.ArchiRealDomain` instead, respectively)
  + structure `archiFieldType` and its HB class `Num.ArchiField`
    (use `archiRealFieldType` and `Num.ArchiRealField` instead, respectively)

- in `ssrfun.v`:
  + definition `idempotent` (is now `idempotent_op`)

### Infrastructure

### Misc

