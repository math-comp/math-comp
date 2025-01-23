- in `intdiv.v`
  + `dvdz_charf` -> `dvdz_pcharf`

- in `poly.v`
	+ `char_poly` -> `pchar_poly`
	+ `prim_root_charF` -> `prim_root_pcharF`
	+ `char_prim_root` -> `pchar_prim_root`

- in `qpoly.v`
	+ `char_qpoly` -> `pchar_qpoly`

- in `sesquilinear.v`
	+ `is_symplectic` -> `is_psymplectic`
	+ `is_orthogonal` -> `is_porthogonal`

- in `ssralg.v`
	+ `char` -> `pchar`
	+ `[char _]` -> `[pchar _]`
	+ `has_char0` -> `has_pchar0`
	+ `Frobenius_aut` -> `pFrobenius_aut`
	+ `charf0` -> `pcharf0`
	+ `charf_prime` -> `pcharf_prime`
	+ `mulrn_char` -> `mulrn_pchar`
	+ `natr_mod_char` -> `natr_mod_pchar`
	+ `dvdn_charf` -> `dvdn_pcharf`
	+ `charf_eq` -> `pcharf_eq`
	+ `bin_lt_charf_0` -> `bin_lt_pcharf_0`
	+ `Frobenius_autE` -> `pFrobenius_autE`
	+ `Frobenius_aut0` -> `pFrobenius_aut0`
	+ `Frobenius_aut1` -> `pFrobenius_aut1`
	+ `Frobenius_autMn` -> `pFrobenius_autMn`
	+ `Frobenius_aut_nat` -> `pFrobenius_aut_nat`
	+ `Frobenius_autM_comm` -> `pFrobenius_autM_comm`
	+ `Frobenius_autX` -> `pFrobenius_autX`
	+ `addrr_char2` -> `addrr_pchar2`
	+ `Frobenius_autN` -> `pFrobenius_autN`
	+ `Frobenius_autB_comm` -> `pFrobenius_autB_comm`
	+ `exprNn_char` -> `exprNn_pchar`
	+ `oppr_char2` -> `oppr_pchar2`
	+ `subr_char2` -> `subr_pchar2`
	+ `addrK_char2` -> `addrK_pchar2`
	+ `rmorph_char` -> `rmorph_pchar`
	+ `Frobenius_aut_is_semi_additive` -> `pFrobenius_aut_is_semi_additive`
	+ `Frobenius_aut_is_multiplicative` -> `pFrobenius_aut_is_multiplicative`
	+ `exprDn_char` -> `exprDn_pchar`
	+ `natf_neq0` -> `natf_neq0'`
	+ `natf0_char` -> `natf0_pchar`
	+ `charf'_nat` -> `pcharf'_nat`
	+ `charf0P` -> `pcharf0P`
	+ `char0_natf_div` -> `pchar0_natf_div`
	+ `fmorph_char` -> `fmorph_pchar`
	+ `char_lalg` -> `pchar_lalg`

- in `ssrint.v`
	+ `Frobenius_autMz` -> `pFrobenius_autMz`
	+ `Frobenius_aut_int` -> `pFrobenius_aut_int`

- in `ssrnum.v`
	+ `char_num` -> `pchar_num`

- in `zmodp.v`
	+ `char_Zp` -> `pchar_Zp`
	+ `char_Fp` -> `pchar_Fp`
	+ `char_Fp_0` -> `pchar_Fp_0`

- in `classfun.v`
	+ `algC'G` -> `algC'G'`

- in `mxabelem.v`
	+ `rfix_pgroup_char` -> `rfix_pgroup_pchar`
	+ `pcore_sub_rstab_mxsimple` -> `pcore_sub_rstab_mxsimple'`
	+ `pcore_sub_rker_mx_irr` -> `pcore_sub_rker_mx_irr'`
	+ `pcore_faithful_mx_irr` -> `pcore_faithful_mx_irr'`
	+ `extraspecial_repr_structure` -> `extraspecial_repr_structure'`
	+ `faithful_repr_extraspecial` -> `faithful_repr_extraspecial'`

- in `mxrepresentation.v`
	+ `mx_Maschke` -> `mx_Maschke'`
	+ `rsim_regular_submod` -> `rsim_regular_submod'`
	+ `irr_mx_sum` -> `irr_mx_sum'`
	+ `Wedderburn_sum` -> `Wedderburn_sum'`
	+ `Wedderburn_sum_id` -> `Wedderburn_sum_id'`
	+ `Wedderburn_is_id` -> `Wedderburn_is_id'`
	+ `Wedderburn_closed` -> `Wedderburn_closed'`
	+ `Wedderburn_is_ring` -> `Wedderburn_is_ring'`
	+ `Wedderburn_min_ideal` -> `Wedderburn_min_ideal'`
	+ `not_rsim_op0` -> `not_rsim_op0'`
	+ `rsim_irr_comp` -> `rsim_irr_comp'`
	+ `irr_comp'_op0` -> `irr_comp'_op0'`
	+ `irr_comp_envelop` -> `irr_comp_envelop'`
	+ `ker_irr_comp_op` -> `ker_irr_comp_op'`
	+ `regular_op_inj` -> `regular_op_inj'`
	+ `rank_irr_comp` -> `rank_irr_comp'`
	+ `irr_comp_rsim` -> `irr_comp_rsim'`
	+ `irr_reprK` -> `irr_reprK'`
	+ `irr_repr'_op0` -> `irr_repr'_op0'`
	+ `op_Wedderburn_id` -> `op_Wedderburn_id'`
	+ `irr_comp_id` -> `irr_comp_id'`
	+ `rank_Wedderburn_subring` -> `rank_Wedderburn_subring'`
	+ `sum_irr_degree` -> `sum_irr_degree'`
	+ `irr_mx_mult` -> `irr_mx_mult'`
	+ `mxtrace_regular` -> `mxtrace_regular'`
	+ `linear_irr_comp` -> `linear_irr_comp'`
	+ `Wedderburn_subring_center` -> `Wedderburn_subring_center'`
	+ `Wedderburn_center` -> `Wedderburn_center'`
	+ `card_irr` -> `card_irr'`
	+ `cycle_repr_structure` -> `cycle_repr_structure'`
	+ `splitting_cyclic_primitive_root` -> `splitting_cyclic_primitive_root'`
	
- in `algC.v`
	+ `Cchar` -> `Cpchar`

- in `finfield.v`
	+ `finCharP` -> `finPcharP'`
	+ `card_finCharP` -> `card_finPcharP`
	+ `PrimeCharType` -> `pPrimeCharType`
	+ `primeChar_scale` -> `pprimeChar_scale`
	+ `primeChar_scaleA` -> `pprimeChar_scaleA`
	+ `primeChar_scale1` -> `pprimeChar_scale1`
	+ `primeChar_scaleDr` -> `pprimeChar_scaleDr`
	+ `primeChar_scaleDl` -> `pprimeChar_scaleDl`
	+ `primeChar_scaleAl` -> `pprimeChar_scaleAl`
	+ `primeChar_scaleAr` -> `pprimeChar_scaleAr`
	+ `primeChar_abelem` -> `pprimeChar_abelem`
	+ `primeChar_pgroup` -> `pprimeChar_pgroup`
	+ `order_primeChar` -> `order_pprimeChar`
	+ `card_primeChar` -> `card_pprimeChar`
	+ `primeChar_vectAxiom` -> `pprimeChar_vectAxiom`
	+ `primeChar_dimf` -> `pprimeChar_dimf`
	+ `PrimePowerField` -> pPrimePowerField`
	+ `FinDomainSplittingFieldType` -> `FinDomainSplittingFieldType'`

- in `separable.v`
	+ `char0_PET` -> `pchar0_PET`
	+ `separablePn` -> `separablePn'`
	+ `separable_exponent` -> `separable_exponent'`
	+ `charf0_separable` -> `pcharf0_separable`
	+ `charf_p_separable` -> `pcharf_p_separable
	+ `charf_n_separable` -> `pcharf_n_separable`
	+ `purely_inseparable_elementP` -> `purely_inseparable_elementP'`

- in `abelian.v`
	+ `fin_lmod_char_abelem` -> `fin_lmod_pchar_abelem`
	+ `fin_lmod_char_abelem` -> `fin_lmod_pchar_abelem`
    (`#1311 <https://github.com/coq/stdlib/pull/1311>`_,
    by Tragicus).
