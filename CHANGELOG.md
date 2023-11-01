# Changelog
All notable changes to this project will be documented in this file.

Last releases: [[1.18.0] - 2023-11-01](#1180---2023-11-01), [[1.17.0] - 2023-05-09](#1170---2023-05-09), [[1.16.0] - 2023-02-01](#1160---2023-02-01), [[1.15.0] - 2022-06-30](#1150---2022-06-30), and [[1.14.0] - 2022-01-19](#1140---2022-01-19).

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [1.18.0] - 2023-11-01

This release is compatible with Coq versions 8.16, 8.17, and 8.18.

The contributors to this version are:

Reynald Affeldt, Sophie Bernard, Alessandro Bruni, Fernando Chu, Cyril Cohen, Josh Cohen, Hugo Deleye, Jason Gross, Pierre Jouvelot, Erik Martin-Dorel, Pierre Roux, Kazuhiko Sakaguchi, Julin Shaji, Enrico Tassi, Laurent Théry, Quentin Vermande

### Added

- in `ssrbool.v`
  + lemma `relpre_trans`

- in `ssrnat.v`
  + lemma `addn_eq1`

- in `seq.v`
  + lemma `foldl_foldr`
  + lemmas `find_pred0`, `find_predT`
  + lemmas `allrel_revl`, `allrel_revr`, `allrel_rev2`, `eq_allrel_meml`,
    `eq_allrel_memr`, `eq_allrel_mem2`
  + lemmas `sumn_ncons`, `sumn_set_nth`, `sumn_set_nth_ltn`,
    `sumn_set_nth0`
  + lemma `rem_mem`

- in `fintype.v`
  + definitions `ordS`, `ord_pred`
  + lemmas `ordS_subproof`, `ord_pred_subproof`, `ordSK`, `ord_predK`,
  `ordS_bij`, `ordS_inj`, `ord_pred_bij`, `ord_pred_inj`

- in `bigop.v`
  + lemma `big_if`
  + lemma `big_condT`
  + lemmas `sum_nat_seq_eq0`, `sum_nat_seq_neq0`, `sum_nat_seq_eq1`,
    `sum_nat_eq1`, `prod_nat_seq_eq0`, `prod_nat_seq_neq0`,
    `prod_nat_seq_eq1`, `prod_nat_seq_neq1`

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
  + lemmas `polyC_natr`, `char_poly`

- in `ssralg.v`
  + support for negative constant (like `-42`) in the `Number
    Notation` in `ring_scope`

- in `finalg.v`
  + lemmas `card_finRing_gt1`, `card_finField_unit`

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
  + lemmas `gerBl`, `gtrBl`
  + added `Num.npos` and lemma `nposrE`
  + added lemmas `ger0_le_norm`, `gtr0_le_norm`, `ler0_ge_norm` and `ltr0_ge_norm`

- in `polydiv.v`
  + lemmas `rmodp_id`, `rmodpN`, `rmodpB`, `rmodpZ`, `rmodp_sum`,
    `rmodp_mulml`, `rmodpX`, `rmodp_compr`

- in `zmodp.v`
  + lemmas `add_1_Zp`, `add_Zp_1`, `sub_Zp_1` and `add_N1_Zp`.

- in `cyclic.v`
  + added lemma `units_Zp_cyclic`

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

- in `qfpoly.v`
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

### Changed

- in `ssralg.v`
  + implicits of `natr1` and `nat1r`

### Renamed

- in `order.v`
  + `le_maxl` -> `ge_max`
  + `le_maxr` -> `le_max`
  + `lt_maxr` -> `lt_max`
  + `lt_maxl` -> `gt_max`
  + `lt_minr` -> `lt_min`
  + `lt_minl` -> `gt_min`
  + `le_minr` -> `le_min`
  + `le_minl` -> `ge_min`
  + `comparable_le_maxr` -> `comparable_le_max`
  + `comparable_le_maxl` -> `comparable_ge_max`
  + `comparable_lt_maxr` -> `comparable_lt_max`
  + `comparable_lt_maxl` -> `comparable_gt_max`
  + `comparable_lt_minl` -> `comparable_gt_min`
  + `comparable_lt_minr` -> `comparable_lt_min`
  + `comparable_le_minr` -> `comparable_le_min`
  + `comparable_le_minl` -> `comparable_ge_min`

- in `polydiv.v`
  + `modp_mod` -> `modp_id`

### Removed

- in `ssrbool.v`
  + `rel_of_simpl_rel` (use `rel_of_simpl`)

- in `fintype.v`
  + `enum_ordS` (use `enum_ordSl` instead)

### Deprecated

- in `ssrint.v`
  + `mulrzDr` temporarily deprecated, use `mulrzDl_tmp` instead,
    will eventually be renamed `mulrzDl`
  + `mulrzDl` temporarily deprecated, use `mulrzDr_tmp` instead,
    will eventually be renamed `mulrzDr`

## [1.17.0] - 2023-05-09

This release is compatible with Coq versions 8.15, 8.16 and 8.17.

The contributors to this version are:

Alex Gryzlov, Cyril Cohen, Jason Gross, Kazuhiko Sakaguchi, Kimaya Bedarkar,
Laurent Théry, Pierre Jouvelot, Pierre Roux, Quentin Vermande, Reynald Affeldt, Takafumi Saikawa,
Mitsuharu Yamamoto, Marina López Chamosa

### Added

- in `ssrfun.v`
  + lemmas `inj_omap`, `omap_id`, `eq_omap`, `omapK`

- in `ssrnat.v`
  + lemmas `addnCBA`, `addnBr_leq`, `addnBl_leq`, `subnDAC`,
    `subnCBA`, `subnBr_leq`, `subnBl_leq`, `subnBAC`, `subDnAC`,
    `subDnCA`, `subDnCAC`, `addnBC`, `addnCB`, `addBnAC`, `addBnCAC`,
    `addBnA`, `subBnAC`, `eqn_sub2lE`, `eqn_sub2rE`

- in `seq.v`
  + lemmas `find_pred0`, `find_predT`
  + lemmas `sumn_ncons`, `sumn_set_nth`, `sumn_set_nth_ltn`,
    `sumn_set_nth0`

- in `order.v`
  + notations `0%O`, `1%O`, `0^d%O` and `1^d%O` as backward compatible
    replacements of removed  notation `0`, `1`, `0^d` and `1^d`
    for bottom and top of lattices
  + notations `\top` and `\bot` for `Order.top` and `Order.bottom`
  + notations `\top^d` and `\bot^d` for `Order.dual_top` and `Order.dual_bottom`

- in `perm.v`
  + lemmas `perm_on_id`, `perm_onC`, `tperm_on`

- in `bigop.v`
  + lemma `big_if`

- in `finset.v`
  + lemma `bigA_distr`

- in `ssralg.v`
  + `bool` is now canonically a `fieldType` with additive law `addb` and
    multiplicative law `andb`

- in `finalg.v`
  + `bool` is now canonically a `finFieldType` and a `decFieldType`.

- in `poly.v`
  + lemmas `coef_prod_XsubC`, `coefPn_prod_XsubC`, `coef0_prod_XsubC`,
	 `polyOver_mulr_2closed`

### Changed

- in `ssrnat.v`
  + change the doubling and halving operators to be left-associative

- in `seq.v`,
  + notations `[seq x <- s | C ]`, `[seq x <- s | C1 & C2 ]`, `[seq E
    | i <- s ]`, `[seq E | i <- s & C ]`, `[seq E : R | i <- s ]`,
    `[seq E : R | i <- s & C ]`, `[seq E | x <- s, y <- t ]`, `[seq
    E : R | x <- s, y <- t ]` now support destructuring patterns in
    binder positions.

- in `fintype.v`,
  + notations `[seq F | x in A ]` and `[seq F | x ]` now support destructuring
    patterns in binder positions.  In the case of `[seq F | x ]` and `[seq F |
    x : T ]`, type inference on `x` now occurs earlier, meaning that implicit
    types and typeclass resolution in `T` will take precedence over unification
    constraints arising from typechecking `x` in `F`.  This may result in
    occasional incompatibilities.

- in `order.v`
  + fix lemmas `eq_bigmax` and `eq_bigmin` to respect given predicates
  + fix `\meet^p_` and `\join^p_` notations
  + fix the scope of `n.-tuplelexi` notations
  + fix the definition of `max_fun` (notation `\max`)
    which was equal to `min_fun`

- in `intdiv.v`
  + `zcontents` is now of type `{poly int} -> int`
  + `divz` is now of type `int -> int -> int`

### Renamed

- in `ssralg.v`:
  + `rmorphX` -> `rmorphXn`
- in `fraction.v`:
  + `tofracX` -> `tofracXn`
- in `ssrnum.v`:
  + `ler_opp2` -> `lerN2`
  + `ltr_opp2` -> `ltrN2`
  + `lter_opp2` -> `lterN2`
  + `ler_oppr` -> `lerNr`
  + `ltr_oppr` -> `ltrNr`
  + `lter_oppr` -> `lterNr`
  + `ler_oppl` -> `lerNl`
  + `ltr_oppl` -> `ltrNl`
  + `lter_oppl` -> `lterNl`
  + `lteif_opp2` -> `lteifN2`
  + `ler_add2l` -> `lerD2l`
  + `ler_add2r` -> `lerD2r`
  + `ltr_add2l` -> `ltrD2l`
  + `ltr_add2r` -> `ltD2r`
  + `ler_add2` -> `lerD2`
  + `ltr_add2` -> `ltrD2`
  + `lter_add2` -> `lterD2r`
  + `ler_add` -> `lerD`
  + `ler_lt_add` -> `ler_ltD`
  + `ltr_le_add` -> `ltr_leD`
  + `ltr_add` -> `ltrD`
  + `ler_sub` -> `lerB`
  + `ler_lt_sub` -> `ler_ltB`
  + `ltr_le_sub` -> `ltr_leB`
  + `ltr_sub` -> `ltrB`
  + `ler_subl_addr` -> `lerBlDr`
  + `ltr_subl_addr` -> `ltrBlDr`
  + `ler_subr_addr` -> `lerBrDr`
  + `ltr_subr_addr` -> `ltrBrDr`
  + `ler_sub_addr` -> `lerBDr`
  + `ltr_sub_addr` -> `ltrBDr`
  + `lter_sub_addr` -> `lterBDr`
  + `ler_subl_addl` -> `lerBlDl`
  + `ltr_subl_addl` -> `ltrBlDl`
  + `ler_subr_addl` -> `lerBrDl`
  + `ltr_subr_addl` -> `ltrBrDl`
  + `ler_sub_addl` -> `lerBDl`
  + `ltr_sub_addl` -> `ltrBDl`
  + `lter_sub_addl` -> `lterBDl`
  + `ler_addl` -> `lerDl`
  + `ltr_addl` -> `ltrDl`
  + `ler_addr` -> `lerDr`
  + `ltr_addr` -> `ltrDr`
  + `ger_addl` -> `gerDl`
  + `gtr_addl` -> `gtrDl`
  + `ger_addr` -> `gerDr`
  + `gtr_addr` -> `gtrDr`
  + `cpr_add` -> `cprD`
  + `lteif_add2l` -> `lteifD2l`
  + `lteif_add2r` -> `lteifD2r`
  + `lteif_add2` -> `lteifD2`
  + `lteif_subl_addr` -> `lteifBlDr`
  + `lteif_subr_addr` -> `lteifBrDr`
  + `lteif_sub_addr` -> `lteifBDr`
  + `lteif_subl_addl` -> `lteifBlDl`
  + `lteif_subr_addl` -> `lteifBrDl`
  + `lteif_sub_addl` -> `lteifBDl`
  + `ler_norm_add` -> `ler_normD`
  + `ler_norm_sub` -> `ler_normB`
  + `leif_add` -> `leifD`
  + `gtr_opp` -> `gtrN`
  + `lteif_oppl` -> `lteifNl`
  + `lteif_oppr` -> `lteifNr`
  + `lteif_0oppr` -> `lteif0Nr`
  + `lteif_oppr0` -> `lteifNr0`
  + `lter_oppE` -> `lterNE`
  + `ler_dist_add` -> `ler_distD`
  + `ler_dist_norm_add` -> `ler_dist_normD`
  + `ler_sub_norm_add` -> `lerB_normD`
  + `ler_sub_dist` -> `lerB_dist`
  + `ler_sub_real` -> `lerB_real`
  + `ger_sub_real` -> `gerB_real`
  + `ltr_expn2r` -> `ltrXn2r`
  + `ler_expn2r` -> `lerXn2r`
  + `lter_expn2r` -> `lterXn2r`
  + `ler_pmul` -> `ler_pM`
  + `ltr_pmul` -> `ltr_pM`
  + `ler_pinv` -> `ler_pV2`
  + `ler_ninv` -> `ler_nV2`
  + `ltr_pinv` -> `ltr_pV2`
  + `ltr_ninv` -> `ltr_nV2`
  + `ler_pmul2l` -> `ler_pM2l`
  + `ltr_pmul2l` -> `ltr_pM2l`
  + `lter_pmul2l` -> `lter_pM2l`
  + `ler_pmul2r` -> `ler_pM2r`
  + `ltr_pmul2r` -> `ltr_pM2r`
  + `lter_pmul2r` -> `lter_pM2r`
  + `ler_nmul2l` -> `ler_nM2l`
  + `ltr_nmul2l` -> `ltr_nM2l`
  + `lter_nmul2l` -> `lter_nM2l`
  + `ler_nmul2r` -> `ler_nM2r`
  + `ltr_nmul2r` -> `ltr_nM2r`
  + `lter_nmul2r` -> `lter_nM2r`
  + `lef_pinv` -> `lef_pV2`
  + `lef_ninv` -> `lef_nV2`
  + `ltf_pinv` -> `ltf_pV2`
  + `ltf_ninv` -> `ltf_nV2`
  + `ltef_pinv` -> `ltef_pV2`
  + `ltef_ninv` -> `ltef_nV2`
  + `minr_pmulr` -> `minr_pMr`
  + `maxr_pmulr` -> `maxr_pMr`
  + `minr_pmull` -> `minr_pMl`
  + `maxr_pmull` -> `maxr_pMl`
  + `ltr_wpexpn2r` -> `ltr_wpXn2r`
  + `ler_pexpn2r` -> `ler_pXn2r`
  + `ltr_pexpn2r` -> `ltr_pXn2r`
  + `lter_pexpn2r` -> `lter_pXn2r`
  + `ger_pmull` -> `ger_pMl`
  + `gtr_pmull` -> `gtr_pMl`
  + `ger_pmulr` -> `ger_pMr`
  + `gtr_pmulr` -> `gtr_pMr`
  + `ler_pmull` -> `ler_pMl`
  + `ltr_pmull` -> `ltr_pMl`
  + `ler_pmulr` -> `ler_pMr`
  + `ltr_pmulr` -> `ltr_pMr`
  + `ger_nmull` -> `ger_nMl`
  + `gtr_nmull` -> `gtr_nMl`
  + `ger_nmulr` -> `ger_nMr`
  + `gtr_nmulr` -> `gtr_nMr`
  + `ler_nmull` -> `ler_nMl`
  + `ltr_nmull` -> `ltr_nMl`
  + `ler_nmulr` -> `ler_nMr`
  + `ltr_nmulr` -> `ltr_nMr`
  + `leif_pmul` -> `leif_pM`
  + `leif_nmul` -> `leif_nM`
  + `eqr_expn2` -> `eqrXn2`
  + `real_maxr_nmulr` -> `real_maxr_nMr`
  + `real_minr_nmulr` -> `real_minr_nMr`
  + `real_minr_nmull` -> `real_minrnMl`
  + `real_maxr_nmull` -> `real_maxrnMl`
  + `real_ltr_distl_addr` -> `real_ltr_distlDr`
  + `real_ler_distl_addr` -> `real_ler_distlDr`
  + `real_ltr_distlC_addr` -> `real_ltr_distlCDr`
  + `real_ler_distlC_addr` -> `real_ler_distlCDr`
  + `real_ltr_distl_subl` -> `real_ltr_distlBl`
  + `real_ler_distl_subl` -> `real_ler_distlBl`
  + `real_ltr_distlC_subl` -> `real_ltr_distlCBl`
  + `real_ler_distlC_subl` -> `real_ler_distlCBl`
  + `ltr_distl_addr` -> `ltr_distlDr`
  + `ler_distl_addr` -> `ler_distlDr`
  + `ltr_distlC_addr` -> `ltr_distlCDr`
  + `ler_distlC_addr` -> `ler_distlCDr`
  + `ltr_distl_subl` -> `ltr_distlBl`
  + `ler_distl_subl` -> `ler_distlBl`
  + `ltr_distlC_subl` -> `ltr_distlCBl`
  + `ler_distlC_subl` -> `ler_distlCBl`
  + `maxr_nmulr` -> `maxr_nMr`
  + `minr_nmulr` -> `minr_nMr`
  + `minr_nmull` -> `minr_nMl`
  + `maxr_nmull` -> `maxr_nMl`
  + `ler_iexpn2l` -> `ler_iXn2l`
  + `ltr_iexpn2l` -> `ltr_iXn2l`
  + `lter_iexpn2l` -> `lter_iXn2l`
  + `ler_eexpn2l` -> `ler_eXn2l`
  + `ltr_eexpn2l` -> `ltr_eXn2l`
  + `lter_eexpn2l` -> `lter_eXn2l`
  + `ler_wpmul2l` -> `ler_wpM2l`
  + `ler_wpmul2r` -> `ler_wpM2r`
  + `ler_wnmul2l` -> `ler_wnM2l`
  + `ler_wnmul2r` -> `ler_wnM2r`
  + `ler_pemull` -> `ler_peMl`
  + `ler_nemull` -> `ler_neMl`
  + `ler_pemulr` -> `ler_peMr`
  + `ler_nemulr` -> `ler_neMr`
  + `ler_iexpr` -> `ler_iXnr`
  + `ltr_iexpr` -> `ltr_iXnr`
  + `lter_iexpr` -> `lter_iXnr`
  + `ler_eexpr` -> `ler_eXnr`
  + `ltr_eexpr` -> `ltr_eXnr`
  + `lter_eexpr` -> `lter_eXnr`
  + `lter_expr` -> `lter_Xnr`
  + `ler_wiexpn2l` -> `ler_wiXn2l`
  + `ler_weexpn2l` -> `ler_weXn2l`
  + `ler_pimull` -> `ler_piMl`
  + `ler_nimull` -> `ler_niMl`
  + `ler_pimulr` -> `ler_piMr`
  + `ler_nimulr` -> `ler_niMr`
  + `lteif_pdivl_mulr` -> `lteif_pdivlMr`
  + `lteif_pdivr_mulr` -> `lteif_pdivrMr`
  + `lteif_pdivl_mull` -> `lteif_pdivlMl`
  + `lteif_pdivr_mull` -> `lteif_pdivrMl`
  + `lteif_ndivl_mulr` -> `lteif_ndivlMr`
  + `lteif_ndivr_mulr` -> `lteif_ndivrMr`
  + `lteif_ndivl_mull` -> `lteif_ndivlMl`
  + `lteif_ndivr_mull` -> `lteif_ndivrMl`
  + `ler_pdivl_mulr` -> `ler_pdivlMr`
  + `ltr_pdivl_mulr` -> `ltr_pdivlMr`
  + `lter_pdivl_mulr` -> `lter_pdivlMr`
  + `ler_pdivr_mulr` -> `ler_pdivrMr`
  + `ltr_pdivr_mulr` -> `ltr_pdivrMr`
  + `lter_pdivr_mulr` -> `lter_pdivrMr`
  + `ler_pdivl_mull` -> `ler_pdivlMl`
  + `ltr_pdivl_mull` -> `ltr_pdivlMl`
  + `lter_pdivl_mull` -> `lter_pdivlMl`
  + `ler_pdivr_mull` -> `ler_pdivrMl`
  + `ltr_pdivr_mull` -> `ltr_pdivrMl`
  + `lter_pdivr_mull` -> `lter_pdivrMl`
  + `ler_ndivl_mulr` -> `ler_ndivlMr`
  + `ltr_ndivl_mulr` -> `ltr_ndivlMr`
  + `lter_ndivl_mulr` -> `lter_ndivlMr`
  + `ler_ndivr_mulr` -> `ler_ndivrMr`
  + `ltr_ndivr_mulr` -> `ltr_ndivrMr`
  + `lter_ndivr_mulr` -> `lter_ndivrMr`
  + `ler_ndivl_mull` -> `ler_ndivlMl`
  + `ltr_ndivl_mull` -> `ltr_ndivlMl`
  + `lter_ndivl_mull` -> `lter_ndivlMl`
  + `ler_ndivr_mull` -> `ler_ndivrMl`
  + `ltr_ndivr_mull` -> `ltr_ndivrMl`
  + `lter_ndivr_mull` -> `lter_ndivrMl`
  + `eqr_pmuln2r` -> `eqr_pMn2r`
  + `ler_muln2r` -> `lerMn2r`
  + `ler_pmuln2r` -> `ler_pMn2r`
  + `ler_pmuln2l` -> `ler_pMn2l`
  + `ltr_pmuln2r` -> `ltr_pMn2r`
  + `ltr_wmuln2r` -> `ltr_wMn2r`
  + `ler_wmuln2r` -> `ler_wMn2r`
  + `ltr_wpmuln2r` -> `ltr_wpMn2r`
  + `ler_wpmuln2l` -> `ler_wpMn2l`
  + `ler_wnmuln2l` -> `ler_wnMn2l`
  + `ltr_muln2r` -> `ltrMn2r`
  + `eqr_muln2r` -> `eqrMn2r`
  + `ltr_pmuln2l` -> `ltr_pMn2l`
  + `ler_nmuln2l` -> `ler_nMn2l`
  + `ltr_nmuln2l` -> `ltr_nMn2l`
  + `normC_add_eq` -> `normCDeq`
  + `normC_sub_eq` -> `normCBeq`
  + `leif_subLR` -> `leifBLR`
  + `leif_subRL` -> `leifBRL`
- in `ssrint.v`:
  + `leq_add_dist` -> `leqD_dist`
  + `lez_add1r` -> `lez1D`
  + `lez_addr1` -> `lezD1`
  + `ltz_add1r` -> `ltz1D`
  + `ltz_addr1` -> `ltzD1`
  + `oppz_add` -> `oppzD`
  + `leqif_add_distz` -> `leqifD_distz`
  + `leqif_add_dist` -> `leqifD_dist`
  + `ler_pmulz2r` -> `ler_pMz2r`
  + `ler_pmulz2l` -> `ler_pMz2l`
  + `ler_wpmulz2r` -> `ler_wpMz2r`
  + `ler_wpmulz2l` -> `ler_wpMz2l`
  + `ler_wnmulz2l` -> `ler_wnMz2l`
  + `ler_nmulz2r` -> `ler_nMz2r`
  + `ltr_pmulz2r` -> `ltr_pMz2r`
  + `ler_nmulz2l` -> `ler_nMz2l`
  + `ltr_pmulz2l` -> `ltr_pMz2l`
  + `ltr_nmulz2r` -> `ltr_nMz2r`
  + `ltr_nmulz2l` -> `ltr_nMz2l`
  + `ler_wnmulz2r` -> `ler_wnMz2r`
  + `ler_wpexpz2r` -> `ler_wpXz2r`
  + `ler_wnexpz2r` -> `ler_wnXz2r`
  + `ler_pexpz2r` -> `ler_pXz2r`
  + `ltr_pexpz2r` -> `ltr_pXz2r`
  + `ler_nexpz2r` -> `ler_nXz2r`
  + `ltr_nexpz2r` -> `ltr_nXz2r`
  + `ler_wpiexpz2l` -> `ler_wpiXz2l`
  + `ler_wniexpz2l` -> `ler_wniXz2l`
  + `ler_wpeexpz2l` -> `ler_wpeXz2l`
  + `ler_wneexpz2l` -> `ler_wneXz2l`
  + `ler_weexpz2l` -> `ler_weXz2l`
  + `ler_piexpz2l` -> `ler_piXz2l`
  + `ltr_piexpz2l` -> `ltr_piXz2l`
  + `ler_niexpz2l` -> `ler_niXz2l`
  + `ltr_niexpz2l` -> `ltr_niXz2l`
  + `ler_eexpz2l` -> `ler_eXz2l`
  + `ltr_eexpz2l` -> `ltr_eXz2l`
  + `eqr_expz2` -> `eqrXz2`
  + `exprz_pmulzl` -> `exprz_pMzl`
  + `lteif_pmul2l` -> `lteif_pM2l`
  + `lteif_pmul2r` -> `lteif_pM2r`
  + `lteif_nmul2l` -> `lteif_nM2l`
  + `lteif_nmul2r` -> `lteif_nM2r`
  + `ler_paddl` -> `ler_wpDl`
  + `ltr_paddl` -> `ltr_wpDl`
  + `ltr_spaddl` -> `ltr_pwDl`
  + `ltr_spsaddl` -> `ltr_pDl`
  + `ler_naddl` -> `ler_wnDl`
  + `ltr_naddl` -> `ltr_wnDl`
  + `ltr_snaddl` -> `ltr_nwDl`
  + `ltr_snsaddl` -> `ltr_nDl`
  + `ler_paddr` -> `ler_wpDr`
  + `ltr_paddr` -> `ltr_wpDr`
  + `ltr_spaddr` -> `ltr_pwDr`
  + `ltr_spsaddr` -> `ltr_pDr`
  + `ler_naddr` -> `ler_wnDr`
  + `ltr_naddr` -> `ltr_wnDr`
  + `ltr_snaddr` -> `ltr_nwDr`
  + `ltr_snsaddr` -> `ltr_nDr`
- in `interval.v`:
  + `in_segment_addgt0Pr` -> `in_segmentDgt0Pr`
  + `in_segment_addgt0Pl` -> `in_segmentDgt0Pl`
- in `mxrepresentation.v`:
  + `mxval_grootX` -> `mxval_grootXn`

### Removed

- in `ssrbool.v`
  + notation `mono2W_in` that was deprecated in 1.14.0

- in `order.v`
  + notations `0`, `1`, `0^d` and `1^d` in `order_scope`

### Deprecated

- in `order.v`
  + notations `0%O`, `1%O`, `0^d%O` and `1^d%O`

## [1.16.0] - 2023-02-01

This release is compatible with Coq versions 8.13, 8.14, 8.15, 8.16 and 8.17.

The contributors to this version are:

Cyril Cohen, Enrico Tassi, Erik Martin-Dorel, Georges Gonthier,
Yoshihiro Ishiguro, Julien Puydt, Kazuhiko Sakaguchi, Laurent Théry,
Mireia G. Bedmar, Pierre-Marie Pédrot, Pierre Roux, Pierre Pomeret-Coquot, Quentin Vermande,
Reynald Affeldt, Takafumi Saikawa, Yoshihiro Imai

### Added

- in `ssrbool.v`
  + notation `[in A]`
  + lemmas `if_and`, `if_or`, `if_implyb`, `if_impliybC`, `if_add`

- in `eqtype.v`
  + lemmas `existsb` and `exists_inb`

- in `ssrnat.v`
  + lemma `leqVgt`
  + lemmas `ltn_half_double`, `leq_half_double`, `gtn_half_double`
  + lemma `double_pred`
  + lemmas `uphalfE`, `ltn_uphalf_double`, `geq_uphalf_double`, `gtn_uphalf_double`
  + lemmas `halfK`, `uphalfK`, `odd_halfK`, `even_halfK`, `odd_uphalfK`, `even_uphalfK`
  + lemmas `leq_sub2rE`, `leq_sub2lE`, `ltn_sub2rE`, `ltn_sub2lE`

- in `seq.v`
  + lemmas `subset_mapP`, `take_min`, `take_taker`, `perm_allpairs_dep`, `perm_allpairs`
  + lemmas `allT`, `all_mapT`, `inj_in_map`, and `mapK_in`.
  + lemma `if_nth`

- in `path.v`
  + lemmas `prefix_path`, `prefix_sorted`, `infix_sorted`, `suffix_sorted`

- in `finset.v`
  + lemmas `set_nil`, `set_seq1`

- in `bigop.v`
  + lemmas `big_ord1_eq`, `big_ord1_cond_eq`, `big_nat1_eq`,
    `big_nat1_cond_eq`
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
  + definition `oAC`
  + lemmas `oACE`, `some_big_AC_mk_monoid`, `big_AC_mk_monoid`
  + canonical instances `oAC_law` and `oAC_com_law`
  + lemmas `sub_le_big`, `sub_le_big_seq`, `sub_le_big_seq_cond`,
    `uniq_sub_le_big`, `uniq_sub_le_big_cond`, `idem_sub_le_big`,
    `idem_sub_le_big_cond`, `sub_in_le_big`, `le_big_ord`, `subset_le_big`,
    `le_big_nat_cond`, `le_big_nat`, `le_big_ord_cond`
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

- in `ssralg.v`
  + lemmas `natr1`, `nat1r`, `telescope_sumr_eq`, `telescope_prodr_eq`, `telescope_prodf_eq`
  + lemma `eqr_sum_div`
  + lemmas `divrN`, `divrNN`

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

- in `ssrnum.v`
  + lemmas `psumr_neq0`, `psumr_neq0P`

- in `ssrint.v`
  + printing only notation for `x = y :> int`, opening `int_scope` on
    `x` and `y` to better match the already existing parsing only
    notation with the introduction of number notations in `ring_scope`

- in `matrix.v`
  + definitions `Vandermonde`, `map2_mx`
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

### Changed

- in `seq.v`:
  + changed names of implicit arguments of `map_id`, `eq_map`,
    `map_comp`, `mapK`, `eq_in_map`

- in `ssrbool.v`, `eqtype.v`, `seq.v`, `path.v`, `fintype.v`, `fingraph.v`,
  `prime.v`, `binomial.v`, `fingraph.v`, `bigop.v`, `ssralg.v`, `ssrnum.v`,
  `poly.v`, `mxpoly.v`, `action.v`, `perm.v`, `presentation.v`, `abelian.v`,
  `cyclic.v`, `frobenius.v`, `maximal.v`, `primitive_action.v`, `alt.v`,
  `burnside_app.v`, `mxrepresentation.v`, `mxabelian.v`, `character.v`,
  `inertia.v`, `integral_char.v`, `separable.v`, `galois.v`,
  `algebraics_fundamental.v`, changed `mem XXX` and `[mem XXX]` to `[in XX]`.
- Regressions: now redundant instances of `inE` rewriting `mem A x` to
  `x \in A` must be deleted or made optional, as `[in A] x` directly
  beta-reduces to `x \in A`.

- in `poly.v`:
  + generalize `eq_poly`
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

### Renamed

- in `eqtype.v` and `gseries.v`, renamed `rel_of_simpl_rel` to `rel_of_simpl`,
  the actual name used in the coq `ssr.ssrbool.v` file.

### Removed

- in `ssreflect.v`:
  + module `Deprecation` (deprecated in 1.13.0)
  + notatin `deprecate` (deprecated in 1.13.0)

- in `ssrbool.v`, removed outdated `Coq 8.10` compatibility code.

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

- in `ssrnat.v`:
  + notatin `fact_smonotone` (deprecated in 1.13.0)

- in `matrix.v`:
  + notation `card_matrix` (deprecated in 1.13.0)

- in `rat.v`:
  + notation `divq_eq` (deprecated in 1.13.0)

- in `ssralg.v`:
  + notation `prodr_natmul` (deprecated in 1.13.0)

## [1.15.0] - 2022-06-30

This release is compatible with Coq versions 8.13, 8.14, 8.15 and 8.16.

The contributors to this version are:
Cyril Cohen, ed-hermoreyes, Enrico Tassi, Erik Martin-Dorel, Evgenii Moiseenko,
Georges Gonthier, Jonathan Sterling, Kazuhiko Sakaguchi, Laurent Théry,
Mireia G. Bedmar, Pierre Jouvelot, Pierre Roux, Reynald Affeldt,
Wojciech Karpiel

### Added

- in `bigop.v`
  + lemmas `leq_prod`,`telescope_big`, `telescope_sumn`, `telescope_sumn_in`
    `leq_bigmax_seq`, `bigmax_leqP_seq`, `bigmax_sup_seq`, `eq_bigl_supp`,
    `perm_big_supp_cond`, `perm_big_supp`

- in `path.v`
  + lemma `sortedP`

- in `seq.v`,
  + definitions `prefix`, `suffix`, `infix`, `infix_index`
  + lemmas `nilpE`, `prefixE`, `prefix_refl`, `prefixs0`, `prefix0s`,
    `prefix_cons`, `prefix_catr`, `prefix_prefix`, `prefixP`, `prefix_trans`,
    `prefixs1`, `catl_prefix`, `prefix_catl`, `prefix_rcons`, `prefix_rev`,
    `prefix_revLR`, `prefix1s`, `prefix_uniq`, `prefix_take`, `prefix_drop_gt0`,
    `size_prefix`, `suffixE`, `suffix_refl`, `suffixs0`, `suffix0s`,
    `suffix_rev`, `suffix_revLR`, `suffix_suffix`, `suffixP`, `suffix_trans`,
    `suffix_rcons`, `suffix_catl`, `suffix_catr`, `catl_suffix`, `suffix_cons`,
    `suffixW`, `suffix1s`, `suffix_uniq`, `suffix_drop`, `size_suffix`,
    `infix0s`, `infixs0`, `infix_consl`, `infix_indexss`, `infix_index_le`,
    `infixTindex`, `infixPn`, `infix_index0s`, `infix_indexs0`, `infixE`,
    `infix_refl`, `prefixW`, `prefix_infix`, `infix_infix`, `suffix_infix`,
    `infixP`, `infix_rev`, `infix_trans`, `infix_revLR`, `infix_rconsl`,
    `infix_cons`, `infixs1`, `catl_infix`, `catr_infix`, `cons2_infix`,
    `rcons2_infix`, `catr2_infix`, `catl2_infix`, `infix_catl`, `infix_catr`,
    `prefix_infix_trans`, `suffix_infix_trans`, `infix_prefix_trans`,
    `infix_suffix_trans`, `prefix_suffix_trans`, `suffix_prefix_trans`,
    `infixW`, `mem_infix`, `infix1s`, `infix_rcons`, `infix_uniq`,
    `infix_take`, `infix_drop`, `consr_infix`, `consl_infix`, `prefix_index`,
    `size_infix`, `mkseqS`, `mkseq_uniqP`,`nth_seq1`, `set_nthE`,
    `count_set_nth`, `count_set_nth_ltn`, `count_set_nthF`, `subseq_anti`,
    `size_take_min`, `subseq_anti`

- in `ssralg.v`
  + notation `\- f` for definition `opp_fun`
  + notation `f \* g` for definition `mul_fun`
  + lemmas `opp_fun_is_additive` and `opp_fun_is_scalable`
  + canonical instances `opp_fun_additive` and `opp_fun_linear`
  + missing export for `eqr_div`
  + number notation in scope ring_scope, numbers such as `12` or `42`
    are now read as `12%:R` or `42%:R`

- in `rat.v`
  + Number Notation for numbers of the form `-? [0-9][0-9_]* ([.][0-9_]+)?`
    in scope `rat_scope` (for instance 12%Q or 3.14%Q)
  + lemma `rat_vm_compute` which is a specialization to the rewriting
    rule `vm_compute` to trigger `vm_compute` by a rewrite

- in `ssrint.v`
  + number notation in scope int_scope, `12` or `-42`
    are now read as `Posz 12` or `Negz 41`
  + number notation in scope ring_scope, numbers such as `-12` are now
    read as `(-12)%:~R`

- in `fintype.v`
  + lemmas `enum_ord0`, `enum_ordSl`, `enum_ordSr`

- in `ssrbool.v`
  + definition `pred_oapp`
  + lemmas `all_sig2_cond`, `all_sig2_cond`, `can_in_pcan`, `pcan_in_inj`,
    `in_inj_comp`, `can_in_comp`, `pcan_in_comp`, `ocan_in_comp`, `eqbLR`,
    `eqbRL`, `homo_mono1`

- in `choice.v`
  + coercion `Choice.mixin`

- in `eqtype.v`
  + notations `eqbLHS` and `eqbRHS`

- in `order.v`
  + notations `leLHS`, `leRHS`, `ltLHS`, `ltRHS`
  + notation `f \min g` and `f \max g` for definitions `min_fun` and `max_fun`
  + lemma `le_le_trans`

- in `ssrnat.v`
  + notations `leqLHS`, `leqRHS`, `ltnLHS`, `ltnRHS`
  + lemmas `geq_half_double`, `leq_uphalf_double`
  
- in `ssrfun.v`
  + definition `olift`
  + lemmas `obindEapp`, `omapEbind`, `omapEapp`, `oappEmap`, `omap_comp`,
    `oapp_comp`, `oapp_comp_f`, `olift_comp`, `compA`, `ocan_comp`

- in `tuple.v`
  + lemma `tuple_uniqP`

- in `ssreflect.v`:
  + typeclass `vm_compute_eq` and lemma `vm_compute`
    in order to trigger a call to the tactic `vm_compute` when rewriting
    using `rewrite [pattern]vm_compute`
  + notation `[elaborate t]` forcing the elaboration of `t` using Coq's `refine`
    tactic. This notation can be used in tandem with `have` to force type class
    resolution when an explicit proof term `t` is provided (otherwise type
    class instances are quantified implicitly by `have`)

- in `ssrnum.v`
  + lemmas `mulCii`, `ReE`, `ImE`, `conjCN1`, `CrealJ`, `eqCP`,
    `eqC`, `ImM`, `ImMil`, `ReMil`, `ImMir`, `ReMir`, `ReM`,
    `invC_Crect`, `ImV`, `ReV`, `rectC_mulr`, `rectC_mull`,
    `divC_Crect`, `divC_rect`, `Im_div`, `Re_div`
  + adding resolution of `'Re x \in Num.real` and `'Im x \in Num.real`
    as in `Hint Extern` to `core` database

- in `ssrnum.v`
  + lemmas `gtr_opp`, `mulr_ge0_gt0`, `splitr`, `ler_addgt0Pr`, `ler_addgt0Pl`,
    `lt_le`, `gt_ge`

- in `interval.v`
  + definition `miditv`
  + lemmas `in_segment_addgt0Pr`, `in_segment_addgt0Pl`, `ltBSide`,
    `leBSide`, `lteBSide`, `ltBRight_leBLeft`, `leBRight_ltBLeft`,
    `bnd_simp`, `itv_splitU1`, `itv_split1U`, `mem_miditv`,
    `miditv_le_left`, `miditv_ge_right`, `predC_itvl`, `predC_itvr`,
    `predC_itv`
  + coercion `pair_of_interval`

### Changed

- The following notations are now declared in `type_scope`
  + `{tuple n of T}` and `{bseq n of T}` in `tuple.v`
  + `{subset T}` and `{subset [d] T}` in `order.v`
  + `{morphism D >-> T}` in `morphism.v`
  + `{acts A, on S | to}` and `{acts A, on group G | to}` in `action.v`
  + `{additive U -> V}`, `{rmorphism R -> S}`, `{linear U -> V}`
    `{linear U -> V | s}`, `{scalar U}`, `{lrmorphism A -> B}`
    `{lrmorphism A -> B | s}` in `ssralg.v`
  + `{poly R}` in `poly.v`
  + `{quot I}` and `{ideal_quot I}` in `ring_quotient.v`
  + `{ratio T}` and `{fraction T}` in `fraction.v`

- in `rat.v`
  + `zeroq` and `oneq` (hence `0%Q` and `1%Q`) are now the evaluation
    of terms `fracq (0, 1)` and `fracq (1, 1)` (and not the term
    themselves), the old and new values are convertible and can be
    easily converted with `rewrite -[0%Q]valqK -[1%Q]valqK`

- in `order.v`
  + fix `[distrLatticeType of T with disp]` notation

- in `fintype.v`
  + `enum_ordS` now a notation

- in `gproduct.v`
  + put notations `G ><| H`, `G \* H` and `G \x H` in `group_scope`

- in `ssrnum.v`
  + locked definitions `Re` and `Im`

### Renamed

- in `ssrbool.v`
  + `mono2W_in` to `mono1W_in` (was misnamed)

### Removed

- in `ssrbool.v`
  + notations `{pred T}`, `[rel _ | _]`, `[rel _ in _]`, `xrelpre`
    (now in ssrbool in Coq)
  + definitions `PredType`, `simpl_rel`, `SimplRel`, `relpre`
    (now in ssrbool in Coq)
  + coercion `rel_of_simpl_rel` deprecated for `rel_of_simpl`
    (in ssrbool in Coq)
  + lemmas `simpl_pred_sortE`, `homo_sym`, `mono_sym`, `homo_sym_in`,
    `mono_sym_in`, `homo_sym_in11`, `mono_sym_in11`, `onW_can`, `onW_can_in`,
    `in_onW_can`, `onS_can`, `onS_can_in`, `in_onS_can`, `homoRL_in`,
    `homoLR_in`, `homo_mono_in`, `monoLR_in`, `monoRL_in`, `can_mono_in`,
    `inj_can_sym_in_on`, `inj_can_sym_on`, `inj_can_sym_in`, `contra_not`,
    `contraPnot`, `contraTnot`, `contraNnot`, `contraPT`, `contra_notT`,
    `contra_notN`, `contraPN`, `contraFnot`, `contraPF`, `contra_notF`
    (now in ssrbool in Coq, beware that `simpl_pred_sortE`,
    `contra_not`, `contraPnot`, `contraTnot`, `contraNnot`,
    `contraPT`, `contra_notT`, `contra_notN`, `contraPN`,
    `contraFnot`, `contraPF`, `contra_notF` have different implicit
    arguments and the order of arguments changes in `homoRL_in`,
    `homoLR_in`, `homo_mono_in`, `monoLR_in`, `monoRL_in`,
    `can_mono_in`)

- in `ssreflect.v`
  + structure `NonPropType.call_of`, constructor `Call` and field `callee`
    (now in ssreflect in Coq)
  + definitions `maybeProp`, `call` (now in ssreflect in Coq)
  + structure `NonPropType.test_of`, constructor `Test` and field `condition`
    (now in ssreflect in Coq, beware that implicit arguments of `condition`
    differ)
  + definitions `test_Prop`, `test_negative` (now in ssreflect in Coq)
  + structure `NonPropType.type`, constructor `Check` and fields `result`,
    `test`, `frame` (now in ssreflect in Coq, beware that implicit arguments
    of `Check` differ)
  + definition `check` (now in ssreflect in Coq, beware that implicit
    arguments of `check` differ)
  + notation `[apply]`, `[swap]`, `[dup]` in scope `ssripat_scope`
    (now in ssreflect in Coq)

- in `ssrfun.v`
  + lemmas `Some_inj`, `of_voidK`, `inj_compr` (now in ssrfun in Coq,
    beware that implicit arguments of `inj_compr` differ)
  + notation `void` (now in ssrfun in Coq)
  + definition `of_void` (now in ssrfun in Coq)

- in `bigop.v`
  + notation `big_uncond`
  + notations `mulm_addl`, `mulm_addr`, `filter_index_enum`

- in `ssrnat.v`
  + notations `odd_add`, `odd_sub`, `iter_add`, `maxn_mulr`, `maxn_mull`,
    `minn_mulr`, `minn_mull`, `odd_opp`, `odd_mul`, `odd_exp`, `sqrn_sub`

- in `seq.v`
  + notations `take_addn`, `rot_addn`, `nseq_addn`, `allpairs_catr`,
    `allpairs_consr`, `perm_allpairs_rconsr`, `iota_addl`

- in `fintype.v`
  + notations `arg_minP`, `arg_maxP`, `bump_addl`, `unbump_addl`,
    `disjoint_trans`

- in `perm.v`
  + notations `tuple_perm_eqP`, `pcycle`, `pcycles`, `mem_pcycle`, `pcycle_id`,
    `uniq_traject_pcycle`, `pcycle_traject`, `iter_pcycle`, `eq_pcycle_mem`,
    `pcycle_sym`, `pcycle_perm`, `ncycles_mul_tperm`

- in `classfun.v`
  + notation `cf_triangle_lerif`

- in `action.v`
  + notations `pcycleE`, `pcycle_actperm`

- in `prime.v`
  + notations `primes_mul`, `primes_exp`, `pnat_mul`, `pnat_exp`

- in `path.v`
  + notations `sorted_lt_nth`, `sorted_le_nth`, `ltn_index`, `leq_index`,
    `subseq_order_path`

- in `div.v`
  + notations `coprime_mull`, `coprime_mulr`, `coprime_expl`, `coprime_expr`

- in `vector.v`
  + notation `limg_add`

- in `ssrint.v`
  + notation `polyC_mulrz`

- in `poly.v`
  + notations `polyC_add`, `polyC_opp`, `polyC_sub`, `polyC_muln`, `polyC_mul`,
    `polyC_inv`, `lead_coef_opp`, `derivn_sub`

- in `polydiv.v`
  + notations `rdivp_addl`, `rdivp_addr`, `rmodp_add`, `dvdp_scalel`,
    `dvdp_scaler`, `dvdp_opp`, `coprimep_scalel`, `coprimep_scaler`,
    `coprimep_mull`, `coprimep_mulr`, `modp_scalel`, `modp_scaler`, `modp_opp`,
    `modp_add`, `divp_scalel`, `divp_scaler`, `divp_opp`, `divp_add`,
    `modp_scalel`, `modp_scaler`, `modp_opp`, `modp_add`, `divp_scalel`,
    `divp_scaler`, `divp_opp`, `divp_add`

- in `mxalgebra.v`
  + notations `mulsmx_addl`, `mulsmx_addr`

- in `matrix.v`
  + notations `scalar_mx_comm`, `map_mx_sub`

- in `interval.v`
  + notations `@ 'lersif'`, `lersif`, `x <= y ?< 'if' b`, `subr_lersifr0`,
    `subr_lersif0r`, `subr_lersif0`, `lersif_trans`, `lersif01`, `lersif_anti`,
    `lersifxx`, `lersifNF`, `lersifS`, `lersifT`, `lersifF`, `lersif_oppl`,
    `lersif_oppr`, `lersif_0oppr`, `lersif_oppr0`, `lersif_opp2`, `lersif_oppE`,
    `lersif_add2l`, `lersif_add2r`, `lersif_add2`, `lersif_subl_addr`,
    `lersif_subr_addr`, `lersif_sub_addr`, `lersif_subl_addl`,
    `lersif_subr_addl`, `lersif_sub_addl`, `lersif_andb`, `lersif_orb`,
    `lersif_imply`, `lersifW`, `ltrW_lersif`, `lersif_pmul2l`, `lersif_pmul2r`,
    `lersif_nmul2l`, `lersif_nmul2r`, `real_lersifN`, `real_lersif_norml`,
    `real_lersif_normr`, `lersif_nnormr`, `lersifN`, `lersif_norml`,
    `lersif_normr`, `lersif_distl`, `lersif_minr`, `lersif_minl`, `lersif_maxr`,
    `lersif_maxl`, `lersif_pdivl_mulr`, `lersif_pdivr_mulr`,
    `lersif_pdivl_mull`, `lersif_pdivr_mull`, `lersif_ndivl_mulr`,
    `lersif_ndivr_mulr`, `lersif_ndivl_mull`, `lersif_ndivr_mull`,
    `lersif_in_itv`, `itv_gte`, `ltr_in_itv`, `ler_in_itv`, `itv_splitU2`,
    `@ 'itv_intersection'`, `itv_intersection`, `@ 'itv_intersection1i'`,
    `itv_intersection1i`, `@ 'itv_intersectioni1'`, `itv_intersectioni1`,
    `@ 'itv_intersectionii'`, `itv_intersectionii`, `@ 'itv_intersectionC'`,
    `itv_intersectionC`, `@ 'itv_intersectionA'`, `itv_intersectionA`

- in `intdiv.v`
  + notations `coprimez_mull`, `coprimez_mulr`, `coprimez_expl`, `coprimez_expr`

### Infrastructure

- in `builddoc_lib.sh`:
  + change the sed command that removes all starred lines

### Misc

- fix warning `deprecated-hint-without-locality` by adding the `#[global]`
  attribute to most hints
- turn warning `deprecated-hint-without-locality` into an error

## [1.14.0] - 2022-01-19

This release is compatible with Coq versions 8.11, 8.12, 8.13, 8.14, and 8.15.


The contributors to this version are:
Cyril Cohen, Erik Martin-Dorel, Kazuhiko Sakaguchi, Laurent Théry, Pierre Roux

### Added

- in `seq.v`, added theorem `pairwise_trans`,

- in `prime.v` 
  + theorems `trunc_log0`, `trunc_log1`, `trunc_log_eq0`,
    `trunc_log_gt0`, `trunc_log0n`, `trunc_log1n`, `leq_trunc_log`,
    `trunc_log_eq`, `trunc_lognn`, `trunc_expnK`,  `trunc_logMp`,
    `trunc_log2_double`, `trunc_log2S`
  + definition `up_log` 
  + theorems `up_log0`, `up_log1`, `up_log_eq0`, `up_log_gt0`, 
    `up_log_bounds` , `up_logP`, `up_log_gtn`, `up_log_min`,
    `leq_up_log`, `up_log_eq`, `up_lognn`, `up_expnK`, `up_logMp`,
    `up_log2_double`, `up_log2S`, `up_log_trunc_log`, `trunc_log_up_log`
     
### Changed

- in `prime.v` 
  + definition `trunc_log` now it is 0 when p <= 1 

- in `ssrnum.v`
  + generalized lemma `rootCV` so that the degree is not necessarily positive.

## [1.13.0] - 2021-10-28

This release is compatible with Coq versions 8.11, 8.12, 8.13, and 8.14.

The contributors to this version are:
Amel Kebbouche, Anders Mörtberg, Anton Trunov, Christian Doczkal,
Cyril Cohen, Emilio Jesus Gallego Arias, Enrico Tassi, Erik
Martin-Dorel, Evgenii Moiseenko, Florent Hivert, Gaëtan Gilbert,
Kazuhiko Sakaguchi, Laurent Théry, Maxime Dénès, Pierre Jouvelot,
Pierre Roux, Reynald Affeldt, Yves Bertot

### Added

- Added intro pattern ltac views for rewrite:
  `/[1! rules]`, `/[! rules]`.

- in `ssrbool.v`, added lemmas `negPP`, `andPP`, `orPP`, and `implyPP`.

- In `ssrnat.v`: new lemmas `fact_geq`, `leq_pfact`, `leq_fact`,
  `ltn_pfact`, `uphalf_leq`, `uphalf_gt0`.

- in `seq.v`,
  + new higher-order predicate `pairwise r xs` which asserts that the relation
    `r` holds for any i-th and j-th element of `xs` such that i < j.
  + new lemmas `allrel_mask(l|r)`, `allrel_filter(l|r)`, `sub(_in)_allrel`,
    `pairwise_cons`, `pairwise_cat`, `pairwise_rcons`, `pairwise2`,
    `pairwise_mask`, `pairwise_filter`, `pairwiseP`, `pairwise_all2rel`,
    `sub(_in)_pairwise`, `eq(_in)_pairwise`, `pairwise_map`, `subseq_pairwise`,
    `uniq_pairwise`, `pairwise_uniq`, and `pairwise_eq`.
  + new lemmas `zip_map`, `eqseq_all`, and `eq_map_all`.
  + new lemmas `count_undup`, `eq_count_undup`, `rev_take`,
    `rev_drop`, `takeEmask`, `dropEmask`, `filter_iota_ltn`,
    `filter_iota_leq`, `map_nth_iota0` and `map_nth_iota`
  + new lemmas `cat_nilp`, `rev_nilp`, `allrelT`, `allrel_relI`, and
    `pairwise_relI`.
  + new lemma `undup_map_inj`.
  + new lemmas: `forall_cons`, `exists_cons`, `sub_map`, `eq_mem_map`,
    `eq_in_pmap`.

- in `path.v`,
  + new lemmas: `sorted_pairwise(_in)`, `path_pairwise(_in)`,
    `cycle_all2rel(_in)`, `pairwise_sort`, and `sort_pairwise_stable`.
  + new lemmas `cat_sorted2`, `path_le`, `take_path`, `take_sorted`,
    `drop_sorted`, `undup_path`, `undup_sorted`, `count_merge`,
    `eq_count_merge`
  + new lemmas: `pairwise_sorted`, `path_relI`, `cycle_relI`,
    `sorted_relI`, `eq(_in)_sorted`, `mergeA`, `all_merge`, and
    `homo_sort_map(_in)`.

- in `fintype.v`, new lemma `bij_eq_card`.

- in `fingraph.v`, new lemmas: `connect_rev`, `sym_connect_sym`

- in `finset.v`,
  + new lemmas: `bigcup0P`, `bigcup_disjointP`, `imset_cover`,
    `cover1`, `trivIset1`, `trivIsetD`, `trivIsetU`, `coverD1`,
    `partition0`, `partiton_neq0`, `partition_trivIset`, `partitionS`,
    `partitionD1`, `partitionU1`, `partition_set0`,
    `partition_pigeonhole`, `indexed_partition`, `imset_inj`,
    `imset_disjoint`, `imset_trivIset`, `imset0mem`,
    `imset_partition`.
  + generalized `eq_preimset`, `eq_imset`, `eq_in_imset`, `eq_in_imset2` to
    predicates (not only {set T}).

- in `tuple.v`, added type of bounded sequences `n.-bseq T` and its
  theory, i.e.
  + definition `bseq` with constructor `Bseq`,
  + notation `n.-bseq`, `{bseq n of T}`, `[bseq of s]`, `[bseq x1 ;
    .. ; xn]`, and `[bseq]`, coercions to `n.-tuple` and to `seq` (which commute
    definitionally), definitions `insub_bseq`, `in_bseq`, `cast_bseq`,
    `widen_bseq`,  `bseq_tagged_tuple` and `tagged_tuple_bseq` (the
    later two are mutual inverses).
  + canonical instances making `n.-bseq` canonically an `eqType`, a
    `predType`, a `choiceType`, a `countType`, a `subCountType`, a
    `finType`, a `subFinType`; and making `nil`, `cons`, `rcons`,
    `behead`, `belast`, `cat`, `take`, `drop`, `rev`, `rot`, `rotr`, `map`,
    `scanl`, `pairmap`, `allpairs`, and `sort` canonical `_.-bseq`.
  + lemmas `size_bseq`, `bseqE`, `size_insub_bseq`, `cast_bseq_id`,
    `cast_bseqK`, `cast_bseqKV`, `cast_bseq_trans`, `size_cast_bseq`,
    `widen_bseq_id`, `cast_bseqEwiden`, `widen_bseqK`,
    `widen_bseq_trans`, `size_widen_bseq`, `in_bseqE`,
    `widen_bseq_in_bseq`, `bseq0`, `membsE`, `bseq_tagged_tupleK`,
    `tagged_tuple_bseqK`,`bseq_tagged_tuple_bij`, and
    `tagged_tuple_bseq_bij`.
  + added Canonical tuple for sort.
  + new lemma `val_tcast`

- in `bigop.v`,
  + generalized lemma `partition_big`.
  + new lemmas `big_pmap`, `sumnB`, `card_bseq`, `big_nat_widenl`,
  `big_geq_mkord`, `big_bool`, `big_rev_mkord`, `big_nat_mul`

- in `interval.v`, new lemmas: `ge_pinfty`, `le_ninfty`, `gt_pinfty`, `lt_ninfty`.

- in `order.v`
  + we provide a canonical total order on ordinals and lemmas
    `leEord`, `ltEord`, `botEord`, and `topEord` to translate generic
    symbols to the concrete ones. Because of a shortcoming of the
    current interface, which requires `finOrderType` structures to be
    nonempty, the `finOrderType` is only defined for ordinal which are
    manifestly nonempty (i.e. `'I_n.+1`).
  + we provide a canonical finite complemented distributive lattice structure
    on finite set ({set T}) ordered by inclusion and lemmas
    `leEsubset`, `meetEsubset`, `joinEsubset`, `botEsubset`, `topEsubset`
    `subEsubset`, `complEsubset` to translate generic symbols to the
    concrete ones.
  + new notation `Order.enum A` for `sort <=%O (enum A)`, with new
    lemmas in module `Order`: `cardE`, `mem_enum`, `enum_uniq`,
    `cardT`, `enumT`, `enum0`, `enum1`, `eq_enum`, `eq_cardT`,
    `set_enum`, `enum_set0`, `enum_setT`, `enum_set1`, `enum_ord`,
    `val_enum_ord`, `size_enum_ord`, `nth_enum_ord`, `nth_ord_enum`,
    `index_enum_ord`, `mono_sorted_enum`, and `mono_unique`.
  + a new module `Order.EnumVal` (which can be imported locally), with
    definitions `enum_rank_in`, `enum_rank`, `enum_val` on a finite
    partially ordered type `T`, which are the same as the one from
    `fintype.v`, except they are monotonous when `Order.le T` is
    total. We provide the following lemmas: `enum_valP`,
    `enum_val_nth`, `nth_enum_rank_in`, `nth_enum_rank`,
    `enum_rankK_in`, `enum_rankK`, `enum_valK_in`, `enum_valK`,
    `enum_rank_inj`, `enum_val_inj`, `enum_val_bij_in`,
    `eq_enum_rank_in`, `enum_rank_in_inj`, `enum_rank_bij`,
    `enum_val_bij`, `le_enum_val`, `le_enum_rank_in`, and
    `le_enum_rank`.  They are all accessible via module `Order` if one
    chooses not to import `Order.EnumVal`.
  + a new module `tagnat` which provides a monotonous bijection
    between the finite ordered types `{i : 'I_n & 'I_(p_ i)}`
    (canonically ordered lexicographically), and `'I_(\sum_i p_ i)`,
    via the functions `sig` and `rank`. We provide direct access to
    the components of the former type via the functions `sig1`, `sig2`
    and `Rank`. We provide the following lemmas on these definitions:
    `card`, `sigK`, `sig_inj`, `rankK`, `rank_inj`, `sigE12`,
    `rankE`, `sig2K`, `Rank1K`, `Rank2K`, `rank_bij`, `sig_bij `,
    `rank_bij_on`, `sig_bij_on`, `le_sig`, `le_sig1`, `le_rank`,
    `le_Rank`, `lt_sig`, `lt_rank`, `lt_Rank`, `eq_Rank`, `rankEsum`,
    `RankEsum`, `rect`, and `eqRank`.
  + lemmas `joins_le` and `meets_ge`.
  + new lemmas `le_sorted_ltn_nth`, `le_sorted_leq_nth`,
    `lt_sorted_leq_nth`, `lt_sorted_ltn_nth`, `filter_lt_nth`,
    `count_lt_nth`, `filter_le_nth`, `count_le_nth`,
    `count_lt_le_mem`, `sorted_filter_lt`, `sorted_filter_le`,
    `nth_count_le`, `nth_count_lt`, `count_le_gt`,
    `count_lt_ge`, `sorted_filter_gt`, `sorted_filter_ge`,
    `nth_count_ge`, `nth_count_lt` and `nth_count_eq`
  + new lemmas `(le|lt)_path_min`, `(le|lt)_path_sortedE`,
    `(le|lt)_(path|sorted)_pairwise`, `(le|lt)_(path|sorted)_(mask|filter)`,
    `subseq_(le|lt)_(path|sorted)`, `lt_sorted_uniq`, `sort_lt_id`,
    `perm_sort_leP`, `filter_sort_le`, `(sorted_)(mask|subseq)_sort_le`,
    `mem2_sort_le`.
  + a new mixin `meetJoinLeMixin` constructing a `latticeType` from `meet`,
    `join` and proofs that those are respectvely the greatest lower bound and
    the least upper bound.

- in `matrix.v`,
  + seven new definitions: `mxblock`, `mxcol`, `mxrow` and `mxdiag` with
    notations `\mxblock_(i < m, j < n) B_ i j`, `\mxcol_(i < m) B_ i`,
    `\mxrow_(j < n) B_ j`, and `\mxdiag_(i < n) B_ i` (and variants
    without explicit `< n`), to form big matrices described by blocks.
  + `submxblock`, `submxcol` and `submxrow` to extract blocks from the
    former constructions. There is no analogous for `mxdiag` because
    one can simply apply `submxblock A i i`.
  + We provide the following lemmas on these definitions:
    `mxblockEh`, `mxblockEv`, `submxblockEh`, `submxblockEv`,
    `mxblockK`, `mxrowK`, `mxcolK`, `submxrow_matrix`,
    `submxcol_matrix`, `submxblockK`, `submxrowK`, `submxcolK`,
    `mxblockP`, `mxrowP`, `mxcolP`, `eq_mxblockP`, `eq_mxblock`,
    `eq_mxrowP`, `eq_mxrow`, `eq_mxcolP`, `eq_mxcol`, `row_mxrow`,
    `col_mxrow`, `row_mxcol`, `col_mxcol`, `row_mxblock`,
    `col_mxblock`, `tr_mxblock`, `tr_mxrow`, `tr_mxcol`,
    `tr_submxblock`, `tr_submxrow`, `tr_submxcol`, `mxsize_recl`,
    `mxrow_recl`, `mxcol_recu`, `mxblock_recl`, `mxblock_recu`,
    `mxblock_recul`, `mxrowEblock`, `mxcolEblock`, `mxEmxrow`,
    `mxEmxcol`, `mxEmxblock`, `mxrowD`, `mxrowN`, `mxrowB`, `mxrow0`,
    `mxrow_const`, `mxrow_sum`, `submxrowD`, `submxrowN`, `submxrowB`,
    `submxrow0`, `submxrow_sum`, `mul_mxrow`, `mul_submxrow`,
    `mxcolD`, `mxcolN`, `mxcolB`, `mxcol0`, `mxcol_const`,
    `mxcol_sum`, `submxcolD`, `submxcolN`, `submxcolB`, `submxcol0`,
    `submxcol_sum`, `mxcol_mul`, `submxcol_mul`, `mxblockD`,
    `mxblockN`, `mxblockB`, `mxblock0`, `mxblock_const`,
    `mxblock_sum`, `submxblockD`, `submxblockN`, `submxblockB`,
    `submxblock0`, `submxblock_sum`, `mul_mxrow_mxcol`,
    `mul_mxcol_mxrow`, `mul_mxrow_mxblock`, `mul_mxblock_mxrow`,
    `mul_mxblock`, `is_trig_mxblockP`, `is_trig_mxblock`,
    `is_diag_mxblockP`, `is_diag_mxblock`, `submxblock_diag`,
    `eq_mxdiagP`, `eq_mxdiag`, `mxdiagD`, `mxdiagN`, `mxdiagB`,
    `mxdiag0`, `mxdiag_sum`, `tr_mxdiag`, `row_mxdiag`, `col_mxdiag`,
    `mxdiag_recl`, `mxtrace_mxblock`, `mxdiagZ`, `diag_mxrow`,
    `mxtrace_mxdiag`, `mul_mxdiag_mxcol`, `mul_mxrow_mxdiag`,
    `mul_mxblock_mxdiag`, and `mul_mxdiag_mxblock`.
   + adding missing lemmas `trmx_conform` and `eq_castmx`.
   + new lemmas: `row_thin_mx`, `col_flat_mx`, `col1`, `colE`,
    `mulmx_lsub`, `mulmx_rsub`, `mul_usub_mx`, `mul_dsub_mx`,
    `exp_block_diag_mx`, `block_diag_mx_unit`, `invmx_block_diag`

- in `mxalgegra.v`,
  + Lemmas about rank of block matrices with `0`s inside
    `rank_col_mx0`, `rank_col_0mx`, `rank_row_mx0`, `rank_row_0mx`,
    `rank_diag_block_mx`, and `rank_mxdiag`.
  + we provide an equality of spaces `eqmx_col` between `\mxcol_i V_i`
    and the sum of spaces `\sum_i <<V_ i>>)%MS`.

- In `mxpoly.v`
  + developed the theory of diagonalization. To that
    effect, we define `conjmx`, `restrictmx`, and notations `A ~_P B`,
    `A ~_P {in S'}`, `A ~_{in S} B`, `A ~_{in S} {in S'}`,
    `all_simmx_in`, `diagonalizable_for`, `diagonalizable_in`,
    `diagonalizable`, `codiagonalizable_in`, and `codiagonalizable`; and
    their theory: `stablemx_comp`, `stablemx_restrict`, `conjmxM`,
    `conjMmx`, `conjuMmx`, `conjMumx`, `conjuMumx`, `conjmx_scalar`,
    `conj0mx`, `conjmx0`, `conjumx`, `conj1mx`, `conjVmx`, `conjmxK`,
    `conjmxVK`, `horner_mx_conj`, `horner_mx_uconj`, `horner_mx_uconjC`,
    `mxminpoly_conj`, `mxminpoly_uconj`, `sub_kermxpoly_conjmx`,
    `sub_eigenspace_conjmx`, `eigenpoly_conjmx`, `eigenvalue_conjmx`,
    `conjmx_eigenvalue`, `simmxPp`, `simmxW`, `simmxP`, `simmxRL`,
    `simmxLR`, `simmx_minpoly`, `diagonalizable_for_row_base`,
    `diagonalizable_forPp`, `diagonalizable_forP`,
    `diagonalizable_forPex`, `diagonalizable_forLR`,
    `diagonalizable_for_mxminpoly`, `diagonalizable_for_sum`,
    `codiagonalizable1`, `codiagonalizable_on`, `diagonalizable_diag`,
    `diagonalizable_scalar`, `diagonalizable0`, `diagonalizablePeigen`,
    `diagonalizableP`, `diagonalizable_conj_diag`, and
    `codiagonalizableP`.
  + new lemmas `row'_col'_char_poly_mx` and `char_block_diag_mx` 

- In `ssralg.v`
  + new lemma `fmorph_eq`
  + Canonical additive, linear and rmorphism for `fst` and `snd`
  + multi-rules `linearE`, `rmorphE`, and `raddfE`, for easier automatic
    reasoning with linear functions, morphisms, and additive functions.
  + new lemma `eqr_div`
  + new lemmas `lregMl` and `rregMr`

- In `ssrnum.v`:
  + new lemmas `ltr_distlC`, `ler_distlC`, new definition `lter_distlC`
  + new lemmas `sqrtrV`, `eqNr`

- in `ssrint.v`, new lemmas `mulr_absz`, `natr_absz`, `lez_abs`

- In `intdiv.v`
  + new definition `lcmz`
  + new lemmas `dvdz_lcmr`, `dvdz_lcml`, `dvdz_lcm`, `lcmzC`, `lcm0z`,
    `lcmz0`, `lcmz_ge0`, `lcmz_neq0`
  + new lemma `lez_pdiv2r`

- in `polydiv.v`, new lemma `coprimep_XsubC2`

- in `poly.v`, new lemmas `monic_lreg` and `monic_rreg`

- In `rat.v`
  + new lemmas `minr_rat`, `maxr_rat`
  + constants `fracq`, `oppq`, `addq`, `mulq`, `invq`, `normq`,
    `le_rat`, and `lt_rat` are "locked" when applied to variables,
    computation occurs only when applied to constructors. Moreover the
    new definition of `fracq` ensures that if `x` and `y` of type
    `int * int` represent the same rational then `fracq x` is
    definitionally equal to `fracq y` (i.e. the underlying proofs are
    the same). Additionally, `addq` and `mulq` are tuned to minimize
    the number of integer arithmetic operations when the denominators
    are equal to one.
  + notation `[rat x // y]` for displaying the normal form of a
    rational. We also provide the parsable notation for debugging
    purposes.

- In `binomial.v`: new lemma `fact_split`

- In `interval.v`: new lemmas `subset_itv`, `subset_itv_oo_cc`,
  `subset_itv_oo_oc`, `subset_itv_oo_co`, `subset_itv_oc_cc`,
  `subset_itv_co_cc`, `itvxx`, `itvxxP`

- In `perm.v`: new lemma `perm_onV`, `porbitV`, `porbitsV`

### Changed

- In `ssrnum.v`, lemma `normr_nneg`, declared a `Hint Resolve` in the
  `core` database

- In `ssralg.v` and `ssrint.v`, the nullary ring notations `-%R`, `+%R`, `*%R`,
  `*:%R`, and `*~%R` are now declared in `fun_scope`.

- across the library, the deprecation mechanism to use has been changed from the
  `deprecate` notation to the `deprecated` attribute (cf. Removed section).

- in `finalg.v`, `finFieldType` now inherits from `countDecFieldType`.

- `fact_smonotone` moved from `binomial.v` to `ssrnat.v` and renamed to `ltn_fact`.

- in `presentation.v` fixes the doc wrongly describing the meaning of
  `G \isog Grp( ... )`

### Renamed

- in `path.v`,
  + `sub_(path|cycle|sorted)_in` -> `sub_in_(path|cycle|sorted)`
  + `eq_(path|cycle)_in` -> `eq_in_(path|cycle)`

- in `order.v`
  + `join_(|sup_|min_)seq` -> `joins_(|sup_|min_)seq`
  + `meet_(|sup_|min_)seq` -> `meets_(|sup_|min_)seq`
  + `join_(sup|min)` -> `joins_(sup|min)`

- in `matrix.v`, `card_matrix` -> `card_mx`

- in `ssralg.v`, `prodr_natmul` ->  `prodrMn`

- in `bigop.v`, `big_uncond` -> ` big_rmcond`

- in `finset`
  + `mem_imset_eq`  -> `mem_imset`
  + `mem_imset2_eq` -> `mem_imset2`

### Removed

- in `ssreflect.v`, the `deprecate` notation has been deprecated. Use the
  `deprecated` attribute instead (cf. Changed section).

- in `seq.v`, `iota_add` has been deprecated. Use `iotaD` instead.

- in `ssrnat.v` and `ssrnum.v`, deprecation aliases and the `mc_1_10`
  compatibility modules introduced in MathComp 1.11+beta1 have been removed.

- in `seq.v`, remove the following deprecation aliases introduced in MathComp
  1.9.0: `perm_eq_rev`, `perm_eq_flatten`, `perm_eq_all`, `perm_eq_small`,
  `perm_eq_nilP`, `perm_eq_consP`, `leq_size_perm`, `uniq_perm_eq`,
  `perm_eq_iotaP`, and `perm_undup_count`.

- in `path.v`, remove the deprecation aliases `eq(_in)_sorted` introduced in
  MathComp 1.12.0. These names of lemmas are now taken by new lemmas
  (cf. Added section).

- in `order.v`, remove the deprecation aliases `eq_sorted_(le|lt)`.

### Infrastructure

- The way `hierarchy.ml` recognizes inheritance has been changed: `S1` inherits
  from `S2` when there is a coercion path from `S1.sort` to `S2.sort` and there
  is a canonical structure instance that unifies `S1.sort` and `S2.sort`,
  regardless of where (which module) these constants are declared.
  As a result, it recognizes non-forgetful inheritance and checks the uniqueness
  of join and exhaustiveness of canonical declarations involving it.


## [1.12.0] - 2020-11-26

This release is compatible with Coq versions 8.10, 8.11, and 8.12.

The contributors to this version are:
Anton Trunov, Christian Doczkal, Cyril Cohen, Enrico Tassi, Erik Martin-Dorel,
Jasper Hugunin, Kazuhiko Sakaguchi, Laurent Théry, Reynald Affeldt, and Yves Bertot.

### Added

- Contraposition lemmas involving propositions:
  + in `ssrbool.v`: `contra_not`, `contraPnot`, `contraTnot`,
    `contraNnot`, `contraPT`, `contra_notT`, `contra_notN`,
    `contraPN`, `contraFnot`, `contraPF` and `contra_notF`.
  + in `eqtype.v`: `contraPeq`, `contra_not_eq`, `contraPneq`, and
    `contra_neq_not`, `contra_not_neq`, `contra_eq_not`.
- Contraposition lemmas involving inequalities:
  + in `ssrnat.v`: `contraTleq`, `contraTltn`, `contraNleq`,
    `contraNltn`, `contraFleq`, `contraFltn`, `contra_leqT`,
    `contra_ltnT`, `contra_leqN`, `contra_ltnN`, `contra_leqF`,
    `contra_ltnF`, `contra_leq`, `contra_ltn`, `contra_leq_ltn`,
    `contra_ltn_leq`, `contraPleq`, `contraPltn`, `contra_not_leq`,
    `contra_not_ltn`, `contra_leq_not`, `contra_ltn_not`
  + in `order.v`: `comparable_contraTle`, `comparable_contraTlt`,
    `comparable_contraNle`, `comparable_contraNlt`,
    `comparable_contraFle`, `comparable_contraFlt`, `contra_leT`,
    `contra_ltT`, `contra_leN`, `contra_ltN`, `contra_leF`,
    `contra_ltF`, `comparable_contra_leq_le`,
    `comparable_contra_leq_lt`, `comparable_contra_ltn_le`,
    `comparable_contra_ltn_lt`, `contra_le_leq`, `contra_le_ltn`,
    `contra_lt_leq`, `contra_lt_ltn`, `comparable_contra_le`,
    `comparable_contra_le_lt`, `comparable_contra_lt_le`,
    `comparable_contra_lt`, `contraTle`, `contraTlt`, `contraNle`,
    `contraNlt`, `contraFle`, `contraFlt`, `contra_leq_le`,
    `contra_leq_lt`, `contra_ltn_le`, `contra_ltn_lt`, `contra_le`,
    `contra_le_lt`, `contra_lt_le`, `contra_lt`, `contra_le_not`,
    `contra_lt_not`, `comparable_contraPle`, `comparable_contraPlt`,
    `comparable_contra_not_le`, `comparable_contra_not_lt`,
    `contraPle`, `contraPlt`, `contra_not_le`, `contra_not_lt`

- in `ssreflect.v`, added intro pattern ltac views for dup, swap,
  apply: `/[apply]`, `/[swap]` and `/[dup]`.

- in `ssrbool.v` (waiting to be integrated in Coq)
  + generic lemmas about interaction between `{in _, _}` and `{on _,  _}`:
    `in_on1P`, `in_on1lP`, `in_on2P`, `on1W_in`, `on1lW_in`, `on2W_in`,
    `in_on1W`, `in_on1lW`, `in_on2W`, `on1S`, `on1lS`, `on2S`,
    `on1S_in`, `on1lS_in`, `on2S_in`, `in_on1S`, `in_on1lS`, `in_on2S`.
  + lemmas about interaction between `{in _, _}` and `sig`:
    `in1_sig`, `in2_sig`, and `in3_sig`.

- in `ssrnat.v`, new lemmas: `subn_minl`, `subn_maxl`, `oddS`,
  `subnA`, `addnBn`, `addnCAC`, `addnACl`, `iterM`, `iterX`

- in `seq.v`,
  + new lemmas `take_uniq`, `drop_uniq`
  + new lemma `mkseqP` to abstract a sequence `s` with `mkseq f n`,
    where `f` and `n` are fresh variables.
  + new high-order relation `allrel r xs ys` which asserts that
    `r x y` holds whenever `x` is in `xs` and `y` is in `ys`, new notation
    `all2rel r xs (:= allrel r xs xs)` which asserts that `r` holds on all
    pairs of elements of `xs`, and
    * lemmas `allrel0(l|r)`, `allrel_cons(l|r|2)`, `allrel1(l|r)`,
      `allrel_cat(l|r)`, `allrel_allpairsE`, `eq_in_allrel`, `eq_allrel`,
      `allrelC`, `allrel_map(l|r)`, `allrelP`,
    * new lemmas `all2rel1`, `all2rel2`, and `all2rel_cons`
      under assumptions of symmetry of `r`.
  + new lemmas `allss`, `all_mask`, and `all_sigP`.
    `allss` has also been declared as a hint.
  + new lemmas `index_pivot`, `take_pivot`, `rev_pivot`,
    `eqseq_pivot2l`, `eqseq_pivot2r`, `eqseq_pivotl`, `eqseq_pivotr`
    `uniq_eqseq_pivotl`, `uniq_eqseq_pivotr`, `mask_rcons`, `rev_mask`,
    `subseq_rev`, `subseq_cat2l`, `subseq_cat2r`, `subseq_rot`, and
    `uniq_subseq_pivot`.
  + new lemmas `find_ltn`, `has_take`, `has_take_leq`,
    `index_ltn`, `in_take`, `in_take_leq`, `split_find_nth`,
    `split_find` and `nth_rcons_cat_find`.
  + added `drop_index`, `in_mask`, `mask0s`, `cons_subseq`,
    `undup_subseq`, `leq_count_mask`, `leq_count_subseq`,
    `count_maskP`, `count_subseqP`, `count_rem`, `count_mem_rem`,
    `rem_cons`, `remE`, `subseq_rem`, `leq_uniq_countP`, and
    `leq_uniq_count`.
  + new definition `rot_add` and new lemmas `rot_minn`,
    `leq_rot_add`, `rot_addC`, `rot_rot_add`.
  + new lemmas `perm_catACA`, `allpairs0l`, `allpairs0r`,
    `allpairs1l`, `allpairs1r`, `allpairs_cons`, `eq_allpairsr`,
    `allpairs_rcons`, `perm_allpairs_catr`, `perm_allpairs_consr`,
    `mem_allpairs_rconsr`, and `allpairs_rconsr` (with the alias
    `perm_allpairs_rconsr` for the sake of uniformity, but which is
    already deprecated in favor of `allpairs_rconsr`, cf renamed
    section).

- in `path.v`,
  + new lemmas `sub_cycle(_in)`, `eq_cycle_in`,
    `(path|sorted)_(mask|filter)_in`, `rev_cycle`, `cycle_map`,
    `(homo|mono)_cycle(_in)`.
  + new lemma `sort_iota_stable`.
  + new lemmas `order_path_min_in`, `path_sorted_inE`,
    `sorted_(leq|ltn)_nth_in`, `subseq_path_in`, `subseq_sorted_in`,
    `sorted_(leq|ltn)_index_in`, `sorted_uniq_in`, `sorted_eq_in`,
    `irr_sorted_eq_in`, `sort_sorted_in`, `sorted_sort_in`, `perm_sort_inP`,
    `all_sort`, `sort_stable_in`, `filter_sort_in`, `(sorted_)mask_sort_in`,
    `(sorted_)subseq_sort_in`, and `mem2_sort_in`.
  + added `size_merge_sort_push`, which documents an
    invariant of `merge_sort_push`.

- in `fintype.v`,
  + new lemmas `card_geqP`, `card_gt1P`, `card_gt2P`, `card_le1_eqP`
    (generalizes `fintype_le1P`),
  + adds lemma `split_ordP`, a variant of `splitP` which introduces
    ordinal equalities between the index and `lshift`/`rshift`, rather
    than equalities in `nat`, which in some proofs makes the reasoning
    easier (cf `matrix.v`), especially together with the new lemma
    `eq_shift` (which is a multi-rule for new lemmas `eq_lshift`,
    `eq_rshift`, `eq_lrshift` and `eq_rlshift`).
  + new lemmas `eq_liftF` and `lift_eqF`.
  + new lemmas `disjointFr`, `disjointFl`, `disjointWr`, `disjointW`
  + new (pigeonhole) lemmas `leq_card_in`, `leq_card`,
  + added `mask_enum_ord`.

- in `finset.v`
  + new lemmas `set_enum`, `cards_eqP`, `cards2P`
  + new lemmas `properC`, `properCr`, `properCl`
  + new lemmas `mem_imset_eq`, `mem_imset2_eq`. These lemmas will
    lose the `_eq` suffix in the next release, when the shortende
    names will become available (cf. Renamed section)
  + new lemma `disjoints1`

- in `order.v`
  + new lemmas `comparable_bigl` and `comparable_bigr`.
  + added a factory `distrLatticePOrderMixin` to build a
    `distrLatticeType` from a `porderType`.
  + new notations `0^d` and `1^d` for bottom and top elements of dual
    lattices.
  + new definition `lteif` and notations `<?<=%O`, `<?<=^d%O`, `_ < _ ?<= if _`,
    and `_ <^d _ ?<= if _` (cf Changed section).
  + new lemmas `lteifN`, `comparable_lteifNE`, and
    `comparable_lteif_(min|max)(l|r)`.

- in `bigop.v`,
  + new lemma `sig_big_dep`, analogous to `pair_big_dep`
    but with an additional dependency in the index types `I` and `J`.
  + new lemma `reindex_omap` generalizes `reindex_onto`
    to the case where the inverse function to `h` is partial (i.e. with
    codomain `option J`, to cope with a potentially empty `J`.
  + new lemma `bigD1_ord` takes out an element in the
    middle of a `\big_(i < n)` and reindexes the remainder using `lift`.
  + new lemma `big_uncond`. The ideal name is `big_rmcond`
    but it has just been deprecated from its previous meaning (see
    Changed section) so as to reuse it in next mathcomp release.
  + new lemma `big_uncond_in` is a new alias of
    `big_rmcond_in` for the sake of uniformity, but it is already
    deprecated and will be removed two releases from now.
  + added `big_mask_tuple` and `big_mask`.

- in `fingraph.v`, new lemmas `fcard_gt0P`, `fcard_gt1P`

- in `perm.v`, new lemma `permS01`.

- in `ssralg.v`
  + new lemmas `sumr_const_nat` and `iter_addr_0`
  + new lemmas `iter_addr`, `iter_mulr`, `iter_mulr_1`, and
    `prodr_const_nat`.
  + new lemma `raddf_inj`, characterizing injectivity for additive
    maps.
  + Lemma `expr_sum` : equivalent for ring of `expn_sum`
  + Lemma `prodr_natmul` : generalization of `prodrMn_const`. Its name
    will become `prodrMn` in the next release when this name will
    become available (cf. Renamed section).

- in `poly.v`, new lemma `commr_horner`.

- in `polydiv.v`, new lemma `dvdpNl`.

- in `matrix.v`,
  + new definitions `is_diag_mx` and `is_trig_mx` characterizing
    respectively diagonal and lower triangular matrices.  We provide
    the new lemmas `row_diag_mx`, `is_diag_mxP`, `diag_mxP`,
    `diag_mx_is_diag`, `mx0_is_diag`, `is_trig_mxP`,
    `is_diag_mx_is_trig`, `diag_mx_trig`, `mx0_is_trig`,
    `scalar_mx_is_diag`, `is_scalar_mx_is_diag`, `scalar_mx_is_trig`
    and `is_scalar_mx_is_trig`.
  + new lemmas `matrix_eq0`, `matrix0Pn`, `rV0Pn` and `cV0Pn` to
    characterize nonzero matrices and find a nonzero coefficient.
  + new predicate `mxOver S` qualified with `\is a`, and
    * new lemmas `mxOverP`, `mxOverS`, `mxOver_const`,
      `mxOver_constE`, `thinmxOver`, `flatmxOver`, `mxOver_scalar`,
      `mxOver_scalarE`, `mxOverZ`, `mxOverM`, `mxOver_diag`,
      `mxOver_diagE`.
    * new canonical structures:
      - `mxOver S` is closed under addition if `S` is.
      - `mxOver S` is closed under negation if `S` is.
      - `mxOver S` is a sub Z-module if `S` is.
      - `mxOver S` is a semiring for square matrices if `S` is.
      - `mxOver S` is a subring for square matrices if `S` is.
  + new lemmas about `map_mx`: `map_mx_id`, `map_mx_comp`,
    `eq_in_map_mx`, `eq_map_mx` and `map_mx_id_in`.
  + new lemmas `row_usubmx`, `row_dsubmx`, `col_lsubmx`, and
    `col_rsubmx`.
  + new lemma `mul_rVP`.
  + new inductions lemmas: `row_ind`, `col_ind`, `mx_ind`, `sqmx_ind`,
    `ringmx_ind`, `trigmx_ind`, `trigsqmx_ind`, `diagmx_ind`,
    `diagsqmx_ind`.
  + added missing lemma `trmx_eq0`, `det_mx11`.
  + new lemmas about diagonal and triangular matrices: `mx11_is_diag`,
    `mx11_is_trig`, `diag_mx_row`, `is_diag_mxEtrig`, `is_diag_trmx`,
    `ursubmx_trig`, `dlsubmx_diag`, `ulsubmx_trig`, `drsubmx_trig`,
    `ulsubmx_diag`, `drsubmx_diag`, `is_trig_block_mx`,
    `is_diag_block_mx`, and `det_trig`.
  + new definition `mxsub`, `rowsub` and `colsub`,
    corresponding to arbitrary submatrices/reindexation of a matrix.
    * we provide the theorems `x?(row|col)(_perm|')?Esub`, `t?permEsub`
      `[lrud]submxEsub`, `(ul|ur|dl|dr)submxEsub` for compatibility with
      ad-hoc submatrices/permutations.
    * we provide a new, configurable, induction lemma `mxsub_ind`.
    * we provide the basic theory `mxsub_id`, `eq_mxsub`, `eq_rowsub`,
      `eq_colsub`, `mxsub_eq_id`, `mxsub_eq_colsub`, `mxsub_eq_rowsub`,
      `mxsub_ffunl`, `mxsub_ffunr`, `mxsub_ffun`, `mxsub_const`,
      `mxsub_comp`, `rowsub_comp`, `colsub_comp`, `mxsubrc`, `mxsubcr`,
      `trmx_mxsub`, `row_mxsub`, `col_mxsub`, `row_rowsub`,
      `col_colsub`, and `map_mxsub`, `pid_mxErow` and `pid_mxEcol`.
    * interaction with `castmx` through lemmas `rowsub_cast`,
      `colsub_cast`, `mxsub_cast`, and `castmxEsub`.
    * `(mx|row|col)sub` are canonically additive and linear.
    * interaction with `mulmx` through lemmas `mxsub_mul`,
      `mul_rowsub_mx`, `mulmx_colsub`, and `rowsubE`.
  + added `comm_mx` and `comm_mxb` the propositional and
    boolean versions of matrix commutation, `comm_mx A B` is
    definitionally equal to `GRing.comm A B` when `A B : 'M_n.+1`, this
    is witnessed by the lemma `comm_mxE`.  New notation `all_comm_mx`
    stands for `allrel comm_mxb`. New lemmas `comm_mx_sym`,
    `comm_mx_refl`, `comm_mx0`, `comm0mx`, `comm_mx1`, `comm1mx`,
    `comm_mxN`, `comm_mxN1`, `comm_mxD`, `comm_mxB`, `comm_mx_sum`,
    `comm_mxP`, `all_comm_mxP`, `all_comm_mx1`, `all_comm_mx2P`,
    `all_comm_mx_cons`, `comm_mx_scalar`, and `comm_scalar_mx`. The
    common arguments of these lemmas `R` and `n` are maximal implicits.

- in `mxalgebra.v`,
  + completed the theory of `pinvmx` in corner cases, using lemmas
    `mulmxVp`, `mulmxKp`, `pinvmxE`, `mulVpmx`, `pinvmx_free`, and
    `pinvmx_full`.
  + new lemmas `row_base0`, `sub_kermx`, `kermx0` and `mulmx_free_eq0`.
  + new lemma `sub_sums_genmxP` (generalizes `sub_sumsmxP`).
  + new lemma `rowsub_sub`, `eq_row_full`,
    `row_full_castmx`, `row_free_castmx`, `rowsub_comp_sub`,
    `submx_rowsub`, `eqmx_rowsub_comp_perm`, `eqmx_rowsub_comp`,
    `eqmx_rowsub`, `row_freePn`, and `negb_row_free`.
  + new lemma `row_free_injr` which duplicates `row_free_inj` but
    exposing `mulmxr` for compositionality purposes (e.g. with
    `raddf_eq0`), and lemma `inj_row_free` characterizing `row_free`
    matrices `A` through `v *m A = 0 -> v = 0` for all `v`.
  + new notation `stablemx V f` asserting that `f`
    stabilizes `V`, with new theorems: `eigenvectorP`, `eqmx_stable`,
    `stablemx_row_base`, `stablemx_full`, `stablemxM`, `stablemxD`,
    `stablemxN`, `stablemxC`, `stablemx0`, `stableDmx`, `stableNmx`,
    `stable0mx`, `stableCmx`, `stablemx_sums`, and `stablemx_unit`.
  + added `comm_mx_stable`, `comm_mx_stable_ker`, and
    `comm_mx_stable_eigenspace`.
  + new definitions `maxrankfun`, `fullrankfun` which
    are "subset function" to be plugged in `rowsub`, with lemmas:
    `maxrowsub_free`, `eq_maxrowsub`, `maxrankfun_inj`,
    `maxrowsub_full`, `fullrowsub_full`, `fullrowsub_unit`,
    `fullrowsub_free`, `mxrank_fullrowsub`, `eq_fullrowsub`, and
    `fullrankfun_inj`.

- in `mxpoly.v`,
  + new lemmas `mxminpoly_minP` and `dvd_mxminpoly`.
  + new lemmas `horner_mx_diag` and `char_poly_trig`,
   `root_mxminpoly`, and `mxminpoly_diag`
  + new definitions `kermxpoly g p` (the kernel of polynomial $p(g)$).
    * new elementary theorems: `kermxpolyC`, `kermxpoly1`,
      `kermxpolyX`, `kermxpoly_min`
    * kernel lemmas: `mxdirect_kermxpoly`, `kermxpolyM`,
      `kermxpoly_prod`, and `mxdirect_sum_kermx`
    * correspondance between `eigenspace` and `kermxpoly`: `eigenspace_poly`
  + generalized eigenspace `geigenspace` and a generalization of eigenvalues
    called `eigenpoly g` (i.e. polynomials such that `kermxpoly g p`
    is nonzero, e.g. eigen polynomials of degree 1 are of the form
    `'X - a%:P` where `a` are eigenvalues), and
    * correspondance with `kermx`: `geigenspaceE`,
    * application of kernel lemmas `mxdirect_sum_geigenspace`,
    * new lemmas: `eigenpolyP`, `eigenvalue_poly`, `eigenspace_sub_geigen`,
  + new `map_mx` lemmas: `map_kermxpoly`, `map_geigenspace`, `eigenpoly_map`.
  + new lemma `horner_mx_stable`.
  + added `comm_mx_horner`, `comm_horner_mx`, `comm_horner_mx2`,
    `horner_mx_stable`, `comm_mx_stable_kermxpoly`, and
    `comm_mx_stable_geigenspace`.

- in `ssrnum.v`,
  + new lemma `ler_sum_nat`
  + new lemmas `big_real`, `sum_real`, `prod_real`, `max_real`,
    `min_real`, `bigmax_real`, and `bigmin_real`.
  + new lemma `real_lteif_distl`.

- in `interval.v`,
  + intervals and their bounds of `T` now have canonical ordered type instances
    whose ordering relations are the subset relation and the left to right
    ordering respectively. They form partially ordered types if `T` is a
    `porderType`. If `T` is a `latticeType`, they also form `tbLatticeType`
    where the join and meet are intersection and convex hull respectively. If
    `T` is an `orderType`, they are distributive, and the interval bounds are
    totally ordered. (cf Changed section)
  + new lemmas `bound_ltxx`, `subitvE`, `in_itv`, `itv_ge`, `in_itvI`,
    `itv_total_meet3E`, and `itv_total_join3E`.

### Changed

- in `ssrbool.v`, use `Reserved Notation` for `[rel _ _ : _ | _]` to
  avoid warnings with coq-8.12

- in `seq.v`, `mask` will only expand if both arguments are
  constructors, the case `mask [::] s` can be dealt with using
  `mask0s` or explicit conversion.

- in `path.v`,
  + generalized lemmas `sub_path_in`, `sub_sorted_in`, and
    `eq_path_in` for non-`eqType`s.
  + generalized lemmas `sorted_ltn_nth` and `sorted_leq_nth`
    (formerly `sorted_lt_nth` and `sorted_le_nth`, cf Renamed section) for
    non-`eqType`s.

- in `fintype.v`,
  + added lemma `ord1`, it is the same as `zmodp.ord1`,
    except `fintype.ord1` does not rely on `'I_n` zmodType structure.
  + rename `disjoint_trans` to `disjointWl`
  + lemmas `inj_card_onto` and `inj_card_bij` take a
    weaker hypothesis (i.e. `#|T| >= #|T'|` instead of `#|T| = #|T'|`
    thanks to `leq_card` under injectivity assumption).

- in `finset.v`, fixed printing of notation `[set E | x in A , y in B & P ]`

- in `bigop.v`, lemma `big_rmcond` is deprecated and has been renamed
  `big_rmcomd_in` (and aliased `big_uncond_in`, see Added). The
  variant which does not require an `eqType` is currently named
  `big_uncond` (cf Added) but it will be renamed `big_mkcond` in the
  next release.

- in `ssrAC.v`, fix `non-reversible-notation` warnings

- in `order.v`,
  + in the definition of structures, displays are removed from
    parameters of mixins and fields of classes internally and now only
    appear in parameters of structures. Consequently, each mixin is
    now parameterized by a class rather than a structure, and the
    corresponding factory parameterized by a structure is provided to
    replace the use of the mixin. These factories have the same names
    as in the mixins before this change except that `bLatticeMixin`
    and `tbLatticeMixin` have been renamed to `bottomMixin` and
    `topMixin` respectively.
  + the `dual_*` notations such as `dual_le` are now
    qualified with the `Order` module.
  + `\join^d_` and `\meet^d_` notations are now properly
    specialized for `dual_display`.
  + rephrased `comparable_(min|max)[rl]` in terms of
    `{in _, forall x y, _}`, hence reordering the arguments. Made them
    hints for smoother combination with `comparable_big[lr]`.
  + `>=< y` now stands for `[pred x | x >=< y]`
  + `>< y`  now stands for `[pred x | x >< y]`
  + and the same holds for the dual `>=<^d`, `><^d`, the product
    `>=<^p`, `><^p`, and lexicographic `>=<^l`, `><^l`.
    The previous meanings can be obtained through `>=<%O x` and `><%O x`.
  + generalized `sort_le_id` for any `porderType`.
  + the names of lemmas `join_idPl` and `join_idPr` are transposed
    to follow the naming convention.

- In `ssrnum.v`,
  + `>=< y` now stands for `[pred x | x >=< y]`
  + fixed notations `@minr` and `@maxr` to point `Order.min` and
    `Order.max` respectively.

- in `ssrint.v`, generalized `mulpz` for any `ringType`.

- in `interval.v`:
  + `x <= y ?< if c` (`lersif`) has been generalized to `porderType`, relocated
    to `order.v`, and replaced with `x < y ?<= if c'` (`lteif`) where `c'` is
    negation of `c`.
  + Many definitions and lemmas on intervals such as the membership test are
    generalized from numeric domains to ordered types.
  + Interval bounds `itv_bound : Type -> Type` are redefined with two constructors
    `BSide : bool -> T -> itv_bound T` and `BInfty : bool -> itv_bound T`.
    New notations `BLeft` and `BRight` are aliases for `BSide true` and `BSide false` respectively.
    `BInfty false` and `BInfty true` respectively means positive and negative infinity.
    `BLeft x` and `BRight x` respectively mean close and open bounds as left bounds,
    and they respectively mean open and close bounds as right bounds.
    This change gives us the canonical "left to right" ordering of interval bounds.
  + Lemmas `mid_in_itv(|oo|cc)` have been generalized from
    `realFieldType` to `numFieldType`.

- In `matrix.v`, generalized `diag_mx_comm` and `scalar_mx_comm` to
  all `n`, instead of `n'.+1`, thanks to `commmmx`.

### Renamed

- in `ssrnat.v`
  + `iter_add` -> `iterD`
  + `maxn_mul(l|r)` -> `maxnM(l|r)`
  + `minn_mul(l|r)` -> `minnM(l|r)`
  + `odd_(opp|mul|exp)` -> `odd(N|M|X)`
  + `sqrn_sub` -> `sqrnB`

- in `div.v`
  + `coprime_mul(l|r)` -> `coprimeM(l|r)`
  + `coprime_exp(l|r)` -> `coprimeX(l|r)`

- in `prime.v`
  + `primes_(mul|exp)` -> `primes(M|X)`
  + `pnat_(mul|exp)` -> `pnat(M|X)`

- in `seq.v`,
  + `iota_add(|l)` -> `iotaD(|l)`
  + `allpairs_(cons|cat)r` -> `mem_allpairs_(cons|cat)r`
    (`allpairs_consr` and `allpairs_catr` are now deprecated alias,
    and will be attributed to the new `perm_allpairs_catr`).

- in `path.v`,
  + `eq_sorted(_irr)` -> `(irr_)sorted_eq`
  + `sorted_(lt|le)_nth` -> `sorted_(ltn|leq)_nth`
  + `(ltn|leq)_index` -> `sorted_(ltn|leq)_index`
  + `subseq_order_path` -> `subseq_path`

- in `fintype.v`
  + `bump_addl` -> `bumpDl`
  + `unbump_addl` -> `unbumpDl`

- in `finset.v`,
  + `mem_imset` -> `imset_f` (with deprecation alias, cf. Added section)
  + `mem_imset2` -> `imset2_f` (with deprecation alias, cf. Added section)

- in `bigop.v`
  + `big_rmcond` -> `big_rmcond_in` (cf Changed section)
  + `mulm_add(l|r)` -> `mulmD(l|r)`

- in `order.v`, `eq_sorted_(le|lt)` -> `(le|lt)_sorted_eq`

- in `interval.v`, we deprecate, rename, and relocate to `order.v` the following:
  + `lersif_(trans|anti)` -> `lteif_(trans|anti)`
  + `lersif(xx|NF|S|T|F|W)` -> `lteif(xx|NF|S|T|F|W)`
  + `lersif_(andb|orb|imply)` -> `lteif_(andb|orb|imply)`
  + `ltrW_lersif` -> `ltrW_lteif`
  + `lersifN` -> `lteifNE`
  + `lersif_(min|max)(l|r)` -> ` lteif_(min|max)(l|r)`

- in `interval.v`, we deprecate, rename, and relocate to `ssrnum.v` the following:
  + `subr_lersif(r0|0r|0)` -> `subr_lteif(r0|0r|0)`
  + `lersif01` -> `lteif01`
  + `lersif_(oppl|oppr|0oppr|oppr0|opp2|oppE)` -> `lteif_(oppl|oppr|0oppr|oppr0|opp2|oppE)`
  + `lersif_add2(|l|r)` -> `lteif_add2(|l|r)`
  + `lersif_sub(l|r)_add(l|r)` -> `lteif_sub(l|r)_add(l|r)`
  + `lersif_sub_add(l|r)` -> `lteif_sub_add(l|r)`
  + `lersif_(p|n)mul2(l|r)` -> `lteif_(p|n)mul2(l|r)`
  + `real_lersifN` -> `real_lteifNE`
  + `real_lersif_norm(l|r)` -> `real_lteif_norm(l|r)`
  + `lersif_nnormr` -> `lteif_nnormr`
  + `lersif_norm(l|r)` -> `lteif_norm(l|r)`
  + `lersif_distl` -> `lteif_distl`
  + `lersif_(p|n)div(l|r)_mul(l|r)` -> `lteif_(p|n)div(l|r)_mul(l|r)`

- in `interval.v`, we deprecate and replace the following:
  + `lersif_in_itv` -> `lteif_in_itv`
  + `itv_gte` -> `itv_ge`
  + `l(t|e)r_in_itv` -> `lt_in_itv`

- in `ssralg.v`, `prodrMn`-> `prodrMn_const` (with deprecation alias,
  cf. Added section)

- in `ssrint.v`, `polyC_mulrz` -> `polyCMz`

- in `poly.v`
  + `polyC_(add|opp|sub|muln|mul|inv)` -> `polyC(D|N|B|Mn|M|V)`
  + `lead_coef_opp` -> `lead_coefN`
  + `derivn_sub` -> `derivnB`

- in `polydiv.v`
  + `rdivp_add(l|r)` -> `rdivpD(l|r)`
  + `rmodp_add` -> `rmodpD`
  + `dvdp_scale(l|r)` -> `dvdpZ(l|r)`
  + `dvdp_opp` -> `dvdpNl`
  + `coprimep_scale(l|r)` -> `coprimepZ(l|r)`
  + `coprimep_mul(l|r)` -> `coprimepM(l|r)`
  + `modp_scale(l|r)` -> `modpZ(l|r)`
  + `modp_(opp|add|scalel|scaler)` -> `modp(N|D|Zl|Zr)`
  + `divp_(opp|add|scalel|scaler)` -> `divp(N|D|Zl|Zr)`

- in `matrix.v`, `map_mx_sub` -> `map_mxB`

- in `mxalgebra.v`, `mulsmx_add(l|r)` -> `mulsmxD(l|r)`

- in `vector.v`, `limg_add` -> `limgD`

- in `intdiv.v`
  + `coprimez_mul(l|r)` -> `coprimezM(l|r)`
  + `coprimez_exp(l|r)` -> `coprimezX(l|r)`

### Removed

- in `ssrnat.v`, we remove the compatibility module `mc_1_9`.

- in `interval.v`, we remove the following:
  + `le_bound(l|r)` (use `Order.le` instead)
  + `le_bound(l|r)_refl` (use `lexx` instead)
  + `le_bound(l|r)_anti` (use `eq_le` instead)
  + `le_bound(l|r)_trans` (use `le_trans` instead)
  + `le_bound(l|r)_bb` (use `bound_lexx` instead)
  + `le_bound(l|r)_total` (use `le_total` instead)

- in `interval.v`, we deprecate the following:
  + `itv_intersection` (use `Order.meet` instead)
  + `itv_intersection1i` (use `meet1x` instead)
  + `itv_intersectioni1` (use `meetx1` instead)
  + `itv_intersectionii` (use `meetxx` instead)
  + `itv_intersectionC` (use `meetC` instead)
  + `itv_intersectionA` (use `meetA` instead)

- in `mxpoly.v`, we deprecate `scalar_mx_comm`, and advise to use
  `comm_mxC` instead (with maximal implicit arguments `R` and `n`).

### Infrastructure

- in all the hierarchies (in `eqtype.v`, `choice.v`, `order.v`,
  `ssralg.v`,...), the `class_of` records of structures are turned
  into primitive records to prevent prevent potential issues of
  ambiguous paths and convertibility of structure instances.

- across the library, the following constants have been tuned to only
  reduce when they do not expose a match: `subn_rec`, `decode_rec`,
  `nth` (thus avoiding a notorious problem of ``p`_0`` expanding too
  eagerly), `set_nth`, `take`, `drop`, `eqseq`, `incr_nth`, `elogn2`,
  `binomial_rec`, `sumpT`.

## [1.11.0] - 2020-06-09

This release is compatible with Coq versions 8.7, 8.8, 8.9, 8.10, and 8.11.

The contributors to this version are:
Antonio Nikishaev, Anton Trunov, Assia Mahboubi, Christian Doczkal, Cyril Cohen,
Enrico Tassi, Erik Martin-Dorel, Florent Hivert, Kazuhiko Sakaguchi,
Pierre-Marie Pédrot, Pierre-Yves Strub, Reynald Affeldt, Simon Boulier, Yves Bertot.

- Added lemmas about monotony of functions `nat -> T` where `T` is an
  ordered type: `homo_ltn_lt_in`, `incn_inP`, `nondecn_inP`,
  `nhomo_ltn_lt_in`, `decn_inP`, `nonincn_inP`, `homo_ltn_lt`,
  `incnP`, `nondecnP`, `nhomo_ltn_lt`, `decnP`, `nonincnP` in file
  `order.v`.

- Added lemmas for swaping arguments of homomorphisms and
  monomorphisms: `homo_sym`, `mono_sym`, `homo_sym_in`, `mono_sym_in`,
  `homo_sym_in11`, `mono_sym_in11` in `ssrbool.v`

### Added

- in `ssrnum.v`, new lemmas:
  + `(real_)ltr_normlW`, `(real_)ltrNnormlW`, `(real_)ler_normlW`, `(real_)lerNnormlW`
  + `(real_)ltr_distl_addr`, `(real_)ler_distl_addr`, `(real_)ltr_distlC_addr`, `(real_)ler_distlC_addr`,
    `(real_)ltr_distl_subl`, `(real_)ler_distl_subl`, `(real_)ltr_distlC_subl`, `(real_)ler_distlC_subl`

- in `order.v`, defining `min` and `max` independently from `meet` and
  `join`, and providing a theory about for min and max, hence generalizing
  the theory of `Num.min` and `Num.max` from versions <= `1.10`, instead
  of specializing to total order as in `1.11+beta1`:
  ```
  Definition min (T : porderType) (x y : T) := if x < y then x else y.
  Definition max (T : porderType) (x y : T) := if x < y then y else x.
  ```
  + Lemmas: `min_l`, `min_r`, `max_l`, `max_r`, `minxx`, `maxxx`, `eq_minl`, `eq_maxr`,
    `min_idPl`, `max_idPr`, `min_minxK`, `min_minKx`, `max_maxxK`, `max_maxKx`,
    `comparable_minl`, `comparable_minr`,  `comparable_maxl`, and `comparable_maxr`
  + Lemmas about interaction with lattice operations:  `meetEtotal`, `joinEtotal`,
  + Lemmas under condition of pairwise comparability of a (sub)set of their arguments:
    `comparable_minC`, `comparable_maxC`, `comparable_eq_minr`, `comparable_eq_maxl`,
    `comparable_le_minr`, `comparable_le_minl`, `comparable_min_idPr`,
    `comparable_max_idPl`, `comparableP`, `comparable_lt_minr`,
    `comparable_lt_minl`, `comparable_le_maxr`, `comparable_le_maxl`,
    `comparable_lt_maxr`, `comparable_lt_maxl`, `comparable_minxK`, `comparable_minKx`,
    `comparable_maxxK`, `comparable_maxKx`,
    `comparable_minA`, `comparable_maxA`, `comparable_max_minl`, `comparable_min_maxl`,
    `comparable_minAC`, `comparable_maxAC`, `comparable_minCA`, `comparable_maxCA`,
    `comparable_minACA`, `comparable_maxACA`, `comparable_max_minr`, `comparable_min_maxr`
  + and the same but in a total order: `minC`, `maxC`, `minA`, `maxA`, `minAC`, `maxAC`,
    `minCA`, `maxCA`, `minACA`, `maxACA`, `eq_minr`, `eq_maxl`,
    `min_idPr`, `max_idPl`, `le_minr`, `le_minl`, `lt_minr`,
    `lt_minl`, `le_maxr`,`le_maxl`, `lt_maxr`, `lt_maxl`, `minxK`, `minKx`,
    `maxxK`, `maxKx`, `max_minl`, `min_maxl`, `max_minr`, `min_maxr`
- in `ssrnum.v`, theory about `min` and `max` extended to `numDomainType`:
  + Lemmas: `real_oppr_max`, `real_oppr_min`, `real_addr_minl`, `real_addr_minr`,
    `real_addr_maxl`, `real_addr_maxr`, `minr_pmulr`, `maxr_pmulr`, `real_maxr_nmulr`,
    `real_minr_nmulr`, `minr_pmull`, `maxr_pmull`, `real_minr_nmull`, `real_maxr_nmull`,
    `real_maxrN`, `real_maxNr`, `real_minrN`, `real_minNr`
- the compatibility module `ssrnum.mc_1_10` was extended to  support definitional
  compatibility with `min` and `max` which had been lost in `1.11+beta1` for most instances.
- in `fintype.v`, new lemmas: `seq_sub_default`, `seq_subE`
- in `order.v`, new "unfolding" lemmas: `minEnat` and `maxEnat`

- in `ssrbool.v`
  + lemmas about the `cancel` predicate and `{in _, _}`/`{on _, _}` notations:
    * `onW_can`, `onW_can_in`, `in_onW_can`, `onS_can`, `onS_can_in`, `in_onS_can`
  + lemmas about the `cancel` predicate and injective functions:
    * `inj_can_sym_in_on`, `inj_can_sym_on`, `inj_can_sym_in`

### Changed

- in `order.v`, `le_xor_gt`, `lt_xor_ge`, `compare`, `incompare`, `lel_xor_gt`,
  `ltl_xor_ge`, `comparel`, `incomparel` have more parameters, so that the
  the following now deal with `min` and `max`
  + `comparable_ltgtP`, `comparable_leP`, `comparable_ltP`, `comparableP`
  + `lcomparableP`, `lcomparable_ltgtP`, `lcomparable_leP`, `lcomparable_ltP`, `ltgtP`
- in `order.v`:
  + `[arg min_(i < i0 | P) M]` now for `porderType` (was for `orderType`)
  + `[arg max_(i < i0 | P) M]` now for `porderType` (was for `orderType`)
  + added `comparable_arg_minP`,  `comparable_arg_maxP`,  `real_arg_minP`,  `real_arg_maxP`,
    in order to take advantage of the former generalizations.
- in `ssrnum.v`, `maxr` is a notation for `(@Order.max ring_display _)` (was `Order.join`)
  (resp. `minr` is a notation for `(@Order.min ring_display _)`)
- in `ssrnum.v`, `ler_xor_gt`, `ltr_xor_ge`, `comparer`,
  `ger0_xor_lt0`, `ler0_xor_gt0`, `comparer0` have now more parameters, so that
  the following now deal with min and max:
  + `real_leP`, `real_ltP x y`, `real_ltgtP`, `real_ge0P`, `real_le0P`, `real_ltgt0P`
  + `lerP`, `ltrP`, `ltrgtP`, `ger0P`, `ler0P`, `ltrgt0P`
- in `ssrnum.v`, the following have been restated (which were formerly derived from
  `order.v` and stated with specializations of the `meet` and `join` operators):
   + `minrC`, `minrr`, `minr_l`, `minr_r`, `maxrC`, `maxrr`, `maxr_l`,
     `maxr_r`, `minrA`, `minrCA`, `minrAC`, `maxrA`, `maxrCA`, `maxrAC`
   + `eqr_minl`, `eqr_minr`, `eqr_maxl`, `eqr_maxr`, `ler_minr`, `ler_minl`,
     `ler_maxr`, `ler_maxl`, `ltr_minr`, `ltr_minl`, `ltr_maxr`, `ltr_maxl`
   + `minrK`, `minKr`, `maxr_minl`, `maxr_minr`, `minr_maxl`, `minr_maxr`
- The new definitions of `min` and `max` may require the following rewrite rules
  changes when dealing with `max` and `min` instead of `meet` and `join`:
  + `ltexI` -> `(le_minr,lt_minr)`
  + `lteIx` -> `(le_minl,lt_minl)`
  + `ltexU` -> `(le_maxr,lt_maxr)`
  + `lteUx` -> `(le_maxl,lt_maxl)`
  + `lexU` -> `le_maxr`
  + `ltxU` -> `lt_maxr`
  + `lexU` -> `le_maxr`

- in `ssrbool.v`
  + lemmas about monotone functions and the `{in _, _}` notation:
    * `homoRL_in`, `homoLR_in`, `homo_mono_in`, `monoLR_in`, `monoRL_in`, `can_mono_in`

### Renamed

- in `fintype` we deprecate and rename the following:
  + `arg_minP` -> `arg_minnP`
  + `arg_maxP` -> `arg_maxnP`

- in `order.v`, in module `NatOrder`, renamings:
  + `meetEnat` -> `minEnat`, `joinEnat` -> `maxEnat`,
    `meetEnat` -> `minEnat`, `joinEnat` -> `maxEnat`

### Removed

- in `order.v`, removed `total_display` (was used to provide the notation
  `max` for `join` and `min` for `meet`).
- in `order.v`, removed `minnE` and `maxnE`
- in `order.v`,
  + removed `meetEnat` (in favor of `meetEtotal` followed by `minEnat`)
  + removed `joinEnat` (in favor of `joinEtotal` followed by `maxEnat`)

## [1.11+beta1] - 2020-04-15

This release is compatible with Coq versions 8.7, 8.8, 8.9 and 8.10.

The contributors to this version are:
Antonio Nikishaev, Anton Trunov, Assia Mahboubi, Cyril Cohen, Enrico Tassi,
Erik Martin-Dorel, Florent Hivert, Kazuhiko Sakaguchi, Pierre-Marie Pédrot,
Pierre-Yves Strub, Reynald Affeldt, Simon Boulier, Yves Bertot.


### Added

- Arithmetic theorems in ssrnat, div and prime about `logn`,
    `coprime`, `gcd`, `lcm` and `partn`: `logn_coprime`, `logn_gcd`,
    `logn_lcm`, `eq_partn_from_log` and `eqn_from_log`.

- Lemmas `ltnNleqif`, `eq_leqif`, `eqTleqif` in `ssrnat`

- Lemmas `eqEtupe`, `tnthS` and `tnth_nseq` in `tuple`

- Ported `order.v` from the finmap library, which provides structures of ordered
  sets (`porderType`, `latticeType`, `distrLatticeType`, `orderType`, etc.) and
  its theory.

- Lemmas `path_map`, `eq_path_in`, `sub_path_in`, `path_sortedE`,
  `sub_sorted` and `sub_sorted_in` in `path` (and refactored related proofs)

- Added lemmas `hasNfind`, `memNindex` and `findP` in `seq`

- Added lemmas `foldr_rcons`, `foldl_rcons`, `scanl_rcons` and
  `nth_cons_scanl` in `seq`

- ssrAC tactics, see header of `ssreflect/ssrAC.v` for documentation
  of `(AC patternshape reordering)`, `(ACl reordering)` `(ACof
  reordering reordering)`, `op.[AC patternshape reordering]`, `op.[ACl
  reordering]` and `op.[ACof reordering reordering]`.

- Added definition `cast_perm` with a group morphism canonical
  structure, and lemmas `permX_fix`, `imset_perm1`, `permS0`,
  `permS1`, `cast_perm_id`, `cast_ord_permE`, `cast_permE`,
  `cast_perm_comp`, `cast_permK`, `cast_permKV`, `cast_perm_inj`,
  `cast_perm_sym`,`cast_perm_morphM`, and `isom_cast_perm` in `perm`
  and `restr_perm_commute` in `action`.

- Added `card_porbit_neq0`, `porbitP`, and `porbitPmin` in `perm`

- Added definition `Sym` with a group set canonical structure and
  lemmas `card_Sn` and `card_Sym` in `perm` and `SymE` in `action`

### Changed

- Reorganized the algebraic hierarchy and the theory of `ssrnum.v`.
  + `numDomainType` and `realDomainType` get inheritances respectively from
    `porderType` and `orderType`.
  + `normedZmodType` is a new structure for `numDomainType` indexed normed
    additive abelian groups.
  + `[arg minr_( i < n | P ) F]` and `[arg maxr_( i < n | P ) F]` notations are
    removed. Now `[arg min_( i < n | P ) F]` and `[arg max_( i < n | P ) F]`
    notations are defined in `nat_scope` (specialized for `nat`), `order_scope`
    (general one), and `ring_scope` (specialized for `ring_display`). Lemma
    `fintype.arg_minP` is aliased to `arg_minnP` and the same for `arg_maxnP`.
  + The following lemmas are generalized, renamed, and relocated to `order.v`:
    * `ltr_def` -> `lt_def`
    * `(ger|gtr)E` -> `(ge|gt)E`
    * `(le|lt|lte)rr` -> `(le|lt|lte)xx`
    * `ltrW` -> `ltW`
    * `ltr_neqAle` -> `lt_neqAle`
    * `ler_eqVlt` -> `le_eqVlt`
    * `(gtr|ltr)_eqF` -> `(gt|lt)_eqF`
    * `ler_anti`, `ler_asym` -> `le_anti`
    * `eqr_le` -> `eq_le`
    * `(ltr|ler_lt|ltr_le|ler)_trans` -> `(lt|le_lt|lt_le|le)_trans`
    * `lerifP` -> `leifP`
    * `(ltr|ltr_le|ler_lt)_asym` -> `(lt|lt_le|le_lt)_asym`
    * `lter_anti` -> `lte_anti`
    * `ltr_geF` -> `lt_geF`
    * `ler_gtF` -> `le_gtF`
    * `ltr_gtF` -> `lt_gtF`
    * `lt(r|nr|rn)W_(n)homo(_in)` -> `ltW_(n)homo(_in)`
    * `inj_(n)homo_lt(r|nr|rn)(_in)` -> `inj_(n)homo_lt(_in)`
    * `(inc|dec)(r|nr|rn)_inj(_in)` -> `(inc_dec)_inj(_in)`
    * `le(r|nr|rn)W_(n)mono(_in)` -> `leW_(n)mono(_in)`
    * `lenr_(n)mono(_in)` -> `le_(n)mono(_in)`
    * `lerif_(refl|trans|le|eq)` -> `leif_(refl|trans|le|eq)`
    * `(ger|ltr)_lerif` -> `(ge|lt)_leif`
    * `(n)mono(_in)_lerif` -> `(n)mono(_in)_leif`
    * `(ler|ltr)_total` -> `(le|lt)_total`
    * `wlog_(ler|ltr)` -> `wlog_(le|lt)`
    * `ltrNge` -> `ltNge`
    * `lerNgt` -> `leNgt`
    * `neqr_lt` -> `neq_lt`
    * `eqr_(le|lt)(LR|RL)` -> `eq_(le|lt)(LR|RL)`
    * `eqr_(min|max)(l|r)` -> `eq_(meet|join)(l|r)`
    * `ler_minr` -> `lexI`
    * `ler_minl` -> `leIx`
    * `ler_maxr` -> `lexU`
    * `ler_maxl` -> `leUx`
    * `lt(e)r_min(r|l)` -> `lt(e)(xI|Ix)`
    * `lt(e)r_max(r|l)` -> `lt(e)(xU|Ux)`
    * `minrK` -> `meetUKC`
    * `minKr` -> `joinKIC`
    * `maxr_min(l|r)` -> `joinI(l|r)`
    * `minr_max(l|r)` -> `meetU(l|r)`
    * `minrP`, `maxrP` -> `leP`, `ltP`

      Replacing `minrP` and `maxrP` with `leP` and `ltP` may require to provide some arguments explicitly.
      The former ones respectively try to match with `minr` and `maxr` first but the latter ones try that in the order of `<`, `<=`, `maxr`, and `minr`.
    * `(minr|maxr)(r|C|A|CA|AC)` -> `(meet|join)(xx|C|A|CA|AC)`
    * `minr_(l|r)` -> `meet_(l|r)`
    * `maxr_(l|r)` -> `join_(l|r)`
    * `arg_minrP` -> `arg_minP`
    * `arg_maxrP` -> `arg_maxP`
  + Generalized the following lemmas as properties of `normedDomainType`:
    `normr0`, `normr0P`, `normr_eq0`, `distrC`, `normr_id`, `normr_ge0`,
    `normr_le0`, `normr_lt0`, `normr_gt0`, `normrE`, `normr_real`,
    `ler_norm_sum`, `ler_norm_sub`, `ler_dist_add`, `ler_sub_norm_add`,
    `ler_sub_dist`, `ler_dist_dist`, `ler_dist_norm_add`, `ler_nnorml`,
    `ltr_nnorml`, `lter_nnormr`.
  + The compatibility layer for the version 1.10 is provided as the
    `ssrnum.mc_1_10` module. One may compile proofs compatible with the version
    1.10 in newer versions by using the `mc_1_10.Num` module instead of the
    `Num` module. However, instances of the number structures may require
    changes.

- Extended comparison predicates `leqP`, `ltnP`, and `ltngtP` in ssrnat to
  allow case analysis on `minn` and `maxn`.
  + The compatibility layer for the version 1.10 is provided as the
    `ssrnat.mc_1_10` module. One may compile proofs compatible with the version
    1.10 in newer versions by using this module.

- The definition of `all2` was slightly altered for a better interaction with
  the guard condition (#469)

### Renamed

- `real_lerP` -> `real_leP`
- `real_ltrP` -> `real_ltP`
- `real_ltrNge` -> `real_ltNge`
- `real_lerNgt` -> `real_leNgt`
- `real_ltrgtP` -> `real_ltgtP`
- `real_ger0P` -> `real_ge0P`
- `real_ltrgt0P` -> `real_ltgt0P`
- `lerif_nat` -> `leif_nat_r`
- Replaced `lerif` with `leif` in the following names of lemmas:
  + `lerif_subLR`, `lerif_subRL`, `lerif_add`, `lerif_sum`, `lerif_0_sum`,
    `real_lerif_norm`, `lerif_pmul`, `lerif_nmul`, `lerif_pprod`,
    `real_lerif_mean_square_scaled`, `real_lerif_AGM2_scaled`,
    `lerif_AGM_scaled`, `real_lerif_mean_square`, `real_lerif_AGM2`,
    `lerif_AGM`, `relif_mean_square_scaled`, `lerif_AGM2_scaled`,
    `lerif_mean_square`, `lerif_AGM2`, `lerif_normC_Re_Creal`, `lerif_Re_Creal`,
    `lerif_rootC_AGM`.
- The following naming inconsistencies have been fixed in `ssrnat.v`:
  + `homo_inj_lt(_in)` -> `inj_homo_ltn(_in)`
  + `(inc|dec)r_inj(_in)` -> `(inc|dec)n_inj(_in)`
- switching long suffixes to short suffixes
  + `odd_add` -> `oddD`
  + `odd_sub` -> `oddB`
  + `take_addn` -> `takeD`
  + `rot_addn` -> `rotD`
  + `nseq_addn` -> `nseqD`
- Replaced `cycle` by `orbit` in `perm/action`:
  + `pcycle` -> `porbit`
  + `pcycles` -> `porbits`
  + `pcycleE` -> `porbitE`
  + `pcycle_actperm` -> `porbit_actperm`
  + `mem_pcycle` -> `mem_porbit`
  + `pcycle_id` -> `porbit_id`
  + `uniq_traject_pcycle` -> `uniq_traject_porbit`
  + `pcycle_traject` -> `porbit_traject`
  + `iter_pcycle` -> `iter_porbit`
  + `eq_pcycle_mem` -> `eq_porbit_mem`
  + `pcycle_sym` -> `porbit_sym`
  + `pcycle_perm` -> `porbit_perm`
  + `ncycles_mul_tperm` -> `porbits_mul_tperm`

### Removed

The following were deprecated since release 1.9.0
- `tuple_perm_eqP` (use `tuple_permP` instead, from `perm.v`)
- `eq_big_perm` (use `perm_big` instead, from `bigop.v`)
- `perm_eqP` (use `permP` instead, from seq.v)
- `perm_eqlP` (use `permPl` instead)
- `perm_eqrP` (use `permPr` instead)
- `perm_eqlE` (use `permEl` instead)
- `perm_eq_refl` (use `perm_refl` instead)
- `perm_eq_sym` (use `perm_sym` instead)
- `perm_eq_trans` (use `perm_trans` instead)
- `perm_eq_size` (use `perm_size` instead)
- `perm_eq_mem` (use `perm_mem` instead)
- `perm_eq_uniq` (use `perm_uniq` instead)

## [1.10.0] - 2019-11-29

This release is compatible with Coq versions 8.9 and 8.10.

The contributors to this version are:
Antonio Nikishaev, Anton Trunov, Arthur Azevedo de Amorim, Christian Doczkal, Cyril Cohen,
Enrico Tassi, Erik Martin-Dorel, Florent Hivert, Gabriel Taumaturgo, Georges Gonthier,
Kazuhiko Sakaguchi, Laurent Théry, Maxime Dénès, Reynald Affeldt, and Yves Bertot.

### Added

- Added a `void` notation for the `Empty_set` type of the standard library, the
  canonical injection `of_void` and its cancellation lemma `of_voidK`, and
  `eq`, `choice`, `count` and `fin` instances.

- Added `ltn_ind` general induction principle for `nat` variables, helper lemmas `ubnP`, `ltnSE`, ubnPleq, ubnPgeq and ubnPeq, in support of a generalized induction idiom for `nat` measures that does not rely on the `{-2}` numerical occurrence selector, and purged this idiom from the `mathcomp` library (see below).

- Added fixpoint and cofixpoint constructions to `finset`: `fixset`,
  `cofixset` and `fix_order`, with a few theorems about them

- Added functions `tuple_of_finfun`, `finfun_of_tuple`, and their
  "cancellation" lemmas.

- Added theorems `totient_prime` and `Euclid_dvd_prod` in `prime.v`

- Added theorems `ffact_prod`, `prime_modn_expSn` and `fermat_little`
  in `binomial.v`

- Added theorems `flatten_map1`, `allpairs_consr`, `mask_filter`,
  `all_filter`, `all_pmap`, and `all_allpairsP` in `seq.v`.

- Added theorems `nth_rcons_default`, `undup_rcons`, `undup_cat` and
  `undup_flatten_nseq` in `seq.v`

- Fintype theorems: `fintype0`, `card_le1P`, `mem_card1`,
  `card1P`, `fintype_le1P`, `fintype1`, `fintype1P`,
  `existsPn`, `exists_inPn`, `forallPn`, `forall_inPn`,
  `eq_enum_rank_in`, `enum_rank_in_inj`, `lshift_inj`, and
  `rshift_inj`.

- Bigop theorems: `index_enum_uniq`, `big_rmcond`, `bigD1_seq`,
  `big_enum_val_cond`, `big_enum_rank_cond`,
  `big_enum_val`, `big_enum_rank`, `big_set`,
  `big_enumP`, `big_enum_cond`, `big_enum`

- Arithmetic theorems in ssrnat and div:
  - some trivial results in ssrnat: `ltn_predL`, `ltn_predRL`,
    `ltn_subrR`, `leq_subrR`, `ltn_subrL` and `predn_sub`,
  - theorems about `n <=/< p +/- m` and `m +/- n <=/< p`:
    `leq_psubRL`, `ltn_psubLR`, `leq_subRL`, `ltn_subLR`, `leq_subCl`,
    `leq_psubCr`, `leq_subCr`, `ltn_subCr`, `ltn_psubCl` and
    `ltn_subCl`,
  - some commutations between modulo and division: `modn_divl` and
    `divn_modl`,
  - theorems about the euclidean division of additions and subtraction,
     + without preconditions of divisibility: `edivnD`, `edivnB`,
       `divnD`, `divnB`, `modnD`, `modnB`,
     + with divisibility of one argument: `divnDMl`, `divnMBl`,
       `divnBMl`, `divnBl` and `divnBr`,
     + specialization of the former theorems for .+1 and .-1:
       `edivnS`, `divnS`, `modnS`, `edivn_pred`, `divn_pred` and
       `modn_pred`.

- Added `sort_rec1` and `sortE` to help inductive reasoning on `sort`.

- Added map/parametricity theorems about `path`, `sort`, and `sorted`:
  `homo_path`, `mono_path`, `homo_path_in`, `mono_path_in`,
  `homo_sorted`, `mono_sorted`, `map_merge`, `merge_map`, `map_sort`,
  `sort_map`, `sorted_map`, `homo_sorted_in`, `mono_sorted_in`.

- Extracting lemma `fpathE` from `fpathP`, and shortening the proof of
  the latter.

- Added the theorem `perm_iota_sort` to express that the sorting of
  any sequence `s` is equal to a mapping of `iota 0 (size s)` to the
  nth elements of `s`, so that one can still reason on `nat`, even
  though the elements of `s` are not in an `eqType`.

- Added stability theorems about `merge` and `sort`: `sorted_merge`,
  `merge_stable_path`, `merge_stable_sorted`, `sorted_sort`, `sort_stable`,
  `filter_sort`, `mask_sort`, `sorted_mask_sort`, `subseq_sort`,
  `sorted_subseq_sort`, and `mem2_sort`.

- New algebraic interfaces in `ssralg.v`: comAlgebra and
  comUnitAlgebra for commutative and commutative-unitary algebras.

- Initial property for polynomials in algebras:
  New canonical lrMoprphism `horner_alg` evaluating a polynomial in an element
  of an algebra. The theory include the lemmas `in_alg_comm`, `horner_algC`,
  `horner_algX`, `poly_alg_initial`.

- Added lemmas on commutation with difference, big sum and prod:
  `commrB`, `commr_sum`, `commr_prod`.

- Added a few basic seq lemmas about `nseq`, `take` and `drop`:
  `nseq_addn`, `take_take`, `take_drop`, `take_addn`, `takeC`,
  `take_nseq`, `drop_nseq`, `rev_nseq`, `take_iota`, `drop_iota`.

- Added ssrfun theorem `inj_compr`.

- Added theorems `mem2E`, `nextE`, `mem_fcycle`, `inj_cycle`,
  `take_traject`, `trajectD` and `cycle_catC` in `path.v`

- Added lemmas about `cycle`, `connect`, `fconnect`, `order` and
  `orbit` in `fingraph.v`:
  - lemma `connect_cycle`,
  - lemmas `in_orbit`, `order_gt0`, `findex_eq0`, `mem_orbit`,
    `image_orbit`,
  - lemmas `fcycle_rconsE`, `fcycle_consE`, `fcycle_consEflatten` and
    `undup_cycle_cons` which operate under the precondition that the
    sequence `x :: p` is a cycle for f (i.e. `fcycle f (x :: p)`).
  - lemmas which operate under the precondition there is a sequence
    `p` which is a cycle for `f` (i.e. `fcycle f p`):
    `order_le_cycle`, `finv_cycle`, `f_finv_cycle`, `finv_f_cycle`,
    `finv_inj_cycle`, `iter_finv_cycle`, `cycle_orbit_cycle`,
    `fpath_finv_cycle`, `fpath_finv_f_cycle`, `fpath_f_finv_cycle`,
    `prevE`, `fcycleEflatten`, `fcycle_undup`, `in_orbit_cycle`,
    `eq_order_cycle`, `iter_order_cycle`,
  - lemmas `injectivePcycle`, `orbitPcycle`, `fconnect_eqVf`,
    `order_id_cycle`, `orderPcycle`, `fconnect_f`, `fconnect_findex`.

- Added lemma `rot_index` which explicits the index given by `rot_to`.

- Added tactic `tfae` to split an equivalence between n+1 propositions
  into n+1 goals, and referenced orbitPcycle as a reference of use.

### Changed

- Replaced the legacy generalised induction idiom with a more robust one
that does not rely on the `{-2}` numerical occurrence selector, using
new `ssrnat` helper lemmas `ltn_ind`, `ubnP`, `ubnPleq`,  ...., (see above). The new idiom is documented in `ssrnat`.
   This change anticipates an expected evolution of `fintype` to integrate `finmap`. It is likely that the new definition of the `#|A|` notation will hide multiple occurrences of `A`, which will break the `{-2}` induction idiom. Client libraries should update before the 1.11 release (see [PR #434](https://github.com/math-comp/math-comp/pull/434) for examples).

 - Replaced the use of the accidental convertibility between `enum A` and
   `filter A (index_enum T)` with more explicit lemmas `big_enumP`, `big_enum`, `big_enum_cond`, `big_image` added to the `bigop` library, and deprecated the `filter_index_enum` lemma that states the corresponding equality. Both convertibility and equality may no longer hold in future `mathcomp` releases when sets over `finType`s are generalised to finite sets over `choiceType`s, so client libraries should stop relying on this identity. File `bigop.v` has some boilerplate to help with the port; also see [PR #441](https://github.com/math-comp/math-comp/pull/441) for examples.

 - Restricted `big_image`, `big_image_cond`, `big_image_id` and `big_image_cond_id`
 to `bigop`s over _abelian_ monoids, anticipating the change in the definition of `enum`. This may introduce some incompatibilities - non-abelian instances should be dealt with a combination of `big_map` and `big_enumP`.

- `eqVneq` lemma is changed from `{x = y} + {x != y}` to
  `eq_xor_neq x y (y == x) (x == y)`, on which a case analysis performs
  simultaneous replacement of expressions of the form `x == y` and `y == x`
  by `true` or `false`, while keeping the ability to use it in the way
  it was used before.

- Generalized the `allpairs_catr` lemma to the case where the types of `s`,
  `t1`, and `t2` are non-`eqType`s in `[seq E | i <- s, j <- t1 ++ t2]`.

- Generalized `muln_modr` and `muln_modl` removing hypothesis `0 < p`.

- Generalized `sort` to non-`eqType`s (as well as `merge`,
  `merge_sort_push`, `merge_sort_pop`), together with all the lemmas
  that did not really rely on an `eqType`: `size_merge`, `size_sort`,
  `merge_path`, `merge_sorted`, `sort_sorted`, `path_min_sorted`
  (which statement was modified to remove the dependency in `eqType`),
  and `order_path_min`.

- `compare_nat` type family and `ltngtP` comparison predicate are changed
  from `compare_nat m n (m <= n) (n <= m) (m < n) (n < m) (n == m) (m == n)`
  to `compare_nat m n (n == m) (m == n) (n <= m) (m <= n) (n < m) (m < n)`,
  to make it tries to match subterms with `m < n` first, `m <= n`, then
  `m == n`.
  + The compatibility layer for the version 1.9 is provided as the
    `ssrnat.mc_1_9` module. One may compile proofs compatible with the version
    1.9 in newer versions by using this module.

- Moved `iter_in` to ssrnat and reordered its arguments.

- Notation `[<-> P0 ; .. ; Pn]` now forces `Pi` to be of type `Prop`.

### Removed

- `fin_inj_bij` lemma is removed as a duplicate of `injF_bij` lemma
  from `fintype` library.

### Infrastructure

- `Makefile` now supports the `test-suite` and `only` targets. Currently,
  `make test-suite` will verify the implementation of mathematical structures
  and their inheritances of MathComp automatically, by using the `hierarchy.ml`
  utility. One can use the `only` target to build the sub-libraries of MathComp
  specified by the `TGTS` variable, e.g.,
  `make only TGTS="ssreflect/all_ssreflect.vo fingroup/all_fingroup.vo"`.

- `Makefile`now supports a `doc` target to build the documentation as made
   available on https://mathcomp.github.io/htmldoc/index.html

## [1.9.0] - 2019-05-22

MathComp 1.9.0 is compatible with Coq 8.7, 8.8, 8.9 and 8.10beta1.
Minor releases will remain compatible with Coq 8.9 and 8.10; compatibility with earlier
versions may be dropped.

The contributors to this version are:
Cyril Cohen, Enrico Tassi, Erik Martin-Dorel, Georges Gonthier,
Kazuhiko Sakaguchi, Sora Chen, Søren Eller Thomsen.

### Added

- `nonPropType`, an interface for non-`Prop` types, and `{pred T}` and
   `relpre f r`, all of which will be in the Coq 8.10 core SSreflect library.

- `deprecate old_id new_id`, notation for `new_id` that prints a deprecation
  warning for `old_id`; `Import Deprecation.Silent` turns off those warnings,
  `Import Deprecation.Reject` raises errors instead of only warning.

- `filter_nseq`, `count_nseq`, `mem_nseq`,
  `rcons_inj`, `rcons_injl`, `rcons_injr`, `nthK`, `sumn_rot`.

- some `perm_eq` lemmas: `perm_cat[lr]`, `perm_nilP`,
  `perm_consP`, `perm_has`, `perm_flatten`, `perm_sumn`.

- computing (efficiently) (item, multiplicity) tallies of sequences over an
  `eqType`: `tally s`, `incr_tally bs x`, `bs \is a wf_tally`, `tally_seq bs`.

### Changed

- definition of `PredType` which now takes only a `P -> pred T` function;
  definition of `simpl_rel` to improve simplification by `inE`. Both these
  changes will be in the Coq 8.10 SSReflect core library.

- definition of `permutations s` now uses an optimal algorithm (in space _and_
  time) to generate all permutations of s back-to-front, using `tally s`.

### Renamed

- `perm_eqP` -> `permP` (`seq.permP` if `perm.v` is also imported)
- `perm_eqlP` -> `permPl`
- `perm_eqrP` -> `permPr`
- `perm_eqlE` -> `permEl`
- `perm_eq_refl` -> `perm_refl`
- `perm_eq_sym` -> `perm_sym`
- `perm_eq_trans` -> `perm_trans`
- `perm_eq_size` -> `perm_size`
- `perm_eq_mem` -> `perm_mem`
- `perm_eq_uniq` -> `perm_uniq`
- `perm_eq_rev` -> `perm_rev`
- `perm_eq_flatten` -> `perm_flatten`
- `perm_eq_all` -> `perm_all`
- `perm_eq_small` -> `perm_small_eq`
- `perm_eq_nilP` -> `perm_nilP`
- `perm_eq_consP` -> `perm_consP`
- `leq_size_perm` -> `uniq_min_size` (permuting conclusions)
- `perm_uniq` -> `eq_uniq` (permuting assumptions)
  --> beware `perm_uniq` now means `perm_eq_uniq`
- `uniq_perm_eq` -> `uniq_perm`
- `perm_eq_iotaP` -> `perm_iotaP`
- `perm_undup_count` -> `perm_count_undup`
- `tuple_perm_eqP` -> `tuple_permP`
- `eq_big_perm` -> `perm_big`
- `perm_eq_abelian_type` -> `abelian_type_pgroup`

### Misc

- removed Coq prelude hints `plus_n_O` `plus_n_Sm` `mult_n_O` `mult_n_Sm`,
  to improve robustness of `by ...`; scripts may need to invoke
  `addn0`, `addnS`, `muln0` or `mulnS`
  explicitly where these hints were used accidentally.

## [1.8.0] - 2019-04-08

Drop compatibility with Coq 8.6 (OCaml plugin removed).
MathComp 1.8.0 is compatible with Coq 8.7, 8.8 and 8.9.

The contributors to this version are:
Anton Trunov, Assia Mahboubi, Cyril Cohen, Enrico Tassi, Erik Martin-Dorel,
Florent Hivert, Georges Gonthier, Kazuhiko Sakaguchi, Laurence Rideau,
Laurent Théry, Pierre-Yves Strub, Søren Eller Thomsen, Yves Bertot. 

### Added

- Companion matrix of a polynomial `companionmx p` and the
  theorems: `companionmxK`, `map_mx_companion` and `companion_map_poly`

- `homoW_in`, `inj_homo_in`, `mono_inj_in`, `anti_mono_in`,
  `total_homo_mono_in`, `homoW`, `inj_homo`, `monoj`, `anti_mono`,
  `total_homo_mono`

- `sorted_lt_nth`, `ltn_index`, `sorted_le_nth`, `leq_index`.

- `[arg minr_( i < n | P ) F]` and `[arg maxr_( i < n | P ) F]`
  with all their variants, following the same convention as for `nat`

- `contra_neqN`, `contra_neqF`, `contra_neqT`, `contra_neq_eq`, `contra_eq_neq`

- `take_subseq`, `drop_subseq`

- `big_imset_cond`,`big_map_id`, `big_image_cond`
  `big_image`, `big_image_cond_id` and `big_image_id`

- `foldrE`, `foldlE`, `foldl_idx` and `sumnE`
  to turn "seq statements" into "bigop statements"

- `all_iff` with notation `[<-> P0; P1; ..; Pn]` to talk about
  circular implication `P0 -> P1 -> ... -> Pn -> P0`.
  Related theorems are `all_iffLR` and `all_iffP`

- support for casts in map comprehension notations, e.g.,
  `[seq E : T | s <- s]`.

- a predicate `all2`, a parallel double `seq` version of `all`.

- some `perm_eq` lemmas: `perm_cat[lr]`, `perm_eq_nilP`,
  `perm_eq_consP`, `perm_eq_flatten`.

- a function `permutations` that computes a duplicate-free list
  of all permutations of a given sequence `s` over an `eqType`, along
  with its theory: `mem_permutations`, `size_permutations`,
  `permutations_uniq`, `permutations_all_uniq`, `perm_permutations`.

- `eq_mktuple`, `eq_ffun`, `eq_finset`, `eq_poly`, `ex_mx` that can be
  used with the `under` tactic from the Coq 8.10 SSReflect plugin
  (cf. [coq/coq#9651](https://github.com/coq/coq/pull/9651))

### Changed

- Theory of `lersif` and intervals:
  + Many `lersif` related lemmas are ported from `ssrnum`
  + Changed: `prev_of_itv`, `itv_decompose`, and `itv_rewrite`
  + New theory of intersections of intervals

- Generalized `extremum_spec` and its theory, added `extremum` and
  `extremumP`, generalizing `arg_min` for an arbitrary `eqType` with an
  order relation on it (rather than `nat`). Redefined `arg_min` and
  `arg_max` with it.

- Reshuffled theorems inside files and packages:
  + `countalg` goes from the field to the algebra package
  + `finalg` inherits from countalg
  + `closed_field` contains the construction of algebraic closure
    for countable fields that used to be in the file `countalg`.

- Maximal implicits applied to reflection, injectivity and cancellation
  lemmas so that they are easier to pass to combinator lemmas such as
  `sameP`, `inj_eq` or `canLR`.

- Added `reindex_inj s` shorthand for reindexing a bigop with a
  permutation `s`.

- Added lemma `eqmxMunitP`: two matrices with the same shape
  represent the same subspace iff they differ only by a change of
  basis.

- Corrected implicits and documentation of `MatrixGenField`.

- Rewritten proof of quantifier elimination for closed field in a
  monadic style.

- Specialized `bool_irrelevance` so that the statement reflects
  the name.

- Changed the shape of the type of `FieldMixin` to allow one-line
  in-proof definition of bespoke `fieldType` structure.

- Refactored and extended Arguments directives to provide more
  comprehensive signature information.

- Generalized the notation `[seq E | i <- s, j <- t]` to the case
  where `t` may depend on `i`. The notation is now primitive and
  expressed using `flatten` and `map` (see documentation of seq).
  `allpairs` now expands to this notation when fully applied.
  + Added `allpairs_dep` and made it self-expanding as well.
  + Generalized some lemmas in a backward compatible way.
  + Some strictly more general lemmas now have suffix `_dep`.
  + Replaced `allpairs_comp` with its converse `map_allpairs`.
  + Added `allpairs` extensionality lemmas for the following cases:
    non-localised (`eq_allpairs`), dependent localised
    (`eq_in_allpairs_dep`) and non-dependent localised
    (`eq_in_allpairs`); as per `eq_in_map`, the latter two are
    equivalences.

- Generalized `{ffun A -> R}` to handle dependent functions, and to be
  structurally positive so it can be used in recursive inductive type
  definitions.

  Minor backward incompatibilities: `fgraph f` is no longer
  a field accessor, and no longer equal to `val f` as `{ffun A -> R}` is no
  longer a `subType`; some instances of `finfun`, `ffunE`, `ffunK` may not unify
  with a generic non-dependent function type `A -> ?R` due to a bug in
  Coq version 8.9 or below.

- Renamed double `seq` induction lemma from `seq2_ind` to `seq_ind2`,
  and weakened its induction hypothesis.

- Replaced the `nosimpl` in `rev` with a `Arguments simpl never`
  directive.

- Many corrections in implicits declarations.

- fixed missing joins in `ssralg`, `ssrnum`, `finalg` and `countalg`

### Renamed

Renamings also involve the `_in` suffix counterpart when applicable

- `mono_inj` -> `incr_inj`
- `nmono_inj` -> `decr_inj`
- `leq_mono_inj` -> `incnr_inj`
- `leq_nmono_inj` -> `decnr_inj`
- `homo_inj_ltn_lt` -> `incnr_inj`
- `nhomo_inj_ltn_lt` -> `decnr_inj`
- `homo_inj_in_lt` -> `inj_homo_ltr_in`
- `nhomo_inj_in_lt` -> `inj_nhomo_ltr_in`
- `ltn_ltrW_homo` -> `ltnrW_homo`
- `ltn_ltrW_nhomo` -> `ltnrW_nhomo`
- `leq_lerW_mono` -> `lenrW_mono`
- `leq_lerW_nmono` -> `lenrW_nmono`
- `homo_leq_mono` -> `lenr_mono`
- `nhomo_leq_mono` -> `lenr_nmono`
- `homo_inj_lt` -> `inj_homo_ltr`
- `nhomo_inj_lt` -> `inj_nhomo_ltr`
- `homo_inj_ltn_lt` -> `inj_homo_ltnr`
- `nhomo_inj_ltn_lt` -> `inj_nhomo_ltnr`
- `homo_mono` -> `ler_mono`
- `nhomo_mono` -> `ler_nmono`
- `big_setIDdep` -> `big_setIDcond`
- `sum_nat_dep_const` -> `sum_nat_cond_const`

### Misc

- Removed trailing `_ : Type` field from packed classes. This performance
  optimization is not strictly necessary with modern Coq versions.

- Removed duplicated definitions of `tag`, `tagged` and `Tagged`
  from `eqtype.v`. They are already in `ssrfun.v`.

- Miscellaneous improvements to proof scripts and file organisation.

## [1.7.0] - 2018-04-24

Compatibility with Coq 8.8 and lost compatibility with
Coq <= 8.5. This release is compatible with Coq 8.6, 8.7 and 8.8.

- Integration in Coq startng from version 8.7 of:
  + OCaml plugin (plugin for 8.6 still in the archive for backward compatibility)
  + `ssreflect.v`, `ssrbool.v`, `ssrfun.v` and `ssrtest/`

- Cleaning up the github repository: the math-comp repository is
  now dedicated to the released material (as in the present
  release). For instance, directories `real-closed/` and `odd-order/` now
  have their own repository.

### Changed

- Library refactoring: `algC` and `ssrnum`.
  Library `ssrnum.v` provides an interface `numClosedFieldType`, which abstracts the
  theory of algebraic numbers. In particular, `Re`, `Im`, `'i`,
  `conjC`, `n.-root` and `sqrtC`, previously defined in library `algC.v`,
  are now part of this generic interface. In case of ambiguity,
  a cast to type `algC`, of complex algebraic numbers, can be used to
  disambiguate via  typing constraints. Some theory was thus made
  more generic, and the corresponding lemmas, previously defined in
  library `algC.v` (e.g. `conjCK`) now feature an extra, non maximal
  implicit, parameter of type `numClosedFieldType`. This could break
  some proofs.
  Every theorem from `ssrnum` that used to be in `algC` changed statement.

- `ltngtP`, `contra_eq`, `contra_neq`, `odd_opp`, `nth_iota`

### Added

- `iter_in`, `finv_in`, `inv_f_in`, `finv_inj_in`, `fconnect_sym_in`, `iter_order_in`,
  `iter_finv_in`, `cycle_orbit_in`, `fpath_finv_in`, `fpath_finv_f_in`, `fpath_f_finv_in`
- `big_allpairs`
- `uniqP, uniqPn`
- `dec_factor_theorem`, `mul_bin_down`, `mul_bin_left`
- `abstract_context` (`in ssreflect.v`, now merged in Coq proper)

### Renamed

- Lemma `dvdn_fact` was moved from library `prime.v` to library `div.v`
- `mul_Sm_binm -> mul_bin_diag
- `divn1` -> `divz1` (in intdiv)
- `rootC` -> `nthroot`
- `algRe` -> `Re`
- `algIm` -> `Im`
- `algCi` -> `imaginaryC`
- `reshape_index_leq` -> `reshape_leq`

## [1.6.0] - 2015-11-24 (ssreflect + mathcomp)

Major reorganization of the archive.

- Files split into sub-directories: `ssreflect/`, `algebra/`, `fingroup/`,
  `solvable/`, `field/` and `character/`. In this way the user can decide
  to compile only the subset of the Mathematical Components library
  that is relevant to her. Note that this introduces a possible
  incompatibility for users of the previous version. A replacement
  scheme is suggested in the installation notes.

- The archive is now open and based on git. Public mirror at:
  https://github.com/math-comp/math-comp

- Sources of the reference manual of the Ssreflect tactic language are
  also open and available at: https://github.com/math-comp/ssr-manual
  Pull requests improving the documentation are welcome.

### Renamed
- `conjC_closed` -> `cfConjC_closed`
- `class_transr` -> `class_eqP`
- `cfclass_transl` -> `cfclass_transr`
- `nontrivial_ideal` -> `proper_ideal`
- `zchar_orthonormalP` -> `vchar_orthonormalP`

### Changed
- `seq_sub`
- `orbit_in_transl`, `orbit_sym`, `orbit_trans`, `orbit_transl`, `orbit_transr`,
  `cfAut_char`, `cfConjC_char`, `invg_lcosets`, `lcoset_transl`, `lcoset_transr`,
  `rcoset_transl`, `rcoset_transr`, `mem2_last`, `bind_unless`, `unless_contra`, `all_and2`,
  `all_and3`, `all_and4`, `all_and5`, `ltr0_neq0`, `ltr_prod`, `Zisometry_of_iso`

### Added
- `adhoc_seq_sub_choiceMixin`, `adhoc_seq_sub_[choice|fin]Type`
- `orbit_in_eqP`, `cards_draws`, `cfAut_lin_char`, `cfConjC_lin_char`,
  `extend_cfConjC_subset`, `isometry_of_free`, `cfAutK`, `cfAutVK`,
  `lcoset_eqP`, `rcoset_eqP`, `class_eqP`, `gFsub_trans`, `gFnorms`,
  `gFchar_trans`, `gFnormal_trans`, `gFnorm_trans`, `mem2_seq1`,
  `dvdn_fact`, `prime_above`, `subKr`, `subrI`, `subIr`, `subr0_eq`,
  `divrI`, `divIr`, `divKr`, `divfI`, `divIf`, `divKf`, `impliesP`, `impliesPn`,
  `unlessL`, `unlessR`, `unless_sym`, `unlessP` (coercion), `classicW`,
  `ltr_prod_nat`
- Notation `\unless C, P`

## [1.5.0] - 2014-03-12 (ssreflect + mathcomp)

Split the archive in SSReflect and MathComp

- With this release "ssreflect" has been split into two packages.
  The Ssreflect one contains the proof language (plugin for Coq) and a
  small set of core theory libraries about boolean, natural numbers,
  sequences, decidable equality  and finite types. The Mathematical
  Components one contains advanced theory files covering a wider
  spectrum of mathematics.

- With respect to version 1.4 the proof language got a few new
  features related to forward reasoning and some bug fixes. The
  Mathematical Components library features 16 new theory files and in
  particular: some field and Galois theory, advanced character theory
  and a construction of algebraic numbers.

## [1.4.0] - 2012-09-05 (ssreflect)

- With this release the plugin code received many bug fixes and the
  existing libraries relevant updates.  This release also includes
  some new libraries on the following topics: rational numbers,
  divisibility of integers, F-algebras, finite dimensional field
  extensions and Euclidean division for polynomials over a ring.

- The release includes a major code refactoring of the plugin for Coq
  8.4.  In particular a documented ML API to access the pattern matching
  facilities of Ssreflect from third party plugins has been introduced.

## [1.3.0] - 2011-03-14 (ssreflect)

- The tactic language has been extended with several new features, inspired by
  the five years of intensive use in our project. However we have kept
  the core of the language unchanged; the new library compiles with
  Ssreflect 1.2.  Users of a Coq 8.2 toplevel statically linked with
  Ssreflect 1.2 need to comment the Declare ML Module "ssreflect" line
  in ssreflect.v to properly compile the 1.3 library.  We will continue
  supporting new releases of Coq in due course.

- The new library adds general linear algebra (matrix rank, subspaces)
  and all of the advanced finite group that was developed in the
  course of completing the Local Analysis part of the Odd Order Theorem,
  starting from the Sylow and Hall theorems and including full structure
  theorems for abelian, extremal and extraspecial groups, and general
  (modular) linear representation theory.

## [1.2.0] - 2009-08-14 (ssreflect)

No change log

## [1.1.0] - 2008-03-18 (ssreflect)

First public release
