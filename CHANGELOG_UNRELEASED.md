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
    `big_rcons`, `big_only1`, `big_mknat`

- in `eqtype.v`
  + definition `dfwith`
  + lemmas `dfwith_in`, `dfwith_out`, `dfwithP`

- in `seq.v`
  + lemmas `has_undup`, `all_undup`

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
  + lemmas `count_sort`, `sorted_cat_rcons`

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

- in `ssrbool.v`
  + lemmas `classic_sigW`, `classic_ex`
- in `intdiv.v`
  + lemmas `dvdz_charf`, `eisenstein`

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

### Changed

- in `zmodp.v`
  + simpler statement of `Fp_Zcast`

### Renamed

### Removed

### Deprecated

### Infrastructure

### Misc

