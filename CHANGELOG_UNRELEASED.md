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

- in `ssrbool.v`
  + lemmas `classic_sigW`, `classic_ex`

### Changed

- in `bigop.v`
  + weaken hypothesis of lemma `telescope_sumn_in`

- in `zmodp.v`
  + simpler statement of `Fp_Zcast`

- in `path.v`
  + generalized `count_merge` from `eqType` to `Type`

- in `order.v`
  + `order_morphism` changed to `homo` from `mono` and renamed `nondecreasing`

### Renamed

- in `binomial.v`
  + `triangular_sum` -> `bin2_sum`

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

- in `binomial.v`
  + lemma `textbook_triangular_sum`

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

### Infrastructure

### Misc

