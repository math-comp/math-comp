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
  + `rcompl x y z` is the relative complement of `z` in `[x, y]` defined for any
    `cDistrLatticeType` instance.
  + `codiff x y` is the dual sectional complement of `y` in `[x, \top]` defined
    for any `ctDistrLatticeType` instance.

### Changed

- in `bigop.v`
  + weaken hypothesis of lemma `telescope_sumn_in`

- in `zmodp.v`
  + simpler statement of `Fp_Zcast`

- in `path.v`
  + generalized `count_merge` from `eqType` to `Type`

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

### Renamed

- in `order.v` (cf. Changed section)
  + `finLatticeType` -> `finTBLatticeType`
  + `finDistrLatticeType` -> `finTBDistrLatticeType`
  + `finOrderType` -> `finTBOrderType`
  + `finCDistrLatticeType` -> `finCTBDistrLatticeType`

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

