- new file `interval_inference.v`
  added to `all_algebra.v`, this can solve automatically a few more
  goals, making some proofs fail (with subgoals no longer existing)
  (backported from https://github.com/math-comp/analysis/pull/1410 )
  ([#1352](https://github.com/math-comp/math-comp/pull/1352),
  by Pierre Roux).

- in `interval_inference.v`
  + definitions `map_iv_bound`, `map_itv`, `Itv.t`, `Itv.sub`,
    `Itv.spec`, `Itv.mk`, `Itv.from`, `fromP`, `Itv.num_sem`,
    `Itv.nat_sem`, `Itv.posnum`, `Itv.nonneg`, `Itv.real1`,
    `Itv.real2`, `empty_itv`, `widen_itv`, `ItvNum`, `ItvReal`,
    `Itv01`, `PosNum`, `NngNum`, `posnum_spec`, `nonneg_spec`
  + module `IntItv` with
    * definitions `opp_bound`, `opp`, `add_boundl`, `add_boundr`,
      `add`, `signb`, `sign_boundl`, `sign_boundr`, `signi`, `sign`,
      `mul_boundl`, `mul_boundr`, `mul`, `min`, `max`,
      `keep_nonneg_bound`, `keep_pos_bound`, `keep_nonpos_bound`,
      `keep_neg_bound`, `inv`, `exprn_le1_bound`, `exprn`,
      `keep_sign`, `keep_nonpos`, `keep_nonneg`
    * lemmas `opp_bound_ge0`, `opp_bound_gt0`, `mul_boundrC`,
      `mul_boundr_gt0`
  + module `Instances` with
    * definitions `sign_spec`, `Instances.sqrt_itv`,
      `Instances.sqrtC_itv`
    * lemmas `num_spec_zero`, `num_spec_one`, `opp_boundr`,
      `opp_boundl`, `num_spec_opp`, `num_itv_add_boundl`,
      `num_itv_add_boundr`, `num_spec_add`, `signP`,
      `num_itv_mul_boundl`, `num_itv_mul_boundr`,
      `BRight_le_mul_boundr`, `comparable_num_itv_bound`,
      `num_itv_bound_min`, `num_itv_bound_max`, `num_spec_mul`,
      `num_spec_min`, `num_spec_max`, `nat_num_spec`,
      `num_spec_natmul`, `num_spec_int`, `num_spec_intmul`,
      `num_itv_bound_keep_pos`, `num_itv_bound_keep_neg`,
      `num_spec_inv`, `num_itv_bound_exprn_le1`, `num_spec_exprn`,
      `num_spec_norm`, `num_spec_sqrt`, `num_spec_sqrtC`,
      `nat_spec_zero`, `nat_spec_succ`, `nat_spec_add`,
      `nat_spec_double`, `nat_spec_mul`, `nat_spec_exp`,
      `nat_spec_min`, `nat_spec_max`, `num_spec_Posz`, `num_spec_Negz`
    * canonical instances `zero_inum`, `one_inum`, `opp_inum`,
      `add_inum`, `mul_inum`, `min_typ_inum`, `max_typ_inum`,
      `num_min_max_typ`, `natmul_inum`, `intmul_inum`, `inv_inum`,
      `exprn_inum`, `norm_inum`, `sqrt_inum`, `sqrtC_inum`,
      `zeron_inum`, `succn_inum`, `addn_inum`, `double_inum`,
      `muln_inum`, `expn_inum`, `minn_inum`, `maxn_inum`,
      `nat_min_max_typ`, `Posz_inum`, `Negz_inum`
  + lemmas `map_itv_bound_comp`, `map_itv_comp`, `Itv.spec_real1`,
    `Itv.spec_real2`, `itv_le_total_subproof`,
    `TypInstances.top_typ_spec`, `TypInstances.real_domain_typ_spec`,
    `TypInstances.real_field_typ_spec`, `TypInstances.nat_typ_spec`,
    `TypInstances.typ_inum_spec`, `le_num_itv_bound`,
    `num_itv_bound_le_BLeft`, `BRight_le_num_itv_bound`,
    `num_spec_sub`, `bottom`, `gt0`, `le0F`, `lt0`, `ge0F`, `ge0`,
    `lt0F`, `le0`, `gt0F`, `cmp0`, `neq0`, `eq0F`, `lt1`, `ge1F`,
    `le1`, `gt1F`, `widen_itv_subproof`, `widen_itvE`, `posE`, `nngE`,
    `num_eq`, `num_le`, `num_lt`, `num_min`, `num_max`, `num_abs_eq0`,
    `num_le_max`, `num_ge_max`, `num_le_min`, `num_ge_min`,
    `num_lt_max`, `num_gt_max`, `num_lt_min`, `num_gt_min`,
    `num_abs_le`, `num_abs_lt`, `itvnum_subdef`, `itvreal_subdef`,
    `itv01_subdef`, `Itv01.`, `posnum_subdef`, `nngnum_subdef`,
    `posnumP`, `nonnegP`
  + canonical instances `TypInstances.top_typ`,
    `TypInstances.real_domain_typ`, `TypInstances.real_field`,
    `TypInstances.nat_typ`, `TypInstances.typ_inum`
  + notations `{itv R & i}`, `{i01 R}`, `{posnum R}`, `{nonneg R}`,
    `x%:itv`, `[itv of x]`, `num`, `x%:inum`, `x%:num`, `x%:posnum`,
    `x%:nngnum`, `unify_itv`, `[gt0 of x]`, `[lt0 of x]`,
    `[ge0 of x]`, `[le0 of x]`, `[cmp0 of x]`, `[neq0 of x]`,
    `x%:i01`, `x%:pos`, `x%:nng`
    (backported from https://github.com/math-comp/analysis/pull/1410 )
    ([#1352](https://github.com/math-comp/math-comp/pull/1352),
    by Pierre Roux).
