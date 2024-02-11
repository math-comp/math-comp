# Changelog (unreleased)

To avoid having old PRs put changes into the wrong section of the CHANGELOG,
new entries now go to the present file as discussed
[here](https://github.com/math-comp/math-comp/wiki/Agenda-of-the-April-23rd-2019-meeting-9h30-to-12h30#avoiding-issues-with-changelog).

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

### Added

### Changed

- in `finset.v`
  + lemmas `big_set1E`, `big_imset_idem`.

- in `order.v`
  + lemmas `bigmin_mkcondl`, `bigmin_mkcondr`, `bigmax_mkcondl`,
    `bigmax_mkcondr`, `bigmin_le_id`, `bigmax_ge_id`, `bigmin_eq_id`,
    `bigmax_eq_id`, `bigminUl`, `bigminUr`, `bigmaxUl`, `bigmaxUr`,
    `bigminIl`, `bigminIr`, `bigmaxIl`, `bigmaxIr`, `bigminD`,
    `bigmaxD`, `bigminU`, `bigmaxU`, `bigmin_set1`, `bigmax_set1`,
    `bigmin_imset`, `bigmax_imset`.

- in `vector.v`
  + lemma `dim_matrix`

- in `order.v`
  + mixin `isPreorder`
  + structure `Preorder`
  + factories `Le_isPreorder`, `LtLe_isPreorder`, `Lt_isPreorder`
  + mixin `Preorder_isPOrder`
  + structure `FinPreorder`
  + lemma `lt_le_def`
  + definitions `PrePcan`, `PreCan`
  + mixin `isSubPreorder`
  + structure `SubPreorder`
  + factory `SubChoice_isSubPreorder`

### Changed

- Notations declared in the `fun_scope` are now declared in the
  `function_scope`.

- in `ssrfun.v`
  + `%FUN` is changed from the delimiter of `fun_scope` to that of
    `function_scope`
  + `fun_scope` is closed

- in `finset.v`
  + generalized lemmas `big_set0` and `big_set` from semigroups
    to arbitrary binary operators

- in `ssrnum.v`
  + generalize `ler_sqrt`
  + generalize `ler_psqrt` to use `nneg` instead of `pos`

- in `finset.v`
  + definitions `set_of` and `setTfor`
    (phantom trick now useless with reverse coercions)

- in `generic_quotient.v`
  + `pi_phant` -> `pi_subdef`
  + `quot_type_subdef` -> `quot_type_of`

- in `fingroup.v`
  + definitions `group_of`, `group_setT`, `setT_group`
    (phantom trick now useless with reverse coercions)

- in `perm.v`
  + definition `perm_of` (phantom trick now useless with reverse coercions)

- in `ssralg.v`
  + definitions `char`, `null_fun_head`, `in_alg_head`
    (phantom trick now useless with reverse coercions)

- in `finalg.v`
  + definitions `unit_of`
    (phantom trick now useless with reverse coercions)

- in `matrix.v`
  + definitions `GLtype`, `GLval`, `GLgroup` and `GLgroup_group`
    (phantom trick now useless with reverse coercions)
- in `alt.v`
  + definitions `Sym`, `Sym_group`, `Alt`, `Alt_group`
    (phantom trick now useless with reverse coercions)

- in `qpoly.v`
  + definitions `polyn`
    (phantom trick now useless with reverse coercions)

- in `vector.v`
  + definitions `vector_axiom_def`, `space`, `vs2mx`, `pred_of_vspace`
    (phantom trick now useless with reverse coercions)

- in `fieldext.v`
  + definition `baseField_type`
    (phantom trick now useless with reverse coercions)

- in `order.v`
  + generalized `le`, `lt`, `comparable`, `ge`, `gt`, `leif`, `le_of_leif`,
    `lteif`, `le_xor_gt`, `lt_xor_ge`, `min`, `max`, `compare`, `incompare`,
	 `arg_min`, `arg_max`, `min_fun`, `max_fun`
  + `isPOrder` is now a factory
  + generalized `geE`, `gtE`, `lexx`, `le_refl`, `ge_refl`, `le_trans`,
    `ge_trans`, `le_le_trans`, `ltxx`, `lt_irreflexive`, `ltexx`, `lt_eqF`,
	 `gt_eqF`, `ltW`, `lt_le_trans`, `lt_trans`, `le_lt_trans`, `lt_nsym`,
	 `lt_asym`, `le_gtF`, `lt_geF`, `lt_gtF`, `lt_leAnge`, `lt_le_asym`,
	 `le_lt_asym`, `le_path_min`, `lt_path_min`, `le_path_sortedE`,
	 `lt_path_sortedE`, `le_sorted_pairwise`, `lt_sorted_pairwise`,
	 `le_path_pairwise`, `lt_path_pairwise`, `lt_sorted_is_uniq_le`,
	 `le_sorted_mask`, `lt_sorted_mask`, `le_sorted_filter`, `lt_sorted_filter`,
	 `le_path_mask`, `lt_path_mask`, `le_path_filter`, `lt_path_filter`,
	 `le_sorted_ltn_nth`, `le_sorted_leq_nth`, `lt_sorted_leq_nth`,
	 `lt_sorted_ltn_nth`, `subseq_le_path`, `subseq_lt_path`, `subseq_le_sorted`,
	 `subseq_lt_sorted`, `lt_sorted_uniq`, `lt_sorted_eq`, `filter_lt_nth`,
	 `count_lt_nth`, `filter_le_nth`, `count_le_nth`, `sorted_filter_lt`,
	 `sorted_filter_le`, `nth_count_le`, `nth_count_lt`, `solt_le_id`,
	 `solt_lt_id`, `comparable_leNgt`, `comparable_ltNge`, `comparable_sym`,
	 `comparablexx`, `incomparable_eqF`, `incomparable_leF`, `incomparable_ltF`,
	 `le_comparable`, `lt_comparable`, `ge_comparable`, `gt_comparable`,
	 `leif_refl`, `eq_leif`, `eqTleif`, `lteif_trans`, `lteifxx`, `lteifNF`,
	 `lteifS`, `lteifT`, `lteifF`, `lteif_orb`, `lteif_andb`, `lteif_imply`,
	 `lteifW`, `ltrW_lteif`, `minElt`, `maxElt`, `minxx`, `maxxx`, `min_minKx`,
	 `min_minxK`, `max_maxKx`, `max_maxxK`, `comparable_minL`, `comparable_minr`,
	 `comparable_maxl`, `comparable_maxr`, `comparable_le_min`,
	 `comparable_ge_min`, `comparable_lt_min`, `comparable_gt_min`,
	 `comparable_le_max`, `comparable_ge_max`, `comparable_lt_max`,
	 `comparable_gt_max`, `comparable_minxK`, `comparable_minKx`,
	 `comparable_maxxK`, `comparable_maxKx`, comparable_lteif_minr`,
	 `comparable_lteif_minl`, `comparable_lteif_maxr`, `comparable_lteif_maxl`,
	 `comparable_minA`, `comparable_maxA`, comparable_min_maxl`,
	 `comparable_max_minr`, `comparable_arg_minP`, `comparable_arg_maxP`,
	 `comparable_bigl`, `comparable_bigr`, `bigmax_lt`, `lt_bigmin`,
	 `comparable_contraTle`, `comparable_contraTlt`, `comparable_contraPle`,
	 `comparable_contraPlt`, `comparable_contraNle`, `comparable_contraNlt`,
	 `comparable_contra_not_le`, `comparable_contra_not_lt`,
	 `comparable_contraFle`, `comparable_contraFlt`, `comparable_contra_leq_le`,
	 `comparable_contra_leq_lt`, `comparable_contra_ltn_le`,
	 `comparable_contra_ltn_lt`, `comparable_contra_le`,
	 `comparable_contra_le_lt`, `comparable_contra_lt_le`,
	 `comparable_contra_lt`, `leW_mono`, `leW_nmono`, `leW_mono_in`,
	 `leW_nmono_in`, `leEdual`, `ltEdual`
  + definitions `Pcan`, `Can`
  + generalized `order_morphism`, `isOrderMorphism`, `OrderMorphism`,
    `omorph’_le`, `omorph_lt`, `idfun_is_order_morphism`,
	 `comp_is_order_morphism`, `leEsub`, `ltEsub`, `homo_ltn_lt_in`,
	 `nondecn_inP`, `nhomo_ltn_lt_in`, `nonincn_inP`, `homo_ltn_lt`, `nondecnP`,
	 `nhomo_ltn_lt`, `nonincnP`, `leEprod`, `ltEprod`, `le_pair`, `leEprodlexi`,
	 `ltEprodlexi`, `lexi_pair`, `ltxi_pair`, `sub_prod_lexi`, `leEseq`, `le0s`,
	 `les0`, `le_cons`, `leEseqlexi`, `ltEseqlexi`, `lexi0s`, `lexis0`, `ltxi0s`,
	 `ltxis0`, `lexi_cons`, `ltxi_cons`, `lexi_lehead`, `ltxi_lehead`,
	 `eqhead_lexiE`, `eqhead_ltxiE`, `sub_seqprod_lexi`, `leEtprod`,
	 `sub_tprod_lexi`

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

### Infrastructure

### Misc

