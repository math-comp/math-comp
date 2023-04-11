### Added

- in `bigop.v`
  + structures `SemiGroup.law` and `SemiGroup.com_law`

### Changed

- in `bigop.v`
  + structures `Monoid.law`, `Monoid.com_law`, `Monoid.mul_law` and
    `Monoid.add_law` ported to HB

### Renamed

### Removed

- in `bigop.v`
  + definition `Monoid.clone_law`, use `Monoid.Law.clone`
  + definition `Monoid.clone_com_law`, use `Monoid.ComLaw.clone`
  + definition `Monoid.clone_mul_law`, use `Monoid.MulLaw.clone`
  + definition `Monoid.clone_add_law`, use `Monoid.AddLaw.clone`
  + notation `[law of f]`, use `Monoid.Law.clone f _`
  + notation `[com_law of f]`, use `f : Monoid.ComLaw.clone f _`
  + notation `[mul_law of f]`, use `f : Monoid.MulLaw.clone f _`
  + notation `[add_law of f]`, use `f : Monoid.AddLaw.clone f _`
  + definitions `andb_monoid` and `andb_comoid`, use `andb : Monoid.com_law`
  + definitions `andb_muloid`
  + definitions `orb_monoid` and `orb_comoid`, use `orb : Monoid.com_law`
  + definitions `orb_muloid`
  + definitions `addb_monoid` and `addb_comoid`, use `addb : Monoid.com_law`
  + definitions `orb_addoid`, `andb_addoid` and `addb_addoid`
  + definitions `addn_monoid` and `addn_comoid`, use `addn : Monoid.com_law`
  + definitions `muln_monoid` and `muln_comoid`, use `muln : Monoid.com_law`
  + definitions `addn_addoid`
  + definitions `maxn_monoid` and `maxn_comoid`, use `maxn : Monoid.com_law`
  + definitions `maxn_addoid`
  + definitions `gcdn_monoid` and `gcdn_comoid`, use `gcdn : Monoid.com_law`
  + definitions `gcdn_addoid`
  + definitions `lcmn_monoid` and `lcmn_comoid`, use `lcmn : Monoid.com_law`
  + definitions `lcmn_addoid`
  + definitions `cat_monoid`, use `cat : Monoid.law`
  + lemma `big_undup_AC`, use `big_undup`
  + lemma `perm_big_AC`, use `perm_big`
  + lemma `big_enum_cond_AC`, use `big_enum_cond`
  + lemma `big_enum_AC`, use `big_enum`
  + lemma `big_uniq_AC`, use `big_uniq`
  + lemma `bigD1_AC`, use `bigD1`
  + lemma `bigD1_seq_AC`, use `bigD1_seq`
  + lemma `big_image_cond_AC`, use `big_image_cond`
  + lemma `big_image_AC`, use `big_image`
  + lemma `reindex_omap_AC`, use `reindex_omap`
  + lemma `reindex_onto_AC`, use `reindex_onto`
  + lemma `reindex_AC`, use `reindex`
  + lemma `reindex_inj_AC`, use `reindex_inj`
  + lemma `bigD1_ord_AC`, use `bigD1_ord`
  + lemma `big_enum_val_cond_AC`, use `big_enum_val_cond`
  + lemma `big_enum_rank_cond_AC`, use `big_enum_rank_cond`
  + lemma `big_nat_rev_AC`, use `big_nat_rev`
  + lemma `big_rev_mkord_AC`, use `big_rev_mkord`

### Deprecated

