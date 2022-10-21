# Changelog (unreleased)

To avoid having old PRs put changes into the wrong section of the CHANGELOG,
new entries now go to the present file as discussed
[here](https://github.com/math-comp/math-comp/wiki/Agenda-of-the-April-23rd-2019-meeting-9h30-to-12h30#avoiding-issues-with-changelog).

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

### Added

- in `path.v` 
  + lemmas `prefix_path`, `prefix_sorted`, `infix_sorted`, `suffix_sorted` 

- in `poly.v`, added lemmas `comm_polyD`, `comm_polyM` and `comm_poly_exp`.

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

### Changed

- in `poly.v`:
  + generalize `eq_poly`

### Renamed

### Removed

### Infrastructure

### Misc

