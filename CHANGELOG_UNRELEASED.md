# Changelog (unreleased)

To avoid having old PRs put changes into the wrong section of the CHANGELOG,
new entries now go to the present file as discussed
[here](https://github.com/math-comp/math-comp/wiki/Agenda-of-the-April-23rd-2019-meeting-9h30-to-12h30#avoiding-issues-with-changelog).

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

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
  structure, and lemmas `permX_fix`, `imset_perm1`, `permS0`, `permS1`,
  `permSleq1` `cast_perm_id`, `cast_ord_permE`, `cast_permE`,
  `cast_perm_comp`, `cast_permK`, `cast_permKV`, `cast_perm_inj`,
  `cast_perm_sym`,`cast_perm_morphM`, and `isom_cast_perm` in `perm`
  and `restr_perm_commute` in `action`.

- Added `card_porbit_neq0`, `porbitP`, and `porbitPmin` in `perm`

- Added definition `Sym` with a group set canonical structure and
  lemmas `card_Sn` and `card_Sym` in `perm` and `SymE` in `action`

- Added lemma `ord1` in `fintype`, it is the same as `zmodp.ord1`,
  except `fintype.ord1` does not rely on `'I_n` zmodType structure.

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
  + In the development process of this version of Mathematical Components, the
    ordering of arguments of comparison predicates `lcomparableP`,
    `(lcomparable_)ltgtP`, `(lcomparable_)leP`, and `(lcomparable_)ltP` in
    `order.v` has been changed as follows. This is a potential source of
    incompatibilities.
    * before the change:
      ```
      lcomparableP x y : incomparel x y
        (y == x) (x == y) (x >= y) (x <= y) (x > y) (x < y)
        (y >=< x) (x >=< y) (y `&` x) (x `&` y) (y `|` x) (x `|` y).
      ltgtP x y : comparel x y
        (y == x) (x == y) (x >= y) (x <= y) (x > y) (x < y)
        (y `&` x) (x `&` y) (y `|` x) (x `|` y).
      leP x y :
        lel_xor_gt x y (x <= y) (y < x) (y `&` x) (x `&` y) (y `|` x) (x `|` y).
      ltP x y :
        ltl_xor_ge x y (y <= x) (x < y) (y `&` x) (x `&` y) (y `|` x) (x `|` y).
      ```
    * after the change:
      ```
      lcomparableP x y : incomparel x y
        (y `&` x) (x `&` y) (y `|` x) (x `|` y)
        (y == x) (x == y) (x >= y) (x <= y) (x > y) (x < y) (y >=< x) (x >=< y).
      ltgtP x y : comparel x y
        (y `&` x) (x `&` y) (y `|` x) (x `|` y)
        (y == x) (x == y) (x >= y) (x <= y) (x > y) (x < y).
      leP x y :
        lel_xor_gt x y (y `&` x) (x `&` y) (y `|` x) (x `|` y) (x <= y) (y < x).
      ltP x y :
        ltl_xor_ge x y (y `&` x) (x `&` y) (y `|` x) (x `|` y) (y <= x) (x < y).
      ```

- Extended comparison predicates `leqP`, `ltnP`, and `ltngtP` in ssrnat to
  allow case analysis on `minn` and `maxn`.
  + The compatibility layer for the version 1.10 is provided as the
    `ssrnat.mc_1_10` module. One may compile proofs compatible with the version
    1.10 in newer versions by using this module.

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
  + `homo_inj_lt(_in)` -> `inj_homo_ltn(in)`
  + `(inc|dec)r(_in)` -> `(inc|dev)n(_in)`

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

### Infrastructure

### Misc
