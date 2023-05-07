# Changelog (unreleased)

To avoid having old PRs put changes into the wrong section of the CHANGELOG,
new entries now go to the present file as discussed
[here](https://github.com/math-comp/math-comp/wiki/Agenda-of-the-April-23rd-2019-meeting-9h30-to-12h30#avoiding-issues-with-changelog).

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

### Added

- in `ssrnum.v`
  + structures `porderZmodType`

- in `ssralg.v`
  + structure `nmodType` (aka Monoid on a choiceType), `semiRingType`,
    `comSemiRingType`, `subNmodType`, `subZmodType`, `subSemiRingType`,
    `subComSemiRingType`, `subRingType`, `subComRingType`, `subLmodType`,
    `subLalgType`, `subAlgType`, `subUnitRingType`, `subComUnitRingType`,
    `subIdomainType`, `subField`
  + predicate `semi_additive`
  + predicate `multiplicative`
  + morphism `semiring2Closed`
  + morphism `semiringClosed`

- in `finalg.v`
  + structures `finComSemiRingType`, `finSemiRingType` and `finZsemimodType`

- in `countalg.v`
  + structures `countComSemiRingType`, `countSemiRingType` and
    `countZsemimodType`

- in `order.v`
  + structures `OrderMorphism`, `MeetLatticeMorphism`,
      `JoinLatticeMorphism`, `LatticeMorphism`, `BLatticeMorphism`,
      `TLatticeMorphism`, `TBLatticeMorphism`, `MeetLatticeClosed`,
      `JoinLatticeClosed`, `LatticeClosed`, `BLatticeClosed`,
      `BJoinLatticeClosed`, `TLatticeClosed`, `TMeetLatticeClosed`,
      `TBLatticeClosed`, `SubPOrder`, `SubPOrderLattice`,
      `SubPOrderBLattice`, `SubPOrderTLattice`, `SubPOrderTBLattice`,
      `MeetSubLattice`, `MeetSubBLattice`, `MeetSubTLattice`,
      `MeetSubTBLattice`, `JoinSubLattice`, `JoinSubBLattice`,
      `JoinSubTLattice`, `JoinSubTBLattice`, `SubLattice`,
      `SubBLattice`, `SubTLattice`, `SubTBLattice`, `BJoinSubLattice`,
      `BJoinSubTLattice`, `BSubLattice`, `BSubTLattice`,
      `TMeetSubLattice`, `TMeetSubBLattice`, `TSubLattice`,
      `TSubBLattice`, `TBSubLattice`, `SubOrder`
  + predicate `meet_morphism`, `join_morphism`, `meet_closed`,
    `join_closed`

- in `eqtype.v`
  + structure `subEqType`
  + notation `\val`

- in `choice.v`
  + notation `subChoiceType`, structure `SubChoice`

- in `bigop.v`
  + structures `SemiGroup.law` and `SemiGroup.com_law`

- in `perm.v`
  + lemmas `perm_on_id`, `perm_onC`, `tperm_on`

- in `seq.v`
  + lemmas `find_pred0`, `find_predT`

- in `bigop.v`
  + lemma `big_if`

- in `seq.v`
  + lemmas `sumn_ncons`, `sumn_set_nth`, `sumn_set_nth_ltn`,
    `sumn_set_nth0`

- in `finset.v`
  + lemma `bigA_distr`

- in `poly.v`
  + lemmas `coef_prod_XsubC`, `coefPn_prod_XsubC`, `coef0_prod_XsubC`,
	 `polyOver_mulr_2closed`

- in `ssralg.v`
  + `bool` is now canonically a `fieldType` with additive law `addb` and
    multiplicative law `andb`

- in `finalg.v`
  + `bool` is now canonically a `finFieldType` and a `decFieldType`.

- in `ssrnat.v`
  + lemmas `addnCBA`, `addnBr_leq`, `addnBl_leq`, `subnDAC`,
    `subnCBA`, `subnBr_leq`, `subnBl_leq`, `subnBAC`, `subDnAC`,
    `subDnCA`, `subDnCAC`, `addnBC`, `addnCB`, `addBnAC`, `addBnCAC`,
    `addBnA`, `subBnAC`, `eqn_sub2lE`, `eqn_sub2rE`

- in `ssrfun.v`
  + lemmas `inj_omap`, `omap_id`, `eq_omap`, `omapK`

### Changed

- in `galois.v`
  + structure `splittingFieldType` ported to HB

- in `finfield.v`
  + structure `fieldExtType` ported to HB
  + module `FinVector` removed in favor of alias (feather factory)
    `finvect_type`

- in `fieldext.v`
  + structure `fieldExtType` ported to HB

- in `falgebra.v`
  + structure `falgType` ported to HB

- in `closed_field.v`
  + notation `closed_field_QEMixin`, use `Field_isAlgClosed.Build`

- in `ssrnum.v`
  + structures `normedZmodType`, `numDomainType`,
    `numFieldType`, `numFieldType`, `numClosedFieldType`, `realDomainType`,
    `realFieldType`, `archiFieldType`, `rcfType` ported to HB

- in `ssralg.v`
  + structures `zmodType`, `ringType`, `lmodType`, `lalgType`, `comRingType`,
    `algType`, `comAlgType`, `unitRingType`, `comUnitRingType`, `unitAlgType`,
    `comUnitAlgType`, `idomainType`, `fieldType`, `decFieldType`,
    `closedFieldType` ported to HB

  + morphisms `additive` and `rmorphism` ported to HB and generalized to
    `nmodType` and `semiRingType` respectively.

  + morphisms `linear` and `lrmorphism` ported to HB

  + predicates `opprClosed`, `addrClosed`, `zmodClosed`, `mulr2Closed`,
    `mulrClosed`, `smulClosed`, `subringClosed`, `divClosed`, `sdivClosed`,
    `submodClosed`, `subalgClosed`, `divringClosed`, `divalgClosed` ported to HB

- in `ring_quotient.v`
  + structures `zmodQuotType`, `ringQuotType` and `unitRingQuotType` have been ported to HB.
  + structures `proper_ideal`, `idealr` and `primeIdealr` have been ported to HB.

- in `finalg.v`
  + structures `finZmodType`, `finRingType`, `finComRingType`,
    `finUnitRingType`, `finComUnitRingType`, `finIdomType`, `finFieldType`,
    `finLmodType`, `finLalgType`, `finAlgType`, `finUnitAlgType` ported to HB

- in `countalg.v`
  + structures `countZmodType`, `countRingType`, `countComRingType`,
    `countUnitRingType`, `countComUnitRingType`, `countIdomainType`,
    `countFieldType`, `countDecFieldType`, `countClosedFieldType` ported to HB

- in `fingroup.v`
  + structures `baseFinGroupType` and `finGroupType` ported to HB

- in `order.v`
  + the structures `POrder`, `Lattice`, `BLattice`, `TLattice`,
    `TBLattice`, `DistrLattice`, `BDistrLattice`, `TBDistrLattice`,
    `CBDistrLattice`, `CTBDDistrLattice`, `Total`, `FinPOrder`, `FinLattice`,
    `FinDistrLattice`, `FinCDistrLattice`, `FinTotal`
  + `PcanPOrderMixin` is replaced by `Order.PcanPartial`
  + `CanPOrderMixin` is replaced by `Order.CanPartial`
  + `MonoTotalMixin` is replaced by `MonoTotal`
  + `IsoLatticeMixin` is replaced by `Order.IsoLattice`

- in `generic_quotient.v`,
  + structures quotType and eqQuotType ported to HB

- in `fintype.v`
  + structures `finType` and `subFinType` ported to HB

- in `eqtype.v`
  + structures `eqType` and `subType` ported to HB

- in `choice.v`
  + `[choiceMixin of T by <:]` becomes `[Choice of T by <:]`
  + `[countMixin of T by <:]` becomes `[Countable of T by <:]`
  + `Choice.mixin_of` becomes `hasChoice`
  + `Countable.mixin_of` becomes `Choice_isCountable`
  + `ChoiceMixin` becomes `hasChoice.Build`
  + `CountMixin` becomes `Choice_isCountable.Build`
  + `CountChoiceMixin` is subsumed by `Equality_isCountable.Build`
    (instead of two successive calls to `CountChoiceMixin` and
    `CountMixin`, only one to `Equality_isCountable.Build` is necessary)
  + `CanChoiceMixin` -> use `Choice.copy` with `can_type` or `CanHasChoice`
  + `PcanChoiceMixin` -> use `Choice.copy` with `pcan_type` or `PCanHasChoice`
  + `CanCountMixin` -> use `Countable.copy` with `can_type` or `CanIsCountable`
  + `PcanCountMixin` -> use `Countable.copy` with `pcan_type` or `PCanIsCountable`

- in `bigop.v`
  + structures `Monoid.law`, `Monoid.com_law`, `Monoid.mul_law` and
    `Monoid.add_law` ported to HB

- in `order.v`
  + fix lemmas `eq_bigmax` and `eq_bigmin` to respect given predicates

- in `order.v`
  + fix `\meet^p_` and `\join^p_` notations
  + fix the scope of `n.-tuplelexi` notations

- in `intdiv.v`
  + `zcontents` is now of type `{poly int} -> int`
  + `divz` is now of type `int -> int -> int`

- in `order.v`
  + fix the definition of `max_fun` (notation `\max`)
    which was equal to `min_fun`

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

### Renamed

- in `galois.v`
  + definition `SplittingField.axiom` -> `splitting_field_axiom`
  + notation `SplittingFieldType`, use `FieldExt_isSplittingfield.Build`

- in `falgebra.v`
  + strcture `FalgType` -> `falgType`
  + notation `FalgUnitRingType`, use `Algebra_isFalgebra.Build`

- in `ssrnum.v`
  + notation `NormedZmodType`, use `Zmodule_isNormed.Build`
  + notation `NumDomainType`, use `isNumRing.Build`
  + notation `NumClosedFieldType`, use `NumField_isImaginary.Build`
  + notation `ArchiFieldType`, use `RealField_isArchimedean.Build`
  + notation `RcfType`, use `RealField_isClosed.Build`

- in `ssralg.v`
  + `*Pred` -> `*Closed`
  + notation `[zmodMixin of M by <:]`, use `[SubChoice_isSubZmodule of U by <:]`
  + notation `[ringMixin of R by <:]`, use `[SubZmodule_isSubRing of U by <:]`
  + notation `[comRingMixin of R by <:]`, use `[SubZmodule_isSubComRing of U by <:]`
  + notation `[unitRingMixin of R by <:]`, use `[SubRing_isSubUnitRing of U by <:]`
  + notation `[comUnitRingMixin of R by <:]`, use `[SubChoice_isSubComUnitRing of U by <:]`
  + notation `[idomainMixin of R by <:]`, use `[SubComUnitRing_isSubIntegralDomain of U by <:]`
  + notation `[fieldMixin of R by <:]`, use `[SubIntegralDomain_isSubField of U by <:]`
  + notation `[lmodMixin of R by <:]`, use `[SubZmodule_isSubLmodule of U by <:]`
  + notation `[lalgMixin of R by <:]`, use `[SubRing_SubLmodule_isSubLalgebra of U by <:]`
  + notation `[algMixin of R by <:]`, use `[SubLalgebra_isSubAlgebra of U by <:]`

- in `order.v`:
  + `[porderMixin of T by <:]` -> `[POrder of T by <:]`
  + `[totalOrderMixin of T by <:]` -> `[Order of T by <:]`
  + `sub` -> `diff`
  + `subKI` -> `diffKI`
  + `subIK` -> `diffIK`
  + `subxx` -> `diffxx`
  + `subKU` -> `diffKU`
  + `subUK` -> `diffUK`
  + `subUx` -> `diffUx`
  + `sub_eq0` -> `diff_eq0`
  + `meet_eq0E_sub` -> `meet_eq0E_diff`
  + `eq_sub` -> `eq_diff`
  + `subxU` -> `diffxU`
  + `subx0` -> `diffx0`
  + `sub0x` -> `diff0x`
  + `subIx` -> `diffIx`
  + `subxI` -> `diffxI`
  + `subBx` -> `diffBx`
  + `subxB` -> `diffxB`
  + `disj_subl` -> `disj_diffl`
  + `disj_subr` -> `disj_diffr`
  + `sub1x` -> `diff1x`
  + `subE` -> `diffE`
  + `tnth_sub` -> `tnth_diff`
  + `subEtprod` -> `diffEtprod`

- in `choice.v`
  + `choiceMixin` -> `hasChoice`
  + `sub_choiceMixin` -> `sub_hasChoice`
  + `seq_choiceMixin` -> `seq_hasChoice`
  + `tagged_choiceMixin` -> `tagged_hasChoice`
  + `nat_choiceMixin` -> `nat_hasChoice`

- in `ssralg.v`:
  + `rmorphX` -> `rmorphXn`
- in `fraction.v`:
  + `tofracX` -> `tofracXn`
- in `mxrepresentation.v`:
  + `mxval_grootX` -> `mxval_grootXn`
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

### Removed

- in `vector.v`
  + notation `VectMixin` and `VectType`, use `Lmodule_hasFinDim.Build`

- in `ssralg.v`
  + notation `ZmodType`, use `isZmodule.Build`
  + notation `RingType`, use `Zmodule_isRing.Build`
  + notation `ComRingType`, use `hasCommutativeMul.Build`
  + notation `UnitRingType`, use `Ring_hasMulInverse.Build`
  + notation `UnitRingType`, use `Ring_hasMulInverse.Build`
  + notation `ComUnitRingMixin`, use `ComRing_hasMulInverse.Build`
  + notation `IdomainType`, use `ComUnitRing_isIntegral.Build`
  + notation `FieldMixin`, use `UnitRing_isField.Build`
  + notation `FieldType`, use `UnitRing_isField.Build`
  + notation `FieldUnitMixin`, use `ComRing_isField.Build`
  + notation `FieldIdomainMixin`
  + notation `GRing.Field.IdomainType`, use `ComRing_isField.Build`
  + notation `DecFieldMixin`, use `Field_isDecField.Build`
  + notation `QEdecFieldMixin`, use `Field_QE_isDecField.Build`
  + notation `ClosedFieldType`, use `DecField_isAlgClosed.Build`
  + notation `LmodMixin`, use `Zmodule_isLmodule.Build`
  + notation `LmodType`, use `Zmodule_isLmodule.Build`
  + notation `LalgType`, use `Lmodule_isLalgebra.Build`
  + notation `AlgType`, use `Lalgebra_isAlgebra.Build`
  + notation `ComAlgType`, use `Lalgebra_isAlgebra.Build`
  + module `GRing.DefaultPred`
  + notation `Additive`, use `isAdditive.Build`
  + notation `RMorphism`, use `Additive_isMultiplicative.Build`
  + notation `AddRMorphism`, use `Additive_isMultiplicative.Build`
  + notation `Linear`, use `isScalable.Build`
  + notation `AddLinear`, use `isScalable.Build`
  + notation `LRMorphism`, use `isScalable.Build`
  + notation `AddLRMorphism`, use `isScalable.Build`

- in `ring_quotient.v`
  + removed `MkIdeal` and `MkPrimeIdeal` in favor of generic HB commands.

- in `finalg.v`
  + notation `[baseFinGroupType of R for +%R]`

- in `eqtype.v`
  + definitions `tuple_eqMixin`, `tuple_choiceMixin`,
    `tuple_countMixin`, `tuple_finMixin`, `bseq_eqMixin`,
    `bseq_choiceMixin`, `bseq_countMixin`, `bseq_finMixin`

- in `order.v`:
  + `LtOrderMixin` (see factory `LtOrder`)
  + `OrderType`
  + `POrderType`
  + `LatticeType`
  + `BLatticeType`
  + `TBLatticeType`
  + `DistrLatticeType`
  + `CBDistrLatticeType`
  + `CTBDistrLatticeType`
  + factory `lePOrderMixin` (use factory `isLePOrdered` instead)
  + factory `ltPOrderMixin` (use factory `isLtPOrdered` instead)
  + factory `latticeMixin` (use mixin `POrder_isLattice` instead)
  + factory `distrLatticeMixin` (use mixin `Lattice_MeetIsDistributive` instead)
  + factory `distrLatticePOrderMixin` (use factory `POrder_isMeetDistrLattice` instead)
  + factory `meetJoinMixin` (use factory `isMeetJoinDistrLattice` instead)
  + factory `meetJoinLeMixin` (use factory `POrder_isMeetJoinLattice` instead)
  + factory `leOrderMixin` (use factory `isOrdered` instead)
  + factory `ltOrderMixin` (use factory `LtOrder` instead)
  + factory `meetJoinLeMixin` (use factory `Porder_isMeetJoinLattice` instead)
  + factory `totalPOrderMixin` (use factory `POrder_isTotal` instead)
  + factory `totalLatticeMixin` (use factory `Lattice_isTotal` instead)
  + factory `totalOrderMixin` (use factory `DistrLattice_isTotal` instead)
  + factory `bottomMixin` (use mixin `hasBottom` instead)
  + factory `topMixin` (use mixin `hasTop` instead)
  + factory `cbDistrLatticeMixin` (use mixin `hasSub` instead)
  + factory `ctbDistrLatticeMixin` (use mixin `hasCompl` instead)
  + `DistrLatticeOfChoiceType` (use `isMeetJoinDistrLattice.Build` and `HB.pack` instead),
    `DistrLatticeOfPOrderType` (use `POrder_isMeetDistrLattice.Build`)
    `OrderOfChoiceType` (use `isOrdered.Build`),
    `OrderOfPOrder` (use `POrder_isTotal.Build`),
    `OrderOfLattice` (use `Lattice_isTotal.Build`)

- in `generic_quotient.v`,
  + notation `QuotClass`, use `isQuotient.Build`
  + notation `EqQuotType`, use `isEqQuotient.Build`

- in `fintype.v`
  + definition `adhoc_seq_sub_choiceMixin`

- in `eqtype.v`
  + notation `EqMixin`, use `hasDecEq.Build`
  + notation `[eqMixin of T]`, use `Equality.on T`
  + `unit_eqMixin` and `unit_eqType`, use `unit : eqType`
  + `bool_eqMixin` and `bool_eqType`, use `bool : eqType`
  + `void_eqMixin` and `void_eqType`, use `void : eqType`
  + `sig_eqMixin` and `sig_eqType`, use `{x | P x} : eqType`
  + `prod_eqMixin` and `prod_eqType`, use `(T1 * T2)%type : eqType`
  + `option_eqMixin` and `option_eqType`, use `option T : eqType`
  + `tag_eqMixin` and `tag_eqType`, use `{i : I & T_ i} : eqType`
  + `sum_eqMixin` and `sum_eqType`, use `(T1 + T2)%type : eqType`
  + definition `clone_subType`, use `SubType.clone`
  + notation `[subType for v]`, use `[isSub for v]`
  + notation `[subType for v by rec]`, use `[isSub for v by rec]`
  + notation `[subType of T for v]`, use `[isSub of T for v]`
  + notation `[subType of T]`, use `SubType.clone T _`
  + definition `NewType`
  + notation `[newType for v]`, use `[isNew for v]`
  + notation `[newType for v by rec]`, use `[isNew for v by rec]`
  + definition `sig_subType`, use `sig P : subType`
  + definitions `sub_eqMixin`, `sub_eqType` and `SubEqMixin`, use alias `sub_type`
  + notation `EqType`

- in `choice.v`
  + `ChoiceType`
  + `CountType`
  + `sub_choiceClass`, `sub_choiceType`
  + `seq_choiceType` (use `seq _ : choiceType` instead, the same
     applies for other `*_choiceType`'s)
  + `tagged_choiceType`
  + `nat_choiceType`
  + `bool_choiceMixin`, `bool_choiceType`, `bitseq_choiceType`,
    `unit_choiceMixin`, `unit_choiceType`, `void_choiceMixin`,
    `void_choiceType`, `option_choiceMixin`, `option_choiceType`,
    `sig_choiceMixin`, `sig_choiceType`, `prod_choiceMixin`,
    `prod_choiceType`, `sum_choiceMixin`, `sum_choiceType`,
    `tree_choiceMixin`, `tree_choiceType`
  + `sub_countMixin`
  + `seq_countMixin`, `seq_countType`,
    `tag_countMixin`, `tag_countType`,
    `nat_countMixin`, `nat_countType`,
    `bool_countMixin`, `bool_countType`,
    `bitseq_countType`,
    `unit_countMixin`, `unit_countType`,
    `void_countMixin`, `void_countType`,
    `option_countMixin`, `option_countType`,
    `sig_countMixin`, `sig_countType`,
    `sig_subCountType`,
    `prod_countMixin`, `prod_countType`,
    `sum_countMixin`, `sum_countType`,
    `tree_countMixin`, `tree_countType`
  + `CountChoiceMixin`

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

- in `galois.v`
  + notation `[splittingFieldType F of L for K]`, use `SplittingField.clone F L K`
  + notation `[splittingFieldType F of L]`, use `SplittingField.clone F L _` or
    `L : splittingFieldType F`

- in `fieldext.v`
  + notation `[fieldExtType F of L for K]`, use `FieldExt.clone F L K`
  + notation `[fieldExtType F of L]`, use `FieldExt.clone F L _` or `L : fieldExtType F`

- in `falgebra.v`
  + notation `[FalgType F of L for L']`, use `Falgebra.clone F L L'`
  + notation `[FalgType F of L]`, use `Falgebra.clone F L _` or `L : FalgType F`

- in `vector.v`
  + notation `[vectType R of T for cT]`, use `Vector.clone T cT`
  + notation `[vectType R of T]`, use `Vector.clone T _` or `T : vectType R`

- in `ssrnum.v`
  + notation `[numDomainType of T for cT]`, use `Num.NumDomain.clone T cT`
  + notation `[numDomainType of T]`, use `Num.NumDomain.clone T _` or `T : numDomainType`
  + notation `[numFieldType of T]`, use `Num.NumField.clone T _` or `T : numFieldType`
  + notation `[numClosedFieldType of T for cT]`, use `Num.ClosedField.clone T cT`
  + notation `[numClosedFieldType of T]`, use `Num.ClosedField.clone T _` or `T : numClosedFieldType`
  + notation `[realDomainType of T]`, use `Num.RealDomain.clone T _` or `T : realDomainType`
  + notation `[realFieldType of T]`, use `Num.RealField.clone T _` or `T : realFieldType`
  + notation `[archiFieldType of T for cT]`, use `Num.ArchimedeanField.clone T cT`
  + notation `[archiFieldType of T]`, use `Num.ArchimedeanField.clone T _` or `T : archiFieldType`
  + notation `[rcfType of T for cT]`, use `Num.RealClosedField.clone T cT`
  + notation `[rcfType of T]`, use `Num.RealClosedField.clone T _` or `T : rcfType`

- in `ssralg.v`
  + notation `[nmodType of T for cT]`, use `GRing.Nmodule.clone T cT`
  + notation `[nmodType of T]`, use `GRing.Nmodule.clone T _` or `T : nmodType`
  + notation `[zmodType of T for cT]`, use `GRing.Zmodule.clone T cT`
  + notation `[zmodType of T]`, use `GRing.Zmodule.clone T _` or `T : zmodType`
  + notation `[semiRingType of T for cT]`, use `GRing.SemiRing.clone T cT`
  + notation `[semiRingType of T]`, use `GRing.SemiRing.clone T _` or `T : semiRingType`
  + notation `[ringType of T for cT]`, use `GRing.Ring.clone T cT`
  + notation `[ringType of T]`, use `GRing.Ring.clone T _` or `T : ringType`
  + notation `[lmodType of T for cT]`, use `GRing.Lmodule.clone T cT`
  + notation `[lmodType of T]`, use `GRing.Lmodule.clone T _` or `T : lmodType`
  + notation `[lalgType of T for cT]`, use `GRing.Lalgebra.clone T cT`
  + notation `[lalgType of T]`, use `GRing.Lalgebra.clone T _` or `T : lalgType`
  + notation `[semi_additive of f as g]`, use `GRing.SemiAdditive.clone _ _ f g`
  + notation `[semi_additive of f]`, use `GRing.SemiAdditive.clone _ _ f _` or `f : {semi_additive _ -> _}`
  + notation `[additive of f as g]`, use `GRing.Additive.clone _ _ f g`
  + notation `[additive of f]`, use `GRing.Additive.clone _ _ f _` or `f : {additive _ -> _}`
  + notation `[srmorphism of f as g]`, use `GRing.SRMorphism.clone _ _ f g`
  + notation `[srmorphism of f]`, use `GRing.SRMorphism.clone _ _ f _` or `f : {srmorphism _ -> _}`
  + notation `[rmorphism of f as g]`, use `GRing.RMorphism.clone _ _ f g`
  + notation `[rmorphism of f]`, use `GRing.RMorphism.clone _ _ f _` or `f : {rmorphism _ -> _}`
  + notation `[linear of f as g]`, use `GRing.Linear.clone _ _ _ _ f g`
  + notation `[linear of f]`, use `GRing.Linear.clone _ _ _ _ f _` or `f : {linear _ -> _}`
  + notation `[lrmorphism of f]`, use `GRing.LRMorphism.clone _ _ _ _ f _` or `f : {lrmorphism _ -> _}`
  + notation `[comSemiRingType of T for cT]`, use `GRing.ComSemiRing.clone T cT`
  + notation `[comSemiRingType of T]`, use `GRing.ComSemiRing.clone T _` or `T : comSemiRingType`
  + notation `[comRingType of T for cT]`, use `GRing.ComRing.clone T cT`
  + notation `[comRingType of T]`, use `GRing.ComRing.clone T _` or `T : comRingType`
  + notation `[algType R of T for cT]`, use `GRing.Algebra.clone R T cT`
  + notation `[algType R of T]`, use `GRing.Algebra.clone R T _` or `T : algType R`
  + notation `[comAlgType R of T]`, use `GRing.ComAlgebra.clone R T _` or `T : comAlgType R`
  + notation `[unitRingType of T for cT]`, use `GRing.UnitRing.clone T cT`
  + notation `[unitRingType of T]`, use `GRing.UnitRing.clone T _` or `T : unitRingType`
  + notation `[comUnitRingType of T]`, use `GRing.ComUnitRing.clone T _` or `T : comUnitRingType`
  + notation `[unitAlgType R of T]`, use `GRing.UnitAlgebra.clone R T _` or `T : unitAlgType R`
  + notation `[comUnitAlgType R of T]`, use `GRing.ComUnitAlgebra.clone R T _` or `T : comUnitAlgType R`
  + notation `[idomainType of T for cT]`, use `GRing.IntegralDomain.clone T cT`
  + notation `[idomainType of T]`, use `GRing.IntegralDomain.clone T _` or `T : idomainType`
  + notation `[fieldType of T for cT]`, use `GRing.Field.clone T cT`
  + notation `[fieldType of T]`, use `GRing.Field.clone T _` or `T : fieldType`
  + notation `[decFieldType of T for cT]`, use `GRing.DecidableField.clone T cT`
  + notation `[decFieldType of T]`, use `GRing.DecidableField.clone T _` or `T : decFieldType`
  + notation `[closedFieldType of T for cT]`, use `GRing.ClosedField.clone T cT`
  + notation `[closedFieldType of T]`, use `GRing.ClosedField.clone T _` or `T : closedFieldType`

- in `ring_quotient.v`
  + notation `[zmodQuotType z, o & a of Q]`, use `ZmodQuotient.clone _ _ z o a Q _`
  + notation `[ringQuotType o & m of Q]`, use `RingQuotient.clone _ _ _ _ _ o m Q _`
  + notation `[unitRingQuotType u & i of Q]`, use `UnitRingQuotient.clone _ _ _ _ _ _ _ u i Q _`

- in `finalg.v`
  + notation `[finZsemimodType of T]`, use `FinRing.Zsemimodule.clone T _` or `T : finZsemimodType`
  + notation `[finZmodType of T]`, use `FinRing.Zmodule.clone T _` or `T : finZmodType`
  + notation `[finSemiRingType of T]`, use `FinRing.SemiRing.clone T _` or `T : finSemiRingType`
  + notation `[finRingType of T]`, use `FinRing.Ring.clone T _` or `T : finRingType`
  + notation `[finComSemiRingType of T]`, use `FinRing.ComSemiRing.clone T _` or `T : finComSemiRingType`
  + notation `[finComRingType of T]`, use `FinRing.ComRing.clone T _` or `T : finComRingType`
  + notation `[finUnitRingType of T]`, use `FinRing.UnitRing.clone T _` or `T : finUnitRingType`
  + notation `[finComUnitRingType of T]`, use `FinRing.ComUnitRing.clone T _` or `T : finComUnitRingType`
  + notation `[finIntegralDomainType of T]`, use `FinRing.IntegralDomain.clone T _` or `T : finIntegralDomainType`
  + notation `[finFieldType of T]`, use `FinRing.Field.clone T _` or `T : finFieldType`
  + notation `[finLmodType of T]`, use `FinRing.Lmodule.clone T _` or `T : finLmodType`
  + notation `[finLalgType of T]`, use `FinRing.Lalgebra.clone T _` or `T : finLalgType`
  + notation `[finAlgType of T]`, use `FinRing.Algebra.clone T _` or `T : finAlgType`
  + notation `[finUnitAlgType of T]`, use `FinRing.UnitAlgebra.clone T _` or `T : finUnitAlgType`

- in `countalg.v`
  + notation `[countZsemimodType of T]`, use `CountRing.Zsemimodule.clone T _` or `T : countZsemimodType`
  + notation `[countZmodType of T]`, use `CountRing.Zmodule.clone T _` or `T : countZmodType`
  + notation `[countSemiRingType of T]`, use `CountRing.SemiRing.clone T _` or `T : countSemiRingType`
  + notation `[countRingType of T]`, use `CountRing.Ring.clone T _` or `T : countRingType`
  + notation `[countComSemiRingType of T]`, use `CountRing.ComSemiRing.clone T _` or `T : countComSemiRingType`
  + notation `[countComRingType of T]`, use `CountRing.ComRing.clone T _` or `T : countComRingType`
  + notation `[countUnitRingType of T]`, use `CountRing.UnitRing.clone T _` or `T : countUnitRingType`
  + notation `[countComUnitRingType of T]`, use `CountRing.ComUnitRing.clone T _` or `T : countComUnitRingType`
  + notation `[countIdomainType of T]`, use `CountRing.IntegralDomain.clone T _` or `T : countIdomainType`
  + notation `[countFieldType of T]`, use `CountRing.Field.clone T _` or `T : countFieldType`
  + notation `[countDecFieldType of T]`, use `CountRing.DecidableField.clone T _` or `T : countDecFieldType`
  + notation `[countClosedFieldType of T]`, use `CountRing.ClosedField.clone T _` or `T : countClosedFieldType`

- in `order.v`
  + notation `[porderType of T for cT]`, use `POrder.clone _ T cT`
  + notation `[porderType of T for cT with disp]`, use `POrder.clone disp T cT`
  + notation `[porderType of T]`, use `POrder.clone _ T _` or `T : porderType`
  + notation `[porderType of T with disp]`, use `POrder.clone disp T _`
  + notation `[latticeType of T for cT]`, use `Lattice.clone _ T cT`
  + notation `[latticeType of T for cT with disp]`, use `Lattice.clone disp T cT`
  + notation `[latticeType of T]`, use `Lattice.clone _ T _` or `T : latticeType`
  + notation `[latticeType of T with disp]`, use `Lattice.clone disp T _`
  + notation `[bLatticeType of T for cT]`, use `BLattice.clone _ T cT`
  + notation `[bLatticeType of T]`, use `BLattice.clone _ T _` or `T : bLatticeType`
  + notation `[bDistrLatticeType of T]`, use `BDistrLattice.clone _ T _` or `T : bDistrLatticeType`
  + notation `[tbDistrLatticeType of T]`, use `TBDistrLattice.clone _ T _` or `T : tbDistrLatticeType`
  + notation `[finPOrderType of T]`, use `FinPOrder.clone _ T _` or `T : finPOrderType`
  + notation `[finLatticeType of T]`, use `FinLattice.clone _ T _` or `T : finLatticeType`
  + notation `[finDistrLatticeType of T]`, use `FinDistrLattice.clone _ T _` or `T : finDistrLatticeType`
  + notation `[finCDistrLatticeType of T]`, use `FinCDistrLattice.clone _ T _` or `T : finCDistrLatticeType`
  + notation `[finOrderType of T]`, use `FinTotal.clone _ T _` or `T : finOrderType`

- in `generic_quotient.v`
  + notation `[quotType of Q]`, use `Quotient.clone _ Q _` or `Q : quotType`
  + notation `[eqQuotType e of Q]`, use `EqQuotient.clone _ e Q _`

- in `fintype.v`
  + notation `EnumMixin`, use `isFInite.Build`
  + notation `Finite.UniqMixin`, use `isFinite.Build` and `Finite.uniq_enumP`
  + notation `Finite.CountMixin`, use `isFinite.Build` and `Finite.count_enumP`
  + notation `FinMixin`, use `isFInite.Build`
  + notation `UniqFinMixin`, use `isFInite.Build` and `Finite.uniq_enumP`
  + notation `[finType of T for C]`, use `Finite.clone T C`
  + notation `[finType of T]`, use `Finite.clone T _` or `T : finType`
  + notation `[subFinType of T]`, use `SubFinite.clone T _`
  + notation `[finMixin of T by <:]`, use `[Finite of T by <:]`

- in `eqtype.v`
  + notation `[eqType of T]`, use `Equality.clone T _` or `T : eqType`
  + notation `[eqType of T for C]`, use `Equality.clone T C`
  + definition `InjEqMixin`, use alias `inj_type`
  + definition `CanEqMixin`, use alias `can_type`
  + definition `PCanEqMixin`, use alias `pcan_type`
  + notation `[eqMixin of T by <:]`, use `[Equality of T by <:]`

- in `choice.v`
  + notation `[hasChoice of T]`, use `Choice.on T`
  + notation `[choiceType of T for C]`, use `Choice.clone T C`
  + notation `[choiceType of T]`, use `Choice.clone T _` or `T : choiceType`
  + notation `[choiceMixin of T by <:]`, use `[Choice of T by <:]`
  + notation `[isCountable of T]`, use `Countable.on T`
  + notation `[countType of T for C]`, use `Countable.clone T C`
  + notation `[countType of T]`, use `Countable.clone T _` or `T : countType`
  + notation `[countMixin of T by <:]`, use `[Countable of T by <:]`
  + notation `[subCountType of T]`, use `SubCountable.clone _ _ T _`

### Infrastructure

### Misc

