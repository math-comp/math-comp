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
  + structures `quotType` and `eqQuotType` ported to HB

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

