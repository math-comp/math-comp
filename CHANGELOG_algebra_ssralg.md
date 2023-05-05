### Added

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

### Changed

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

### Renamed

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

### Removed

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

### Deprecated

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
