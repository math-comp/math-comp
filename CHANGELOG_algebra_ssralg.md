### Added

### Changed

### Renamed

### Removed

### Deprecated

- in `ssralg.v`
  + notation `[zsemimodType of T for cT]`, use `GRing.Zsemimodule.clone T cT`
  + notation `[zsemimodType of T]`, use `GRing.Zsemimodule.clone T _` or `T : zsemimodType`
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
