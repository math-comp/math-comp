### Added

### Changed

- in `fintype.v`
  + structures `finType` and `subFinType` ported to HB

### Renamed

### Removed

### Deprecated

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
