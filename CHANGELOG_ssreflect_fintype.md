### Added

### Changed

### Renamed

### Removed

### Deprecated

- in `fintype.v`
  + notation `EnumMixin`, use `isFInite.Build`
  + notation `FinMixin`, use `isFInite.Build`
  + notation `[finType of T for C]`, use `Finite.clone T C`
  + notation `[finType of T]`, use `Finite.clone T _` or `T : finType`
  + notation `[subFinType of T]`, use `SubFinite.clone T _`
  + notation `[finMixin of T by <:]`, use `[Finite of T by <:]`
