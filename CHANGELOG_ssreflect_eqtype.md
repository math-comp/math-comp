### Added

### Changed

### Renamed

### Removed

### Deprecated

- in `eqtype.v`
  + notation `[eqType of T]`, use `Equality.clone T _` or `T : eqType`
  + notation `[eqType of T for C]`, use `Equality.clone T C`
  + definition `InjEqMixin`, use alias `inj_type`
  + definition `CanEqMixin`, use alias `can_type`
  + definition `PCanEqMixin`, use alias `pcan_type`
  + notation `[eqMixin of T by <:]`, use `[Equality of T by <:]`
