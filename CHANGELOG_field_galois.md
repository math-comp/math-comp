### Added

### Changed

- in `galois.v`
  + structure `splittingFieldType` ported to HB

### Renamed

- in `galois.v`
  + definition `SplittingField.axiom` -> `splitting_field_axiom`
  + notation `SplittingFieldType`, use `FieldExt_isSplittingfield.Build`

### Removed

### Deprecated

- in `galois.v`
  + notation `[splittingFieldType F of L for K]`, use `SplittingField.clone F L K`
  + notation `[splittingFieldType F of L]`, use `SplittingField.clone F L _` or
    `L : splittingFieldType F`
