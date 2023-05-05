### Added

### Changed

- in `falgebra.v`
  + structure `falgType` ported to HB

### Renamed

- in `falgebra.v`
  + strcture `FalgType` -> `falgType`
  + notation `FalgUnitRingType`, use `Algebra_isFalgebra.Build`

### Removed

### Deprecated

- in `falgebra.v`
  + notation `[FalgType F of L for L']`, use `Falgebra.clone F L L'`
  + notation `[FalgType F of L]`, use `Falgebra.clone F L _` or `L : FalgType F`
