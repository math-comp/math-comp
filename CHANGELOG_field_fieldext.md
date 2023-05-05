### Added

### Changed

- in `fieldext.v`
  + structure `fieldExtType` ported to HB

### Renamed

### Removed

### Deprecated

- in `fieldext.v`
  + notation `[fieldExtType F of L for K]`, use `FieldExt.clone F L K`
  + notation `[fieldExtType F of L]`, use `FieldExt.clone F L _` or `L : fieldExtType F`
