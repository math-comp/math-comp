### Added

### Changed

### Renamed

### Removed

- in `vector.v`
  + notation `VectMixin` and `VectType`, use `Lmodule_hasFinDim.Build`

### Deprecated

- in `vector.v`
  + notation `[vectType R of T for cT]`, use `Vector.clone T cT`
  + notation `[vectType R of T]`, use `Vector.clone T _` or `T : vectType R`
