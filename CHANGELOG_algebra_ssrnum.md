### Added

- in `ssrnum.v`
  + structures `porderZmodType`

### Changed

- in `ssrnum.v`
  + structures `normedZmodType`, `numDomainType`,
    `numFieldType`, `numFieldType`, `numClosedFieldType`, `realDomainType`,
    `realFieldType`, `archiFieldType`, `rcfType` ported to HB

### Renamed

- in `ssrnum.v`
  + notation `NormedZmodType`, use `Zmodule_isNormed.Build`
  + notation `NumDomainType`, use `isNumRing.Build`
  + notation `NumClosedFieldType`, use `NumField_isImaginary.Build`
  + notation `ArchiFieldType`, use `RealField_isArchimedean.Build`
  + notation `RcfType`, use `RealField_isClosed.Build`

### Removed

### Deprecated

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
