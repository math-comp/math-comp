### Added

### Changed

- in `generic_quotient.v`,
  + structures quotType and eqQuotType ported to HB

### Renamed

### Removed

- in `generic_quotient.v`,
  + notation `QuotClass`, use `isQuotient.Build`
  + notation `EqQuotType`, use `isEqQuotient.Build`

### Deprecated

- in `generic_quotient.v`
  + notation `[quotType of Q]`, use `Quotient.clone _ Q _` or `Q : quotType`
  + notation `[eqQuotType e of Q]`, use `EqQuotient.clone _ e Q _`
