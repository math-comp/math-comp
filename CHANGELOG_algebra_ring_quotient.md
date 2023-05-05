### Added

### Changed

- in `ring_quotient.v`
  + structures `zmodQuotType`, `ringQuotType` and `unitRingQuotType` have been ported to HB.
  + structures `proper_ideal`, `idealr` and `primeIdealr` have been ported to HB.

### Renamed

### Removed

- in `ring_quotient.v`
  + removed `MkIdeal` and `MkPrimeIdeal` in favor of generic HB commands.

### Deprecated

- in `ring_quotient.v`
  + notation `[zmodQuotType z, o & a of Q]`, use `ZmodQuotient.clone _ _ z o a Q _`
  + notation `[ringQuotType o & m of Q]`, use `RingQuotient.clone _ _ _ _ _ o m Q _`
  + notation `[unitRingQuotType u & i of Q]`, use `UnitRingQuotient.clone _ _ _ _ _ _ _ u i Q _`
