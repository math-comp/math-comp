### Added

### Changed

### Renamed

### Removed

### Deprecated

- in `ring_quotient.v`
  + notation `[zmodQuotType z, o & a of Q]`, use `ZmodQuotient.clone _ _ z o a Q _`
  + notation `[ringQuotType o & m of Q]`, use `RingQuotient.clone _ _ _ _ _ o m Q _`
  + notation `[unitRingQuotType u & i of Q]`, use `UnitRingQuotient.clone _ _ _ _ _ _ _ u i Q _`
