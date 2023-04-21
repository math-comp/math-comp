### Added

### Changed

### Renamed

### Removed

### Deprecated

- in `choice.v`
  + notation `[hasChoice of T]`, use `Choice.on T`
  + notation `[choiceType of T for C]`, use `Choice.clone T C`
  + notation `[choiceType of T]`, use `Choice.clone T _` or `T : choiceType`
  + notation `[choiceMixin of T by <:]`, use `[Choice of T by <:]`
  + notation `[isCountable of T]`, use `Countable.on T`
  + notation `[countType of T for C]`, use `Countable.clone T C`
  + notation `[countType of T]`, use `Countable.clone T _` or `T : countType`
  + notation `[countMixin of T by <:]`, use `[Countable of T by <:]`
  + notation `[subCountType of T]`, use `SubCountable.clone _ _ T _`
