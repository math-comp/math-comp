### Added

- in `choice.v`
  + notation `subChoiceType`, structure `SubChoice`

### Changed

- in `choice.v`
  + `[choiceMixin of T by <:]` becomes `[Choice of T by <:]`
  + `[countMixin of T by <:]` becomes `[Countable of T by <:]`
  + `Choice.mixin_of` becomes `hasChoice`
  + `Countable.mixin_of` becomes `isCountable`

### Renamed

- in `choice.v`
  + `choiceMixin` -> `hasChoice`
  + `sub_choiceMixin` -> `sub_hasChoice`
  + `seq_choiceMixin` -> `seq_hasChoice`
  + `tagged_choiceMixin` -> `tagged_hasChoice`
  + `nat_choiceMixin` -> `nat_hasChoice`
  + `PcanChoiceMixin` -> `pcancel_hasChoice_subproof`

### Removed

- in `choice.v`
  + `ChoiceType`
  + `CountType`
  + `sub_choiceClass`, `sub_choiceType`
  + `seq_choiceType` (use `seq _ : choiceType` instead, the same
     applies for other `*_choiceType`'s)
  + `tagged_choiceType`
  + `nat_choiceType`
  + `bool_choiceMixin`, `bool_choiceType`, `bitseq_choiceType`,
    `unit_choiceMixin`, `unit_choiceType`, `void_choiceMixin`,
    `void_choiceType`, `option_choiceMixin`, `option_choiceType`,
    `sig_choiceMixin`, `sig_choiceType`, `prod_choiceMixin`,
    `prod_choiceType`, `sum_choiceMixin`, `sum_choiceType`,
    `tree_choiceMixin`, `tree_choiceType`
  + `sub_countMixin`
  + `seq_countMixin`, `seq_countType`,
    `tag_countMixin`, `tag_countType`,
    `nat_countMixin`, `nat_countType`,
    `bool_countMixin`, `bool_countType`,
    `bitseq_countType`,
    `unit_countMixin`, `unit_countType`,
    `void_countMixin`, `void_countType`,
    `option_countMixin`, `option_countType`,
    `sig_countMixin`, `sig_countType`,
    `sig_subCountType`,
    `prod_countMixin`, `prod_countType`,
    `sum_countMixin`, `sum_countType`,
    `tree_countMixin`, `tree_countType`

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
  + `CanChoiceMixin` -> use Choice.copy with can_type
  + `PcanChoiceMixin` -> use Choice.copy with pcan_type
  + `CanCountMixin` -> use Countable.copy with can_type
  + `PcanCountMixin` -> use Countable.copy with pcan_type