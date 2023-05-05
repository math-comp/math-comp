### Added

- in `eqtype.v`
  + structure `subEqType`
  + notation `\val`

### Changed

- in `eqtype.v`
  + structures `eqType` and `subType` ported to HB

### Renamed

### Removed

- in `eqtype.v`
  + notation `EqMixin`, use `hasDecEq.Build`
  + notation `[eqMixin of T]`, use `Equality.on T`
  + `unit_eqMixin` and `unit_eqType`, use `unit : eqType`
  + `bool_eqMixin` and `bool_eqType`, use `bool : eqType`
  + `void_eqMixin` and `void_eqType`, use `void : eqType`
  + `sig_eqMixin` and `sig_eqType`, use `{x | P x} : eqType`
  + `prod_eqMixin` and `prod_eqType`, use `(T1 * T2)%type : eqType`
  + `option_eqMixin` and `option_eqType`, use `option T : eqType`
  + `tag_eqMixin` and `tag_eqType`, use `{i : I & T_ i} : eqType`
  + `sum_eqMixin` and `sum_eqType`, use `(T1 + T2)%type : eqType`
  + definition `clone_subType`, use `SubType.clone`
  + notation `[subType for v]`, use `[isSub for v]`
  + notation `[subType for v by rec]`, use `[isSub for v by rec]`
  + notation `[subType of T for v]`, use `[isSub of T for v]`
  + notation `[subType of T]`, use `SubType.clone T _`
  + definition `NewType`
  + notation `[newType for v]`, use `[isNew for v]`
  + notation `[newType for v by rec]`, use `[isNew for v by rec]`
  + definition `sig_subType`, use `sig P : subType`
  + definitions `sub_eqMixin`, `sub_eqType` and `SubEqMixin`, use alias `sub_type`

### Deprecated

- in `eqtype.v`
  + notation `[eqType of T]`, use `Equality.clone T _` or `T : eqType`
  + notation `[eqType of T for C]`, use `Equality.clone T C`
  + definition `InjEqMixin`, use alias `inj_type`
  + definition `CanEqMixin`, use alias `can_type`
  + definition `PCanEqMixin`, use alias `pcan_type`
  + notation `[eqMixin of T by <:]`, use `[Equality of T by <:]`
