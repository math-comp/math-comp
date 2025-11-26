- in `monoid.v`
  + Definitions `invg_closed`, `divg_closed`, `group_closed` generalized from
    `groupType` to `baseGroupType`
    ([#1433](https://github.com/math-comp/math-comp/pull/1433)).

- in `nmodule.v`
  + Mixin `isOppClosed` generalized from `zmodType` to `baseZmodType`
  + Structures `opprClosed` and `zmodClosed` generalized from `zmodType` to
    `baseZmodType`
  + The definition `zmod_closed` has been specialized from `baseZmodType` to
    `zmodType` to avoid non-uniform implicit coercions
  + The implicit status of `telescope_sumr_eq` has been changed to match with
    the old one in `ssralg.v`
    ([#1433](https://github.com/math-comp/math-comp/pull/1433)).
