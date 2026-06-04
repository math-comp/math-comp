### Added

- in `bigop.v`
  + new definition `olaw`
  + new lemmas `olawss`, `olawx1`,`olaw1x`, `some_big_mk_monoid`, `big_mk_option_monoid`, and 
    `big_split_ord_idem`
  + new instances of `Monoid.law` and `Monoid.com_law` for `olaw op`
    when `op` has respective type `SemiGroup.law` and `SemiGroup.com_law`.
    ([#1608](https://github.com/math-comp/math-comp/pull/1608)).
