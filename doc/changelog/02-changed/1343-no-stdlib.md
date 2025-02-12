- in `ssrnat.v`
  + lemma `eq_binP` changed from Stdlib's `N.eqb` to new `N_eqb`
  + eqtype instance on `nat` changed from Stdlib's `N.eqb`
    to new `N_eqb`
    ([#1343](https://github.com/coq/stdlib/pull/1343),
    by Pierre Roux).
