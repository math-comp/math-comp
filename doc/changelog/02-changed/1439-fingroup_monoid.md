- in `fingroup.v`
  + lemma `expgnE`
    generalized from `baseFinGroupType` to `baseUMagmaType`
  + lemma `conjg_prod`
    generalized from `finGroupType` to `groupType`
  + tactic `gsimpl`
    generalized from `finGroupType` to `groupType`
  + definitions `gsimp`, `gnorm`
    generalized from `finGroupType` to `groupType`

- in `monoid.v`
  + definitions `conjg`, `commg`
    generalized from `groupType` to `baseGroupType`
  + lemmas `invg1`, `invgF`, `prodgV`, `eqg_inv`, `eqg_invLR`, `invg_eq1`,
      `expVgn`, `conjgE`, `commgEl`, `commgEr`
    generalized from `groupType` to `starMonoidType`
    ([#1439](https://github.com/math-comp/math-comp/pull/1439)).
