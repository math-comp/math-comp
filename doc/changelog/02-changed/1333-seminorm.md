- in `ssrnum.v`
  + Mixin `Zmodule_isNormed` is now a factory building a
    `SemiNormedZmodule` and a `SemiNormedZmodule_isPositiveDefinite`.
    All lemmas from the theory of `normedZmodType` were generalized
    to `semiNormedZmodType` but for the ones that require a
    `normedZmodType`, namely `normr0_eq0`, `normr0P` and `normr_eq0`.
    (`#1333 <https://github.com/coq/stdlib/pull/1333>`_,
    by Cyril Cohen).
