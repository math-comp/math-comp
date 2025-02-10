- in `ssrnum.v`
  + Mixin `Zmodule_isNormed` is now a factory building a
    `SemiNormedZmodule` and a `SemiNormedZmodule_isPositiveDefinite`.
    ([#1333](https://github.com/coq/stdlib/pull/1333),
    by  Alessandro Bruni and Cyril Cohen).
  + Generalized lemmas from the theory of `normedZmodType` to
    `semiNormedZmodType`: `normr0`, `distrC`, `normr_id`, and
    `normr_ge0`, `normr_real`, `ler_norm_sum`, `ler_normB`,
    `ler_distD`, `lerB_normD`, `lerB_dist`, `ler_dist_dist`,
    `ler_dist_normD`, `ler_nnorml`, `ltr_nnorml`, `lter_nnormr`.
    ([#1333](https://github.com/coq/stdlib/pull/1333),
    by Alessandro Bruni and Cyril Cohen).
