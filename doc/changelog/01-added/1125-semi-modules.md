- in `ssralg.v`
  + Semimodule and semialgebra structures `lSemiModType`, `lSemiAlgType`, `semiAlgType`, `comSemiAlgType`, `subLSemiModType`, `subLSemiAlgType`, and `subSemiAlgType`.
  + Scaling-morphism structures `GRing.Scale.preLaw` and `GRing.Scale.semiLaw`.
  + Mixins `Nmodule_isLSemiModule`, `LSemiModule_isLSemiAlgebra`, `GRing.Scale.isPreLaw`, `GRing.Scale.isSemiLaw`, `LSemiAlgebra_isSemiAlgebra`, `isSubLSemiModule`
  + Factories `LSemiModule_isLmodule`, `isSemilinear`, `LSemiAlgebra_isComSemiAlgebra`, `SubNmodule_isSubLSemiModule`, `SubNzSemiRing_SubLSemiModule_isSubLSemiAlgebra`, `SubLSemiAlgebra_isSubSemiAlgebra`, `SubChoice_isSubLSemiModule`
  + Definitions `semilinear_for`, `subsemimod_closed`
  + Notations `semilinear`, `semiscalar`, `[SubNmodule_isSubLSemiModule of V by <:]`, `[SubChoice_isSubLSemiModule of V by <:]`, `[SubSemiRing_SubLSemiModule_isSubLSemiAlgebra of V by <:]`, `[SubLSemiAlgebra_isSubSemiAlgebra of V by <:]`
  + Lemmas `subsemimod_closedD`, `subsemimod_closedZ`, `submod_closed_semi`, `additive_semilinear`, `scalable_semilinear`, `semilinear_linear`, `semilinearP`, `semilinearPZ`, `can2_semilinear`, `semiscalarP`, `subsemimodClosedP`
    ([#1125](https://github.com/math-comp/math-comp/pull/1125),
    by Kazuhiko Sakaguchi).
