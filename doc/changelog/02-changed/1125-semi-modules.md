- in `ssralg.v`
  + `{linear U -> V | s}` and `{linear U -> V}`, generalized from modules to semimodules, now represent semilinear and linear functions
  + `{scalar U}`, generalized from rings and modules to semirings and semimodules, now represents semiscalar and scalar functions
  + `{lrmorphism A -> B | s}` and `{lrmorphism A -> B}`, generalized from algebras to semialgebras, now represent semialgebra and algebra morphisms
  + Mixins `Zmodule_isLmodule`, `Lmodule_isLalgebra`, `Lalgebra_isAlgebra`, `isSubLmodule` are now factories
  + `GRing.scale`, `scalerA`, `scale0r`, `scale1r`, `scalerDr`, `scalerDl`, `scaler0`, `scaler_nat`, `scalerMnl`, `scalerMnr`, `scaler_suml`, `scaler_sumr`, `scaler_closed`, `scale_fun`, `raddfZnat`, `scalable_for`, `isScalable`, `linear_for`, `rpredZnat`, `submodClosed` generalized to `lSemiModType`
  + `linear0`, `linearD`, `linearMn`, `linear_sum`, `linearZ_LR`, `linearP`, `linearZ`, `linearZZ`, `linearPZ`, `can2_scalable`, `can2_linear`, `scalarZ`, `scalarP` generalized to `lSemiModType` and semilinear functions
  + `scalerAl`, `mulr_algl`, `in_alg`, `subalgClosed` generalized to `lSemiAlgType`
  + `rmorph_alg` generalized to `lSemiAlgType` and semialgebra morphisms
    ([#1125](https://github.com/math-comp/math-comp/pull/1125),
    by Kazuhiko Sakaguchi).
