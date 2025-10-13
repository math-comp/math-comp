- in `qpoly.v`
  + definitions `poly_of_size_pred`, `poly_of_size`, `npoly`,
    `npoly_rV`, `rVnpoly`, `mk_npoly`, `npoly0`, `npolyp`,
    `npoly_of_seq`, `mk_monic`, `qpoly` generalized to
    `nzSemiRingType`
  + definition `npoly_enum` generalized to `finNzSemiRingType`
  + the `submodClosed` instance on `poly_of_size_pred` generalized to
    `nzSemiRingType`
  + the `subType`, `lSemiModType`, `semiVectType` instance on `npoly`
    generalized to `nzSemiRingType`
  + the `countNmodType` instance on `npoly` generalized to
    `countNzSemiRingType`
  + the `finNmodType` instance on `npoly` generalized to
    `finNzSemiRingType`
  + the semilinear function instance on `polyn` generalized to
    `nzSemiRingType`
  + the `npoly` instance on `poly` generalized to `nzSemiRingType`
  + lemmas `npoly_is_a_poly_of_size`, `size_npoly`, `npoly_rV_K`,
    `rVnpolyK`, `npoly_vect_axiom`, `size_npoly0`, `npolyP`,
    `coef_npolyp`, `big_coef_npoly`, `npolypK`, `coef_sum`,
    `mk_monic_X`, `mk_monic_Xn` generalized to `nzSemiRingType`
  + lemmas `npoly_enum_uniq`, `mem_npoly_enum`, `card_npoly`,
    `card_qpoly`, `card_monic_qpoly` generalized to
    `finNzSemiRingType`
    ([#1466](https://github.com/math-comp/math-comp/pull/1466)).
