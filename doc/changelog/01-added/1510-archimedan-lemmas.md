- in `orderedzmod.v`
  + Definitions `Num.to_real` and `Num.to_nneg`
  + Lemmas `to_realT`, `real_to_real`, `to_nnegT`, `ler_to_nneg`,
    `nneg_to_nneg`, `real_to_nneg`, `to_real_le_nneg`, `ler_to_real`, `to_realN`
    ([#1510](https://github.com/math-comp/math-comp/pull/1510),
    fixes [#1377](https://github.com/math-comp/math-comp/issues/1377)).

- in `archimedean.v`
  + Mixin `NumDomain_hasFloorCeilTruncn_truncn_abs_floor` which
    eventually replaces the old archimedean mixin
	`NumDomain_hasFloorCeilTruncn`
  + Lemmas `truncnDrn`, `to_real_floor_itv`, `to_real_floor_le`,
    `to_real_floorD1_gt`, `to_real_floor_gez`, `to_real_floor_ltz`,
    `to_real_eq_floor`, `to_real_floor_eqP`, `real_floor_eqP`,
    `to_real_floorDzr`, `to_real_floorDrz`, `to_real_floor_ge0`,
    `to_real_floor_le0`, `to_real_ceil_itv`, `to_real_ceilB1_lt`,
    `to_real_ceil_ge`, `to_real_ceil_lez`, `to_real_ceil_gtz`,
    `to_real_eq_ceil`, `to_real_ceil_eqP`, `real_ceil_eqP`, `to_real_ceilDzr`,
    `to_real_ceilDrz`, `to_real_ceil_ge0`, `to_real_ceil_le0`,
    `to_nneg_truncn_itv`, `to_nneg_truncn_le`, `to_nneg_truncnS_gt`,
    `to_real_truncnS_gt`, `to_nneg_truncn_geq`, `to_nneg_truncn_ltn`,
    `to_real_truncn_leq`, `to_nneg_eq_truncn`, `to_nneg_truncn_eqP`,
    `truncn_eqP`, `to_nneg_archi_boundP`, `to_nneg_truncnDnr`,
    `to_nneg_truncnDrn`, `floor_eqP`, `ceil_eqP`
    ([#1510](https://github.com/math-comp/math-comp/pull/1510),
    fixes [#1377](https://github.com/math-comp/math-comp/issues/1377)).
