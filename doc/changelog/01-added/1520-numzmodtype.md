- in `orderedzmod.v`
  + structure `POrderNmodule`
  + notation `porderNmodeType` for `POrderNmodule.type`
  + factories `Add_isHomo` and `POrderedZmodule_hasTransCmp`
  + structures `porderedNmodType`, `porderedZmodType` and
    `numZmodType`
  + definitions `ZmodulePositiveCone.type` and `ZmodulePositiveCone.le`
  + instance of `porderedZmodType` on `ZmodulePositiveCone.type`
  + lemmas `addr_gt0`, `mulrn_lgt0`, `pmulrIn`, `zmod_leP`,
    `zmod_ltP`, `zmod_ltgtP`, `zmod_ge0P`, `zmod_le0P` and
    `zmod_ltgt0P`
  + multirule `lteif_oppE`
    ([#1520](https://github.com/math-comp/math-comp/pull/1520)).
