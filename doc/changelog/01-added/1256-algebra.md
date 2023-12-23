- file `monoid.v`
	+ mixin `hasMul`
	+ structures `magmaType`, `ChoiceMagma.type`
	+ definition `commute`
	+ lemmas `commute_refl`, `commute_sym`
	+ definition `mulg_closed`
	+ mixin `Magma_isSemigroup`
	+ structure `semigroupType`
	+ factory `isSemigroup`
	+ lemma `commuteM`
	+ mixin `hasOne`
	+ structures `baseUMagmaType`, `ChoiceBaseUMagma.type`
	+ definition `natexp`
	+ lemmas `expg0`, `expg1`, `expg2`, `expgSS`, `expgb`
	+ definition `umagma_closed`
	+ mixin `BaseUMagma_isUMagma`
	+ factory `Magma_isUMagma`
	+ structure `umagmaType`
	+ lemmas `expgS`, `expg1n`, `commute1`
	+ structure `monoidType`
	+ factories `Semigroup_isMonoid`, `UMagma_isMonoid`, `isMonoid`
	+ lemmas `expgSr`, `expgnDr`, `expgnA`, `expgnAC`, `iter_mulg`, `iter_mulg_1`,
		`commuteX`, `comuteX2`, `expgMn`.
	+ notation `monoid_closed`
	+ mixin `hasInv`
	+ structure `baseGroupType`
	+ mixin `Monoid_isGroup`
	+ structure `groupType`
	+ factory `isGroup`
	+ definitions `conjg`, `commg`
	+ lemmas `divgg`, `mulKg`, `mulVKg`, `mulgK`, `mulgVK`, `mulgI`, `mulIg`,
		`invgK`, `invg_inj`, `divgI`, `divIg`, `invg1`, `invg_eq1`, `divg1`,
		`div1g`, `invgF`, `invgM`, `divKg`, `mulgKA`, `divgKA`, `mulg1_eq`,
		`divg1_eq`, `divg_eq`, `divg_eq1`, `mulg_eq1`, `eqg_inv`, `iqg_invLR`,
		`commuteV`, `expVgn`, `expgnFr`, `expgnFl`, `conjgE`, `conjgC`, `conjgCV`,
		`conjg1`, `conj1g`, `conjMg`, `conjgM`, `conjVg`, `conjJg`, `conjXg`,
		`conjgK`, conjgKV`, `conjg_inj`, `conjg_eq1`, `commgEl`, `commgEr`,
		`commgC`, `commgCV`, `conjRg`, `invgR`, `commgP`, `conjg_fix`, `conjg_fixP`,
		`commg1_sym`, `commg1`, `comm1g`, `commgg`, `commgXg`, `commgVg`, `commgXVg`
	+ definitions `invg_closed`, `divg_closed`, `group_closed`
	+ lemmas `group_closedV`, `group_closedM`
	+ mixin `isMultiplicative`
	+ structure `Multiplicative.type`
	+ mixin `isUMagmaMorphism`
	+ structure `UMagmaMorphism.type`
	+ factory `isGroupMorphism`
	+ notation `{multiplicative _ -> _}`
	+ definitions `mul_fun`, `one_fun`
	+ lemmas `can2_gmulfM`, `gmulf_commute`, `gmulf_eq1`, `can2_gmulf1`,
		`gmulfXn`, `gumlfV`, `gmulfF`, `gmulf_inj`, `gmulfXVn`, `gmulfJ`, `gmulfR`,
		`idfun_gmulfM`, `comp_gmulfM`, `idfun_gmulf1`, `one_fun_gmulf1`,
		`comp_gmulf1`, `one_fun_gmulf1`, `mul_fun_gmulf1`
	+ mixins `isMulClosed`, `isMul1Closed`, `isInvClosed`
	+ structures `mulgClosed`, `umagmaClosed`, `invgClosed`, `groupClosed`
	+ lemmas `gpredXn`, `gpredV`, `gpredF`, `gpredFC`, `gpredXNn`, `gpredMr`,
		`gpredMl`, `gpredFr`, `gpredFl`, `gpredJ`, `gpredR`
	+ mixin `isSubMagma`
	+ structure `subMagmaType`
	+ factory `SubChoice_isSubMagma`
	+ structure `subSemigroupType`
	+ factory `SubChoice_isSubSemigroup`
	+ mixin `isSubBaseUMagma`
	+ structures `subBaseUMagmaType`, `subUMagmaType`
	+ factory `SubChoice_isSubUMagma`
	+ structure `subMonoidType`
	+ factory `SubChoice_isSubMonoid`
	+ structure `subGroupType`
	+ factory `SubChoice_isSubGroup`
	+ definition `ffun_mul`
	+ lemma `ffun_mulgA`
	+ definition `ffun_one`
	+ lemmas `ffun_mul1g`, `ffun_mulg1`
	+ definition `ffun_inv`
	+ lemmas `ffun_mulVg`, `ffun_mulgV`
	+ definition `mul_pair`
	+ lemmas `fst_is_multiplicative`, `snd_is_multiplicative`, `pair_mulgA`
	+ definition `one_pair`
	+ lemmas `first_is_umagma_morphism`, `snd_is_umagma_morphism`, `pair_mul1g`,
		`pair_mulg1`
	+ definition `inv_pair`
	+ lemmas `pair_mulVg`, `pair_mulgV`

- file comoid.v
	+ mixin `hasAdd`
	+ structures `baseAddMagmaType`, `ChoiceBaseAddMagma.type`
	+ definition `to_multiplicative`, `addr_closed`
	+ mixin `BaseAddMagma_isAddMagma`
	+ structure `addMagmaType`
	+ factory `isAddMagma`
	+ lemma `commuteT`
	+ mixin `AddMagma_isAddSemigroup`
	+ structure `addSemigroupType`
	+ factory `isAddSemigroup`
	+ lemmas `addrCA`, `addrAC`, `addrACA`
	+ mixin `hasZero`
	+ structure `baseAddUMagmaType`, `ChoiceBaseAddUMagma.type`
	+ definition `natmul`
	+ lemmas `mulr0n`, `mulr1n`, `mulr2n`, `mulrb`, `mulrSS`
	+ definition `addumagma_closed`
	+ mixin `BaseAddUMagma_isAddUMagma`
	+ factory `isAddUMagma`
	+ structure `addUMagmaType`
	+ lemma `addr0`
	+ factory `isNmodule`
	+ structure `nmodType`
	+ lemmas `mulrS`, `mulrSr`, `mul0rn`, `mulrnDl`, `mulrnDr`, `mulrnA`,
		`mulrnAC`, `iter_addr`, `iter_addr_0`, `sumrMnl`, `sumrMnr`, `sumr_const`,
		`sumr_const_nat`
	+ definition `nmod_closed`
	+ mixin `hasOpp`
	+ structure `baseZmodType`
	+ definitions `oppr_closed`, `subr_closed`, `zmod_closed`
	+ mixin `BaseZmoduleNmodule_isZmodule`
	+ structure `zmodType`
	+ factories `Nmodule_isZmodule`, `isZmodule`, `Group_isZmodule`
	+ lemmas `addrN`, `subrr`, `addKr`, `addNKr`, `addrK`, `addrNK`, `subrK`,
		`subKr`, `addrI`, `subrI`, `subIr`, `opprK`, `oppr_inj`, `oppr0`,
		`oppr_eq0`, `subr0`, `opprB`, `opprD`, `addrKA`, `subrKA`, `addr0_eq`,
		`subr0_eq`, `subr_eq`, `subr_eq0`, `addr_eq0`, `eqr_opp`, `eqr_oppLR`,
		`mulNrn`, `mulrnBl`, `mulrnBr`, `sumrN`, `sumrB`, `telescope_sumr`,
		`telescope_sumr_eq`, `zmod_closedN`, `zmod_closedD`, `zmod_closed0D`
	+ definition `semi_additive`
	+ mixin `isSemiAdditive`
	+ structure `Additive.type`
	+ definition `additive`
	+ factory `isAdditive`
	+ notation `{additive _ -> _}`
	+ lemmas `raddf0`, `raddfD`, `raddf_sum`
	+ definitions `to_fmultiplicative`, `add_fun`, `null_fun`, `opp_fun`,
		`sub_fun`
	+ lemmas `raddf_eq0`, `raddfMn`, `can2_semi_additive`, `raddfN`, `raddfB`,
		`raddf_inj`, `raddfMNn`, `can2_additive`, `add_fun_semi_additiveè,
		`idfun_is_semi_additive`, `comp_is_semi_additive`,
		`null_fun_is_semi_additive`, `opp_is_semi_additive`, `opp_fun_is_additive`,
		`sub_fun_is_additive`
	+ mixins `isAddClosed`, `isOppClosed`
	+ structures `addrClosed`, `opprClosed`, `zmodClosed`
	+ factory `isZmodClosed`
	+ definition `to_pmultiplicative`
	+ lemmas `rpred0`, `rpredD`, `rpred0D`, `rpredMn`, `rpredNr`, `rpredN`,
		`rpredB`, `rpredBC`, `rpredMNn`, `rpredDr`, `rpredDl`, `rpredBr`, `rpredBl`
		`zmodClosedP`
	+ mixin `isSubBaseAddUMagma`
	+ structures `subBaseAddUMagma`, `subAddUMagma`, `subNmodType`
	+ lemmas `valD`, `val0`
	+ factories `SubChoice_isSubAddUMagma`, `SubChoice_isSubNmodule`
	+ structure `subZmodType` 
	+ lemmas `valB`, `valN`
	+ factories `isSubZmodule`, `SubChoice_isSubZmodule`
	+ notations `0`, `-%R`, `- x`, `+%R`, `x + y`, `x - y`, `x *+ n`, `x *- n`,
		``s `_ i`` `support` `1` `- 1` `n %:R`
	+ definition `ffun_add`
	+ lemmas `ffun_addrC`, `ffun_addrA`
	+ definition `ffun_zero`
	+ lemmas `ffun_add0r`, `ffunMnE`, `sum_ffunE`, `sum_ffun`
	+ definition `ffun_opp`
	+ lemma `ffun_addNr`
	+ definition `pair_add`
	+ lemmas `pair_addrC`, `pair_addrA`
	+ definition `pair_zero`
	+ lemmas `fst_is_additive`, `snd_is_additive`, `pair_add0r`
	+ definition `pair_opp`
	+ lemmas `pair_addNr`, `natr0E`, `natrDE`, `natrE`
    (`#1256 <https://github.com/coq/stdlib/pull/1256>`_,
    by Tragicus).
