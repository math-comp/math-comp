- experimental new library `algebra/tensor.v`
  + types `'T[R]_(u_, d_)`, `'T_(u_, d_)` for tensors over `R` with
    contravariant dimensions `u_` and covariant dimensions `d_`
    (each a `k.-tuple {posnum nat}`, coerced to `{posnum nat} ^ k`),
    and shorthands `'nT[R]_(u_)`, `'nT_(u_)` (purely contravariant),
    `'oT[R]_(d_)`, `'oT_(d_)` (purely covariant), and `'sT[R]`, `'sT`
    (purely scalar, i.e. `'T[R]_([tuple], [tuple])`), built from the
    variant `tensor` and its projection `tensor_val`
  + parsing shorthand notations
    `'T[R]_[u1, .., uk ; d1, .., dl]`, `'nT[R]_[u1, .., uk]`,
    `'oT[R]_[d1, .., dl]` expanding to the corresponding
    `[tuple of u1%:posnat :: .. :: uk%:posnat]`-based forms
  + bidirectional coercions `finfun_of_tuple : tuple_of >-> finfun_of`
    and `tuple_of_finfun : finfun_of >-> tuple_of`, letting a
    `k.-tuple T` and a `{ffun 'I_k -> T}` flow into either context
    transparently
  + indexing operations: `nindex`, `oindex`, and `tensor_nil`
  + tensor definitions `const_t`, `tensor1`, `nstack`, `ostack`,
    `nstack_tuple`, `ostack_tuple`, `ntensor_of_tuple`,
    `otensor_of_tuple`, `tuple_of_ntensor`, `tuple_of_otensor`,
    `matrix_of_tensor`, and `tensor_of_matrix`
  + tensor-reshaping operator `castt` (and lemmas `val_castt`,
    `castt_id`, `castt_comp`, `casttK`, `casttKV`), mirroring
    `castmx` at the tensor level
  + notation `_ *t _` for the tensor product (`*t%R` for the unary notation)
  + ring-instance support definitions `unitt`, `invt`
  + index bijections `tensor_index`, `tensor_unindex`,
    `tensor_dffun_index`, `tensor_dffun_unindex`, `tensormx_index`,
    `tensormx_unindex`, `prod_split`, `prod_unsplit`
  + `subType`, `eqType`, `choiceType`, `countType`, `finType`, `nmodType`,
    `zmodType`, `lSemiModType`, `lModType` instances inherited from `matrix`,
    `pzSemiRing`, `pzRing`, `comPzRing`, `nzSemiRing`, `nzRing`,
    `comNzRing`, and `unitRing` instances (using the Hadamard product),
    and a `bilinear` instance for the proper tensor product
  + `nmodMorphism` (over an `nmodType`) and `monoidMorphism` (over a
    `pzSemiRingType`) instances for `tensor_nil` and for `const_t`,
    so `raddfD`/`raddfN`/`raddf0` and `rmorphM`/`rmorph1` apply
    directly to `_.[::]` and to `const_t _`
  + nil-tensor lemmas `prod_nil`, `ord_prod_nil`, `tensor_nilK`,
    `const_tK`, `tensor_nil_eqP`, `tensor_nilV`
  + constant-tensor lemma `const_tV`
  + index-bijection lemmas `card_fprod_u`, `tensor_indexK`,
    `tensor_unindexK`, `tensor_index_bij`, `tensor_dffun_indexK`,
    `tensor_dffun_unindexK`, `tensor_dffun_index_bij`, `tensormx_cast`,
    `tensormx_indexK`, `tensormx_unindexK`
  + extensionality and computation lemmas `ntensorP`, `otensorP`,
    `ntensor_eqP`, `otensor_eqP`, `nstackE`, `ostackE`, `nstack_eqE`,
    `ostack_eqE`, `nstack_tupleE`, `ostack_tupleE`,
    `ntensor_of_tupleE`, `otensor_of_tupleE`, `tensor_of_matrixK`,
    `matrix_of_tensorK`
  + tensor-product lemmas `prod_fcat`, `prod_card`, `multsDl`,
    `multsDr`, `mults0l`, `mults0r`, `mults_const`, `multsNl`,
    `multsNr`, `mults_hmul`, `mults_scale`, `mults_hmul_compat`
- in `boot/finfun.v`
  + definition `cat_fun : forall A B : finType, (A -> T) -> (B -> T) -> (A + B -> T)`
  + lemmas `cat_inl` and `cat_inr`
  + definition `cat_ordfun : forall T (m n : nat), T ^ m -> T ^ n -> T ^ (m + n)`
  + lemmas `cat_lshift`, `cat_rshift`, `cat_ordfunK` and `cat_ordfun_comp`
  + multirule `cat_lrshift`
- in `boot/bigop.v`
  + lemma `big_cat_ordfun` for splitting `\big[op/idx]_(i < n + m) (F +++ G) i`
    into the product of the `n`- and `m`-indexed sub-bigops
- in `boot/ssrnat.v`
  + lemma `ltn_leq_trans`
    ([#1535](https://github.com/math-comp/math-comp/pull/1535))
