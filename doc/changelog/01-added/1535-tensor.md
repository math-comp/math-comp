- new file `algebra/tensor.v`
  + types `'T[R]_(u_, d_)`, `'T_(u_, d_)` for tensors over `R` with
    contravariant dimensions `u_` and covariant dimensions `d_`
    (each a `{posnum nat} ^ k` finfun), and shorthands
    `'nT[R]_(u_)`, `'nT_(u_)` (purely contravariant) and
    `'oT[R]_(d_)`, `'oT_(d_)` (purely covariant), built from the
    variant `tensor` and its projection `tensor_val`
  + dimension notations `[dims n1; ..; nk]` (only parsing) and `[dims]`
  + indexing operations `t^^i`, ``` ``t`_i`` ```, `t^^=i`,
    ``` ``t`_=i`` ```, and the nullary projection `t.[::]`, with
    underlying definitions `nindex`, `oindex`, and `tensor_nil`
  + constructors `\tensor^^(i < n) Expr(i)`,
    ``` \tensor`_(j < n) Expr(j) ```, their `=>` variants, and the
    bracket notations `[tensor^^ t_0; ..; t_n]`,
    ``` [tensor`_ t_0; ..; t_n] ```, `[tensor^^= x_0; ..; x_n]`,
    ``` [tensor`_= x_0; ..; x_n] ```
  + dimension helpers `tensor_nil_f`, `fcons`, and `fcat`
  + tensor definitions `const_t`, `tensor1`, `nstack`, `ostack`,
    `nstack_tuple`, `ostack_tuple`, `ntensor_of_tuple`,
    `otensor_of_tuple`, `matrix_of_tensor`, and `tensor_of_matrix`
  + Hadamard (element-wise) product `t *h u` (definition `hmul`) and
    tensor product `t *t u` (definition `mults`), with `*%R` interpreted
    as the Hadamard product on tensors
  + ring-instance support definitions `unitt`, `invt`, and rewrite
    bundles `tensor_nilr_spec`, `const_tr_spec`
  + order definitions `le_t`, `lt_t`
  + index bijections `tensor_index`, `tensor_unindex`,
    `tensor_dffun_index`, `tensor_dffun_unindex`, `tensormx_index`,
    `tensormx_unindex`, `prod_split`, `prod_unsplit`
  + `subType`, `eqType`, `choiceType`, `countType`, `finType`, `nmodType`,
    `zmodType`, `lSemiModType`, `lModType` instances inherited from `matrix`,
    `pzSemiRing`, `pzRing`, `comPzRing`, `nzSemiRing`, `nzRing`,
    `comNzRing`, and `unitRing` instances (using the Hadamard product),
    a pointwise `POrder` instance, and a `bilinear` instance for the
    proper tensor product
  + nil-tensor lemmas `prod_nil`, `ord_prod_nil`, `tensor_nilK`,
    `const_tK`, `tensor_nil_eqP`, `tensor_nil_leP`, `tensor_nil_ltP`,
    `tensor_nilD`, `tensor_nilN`, `tensor_nilM`, `tensor_nilV`
  + constant-tensor lemmas `const_tD`, `const_tN`, `const_tM`,
    `const_tV`
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
- in `boot/ssrnat.v`
  + lemma `ltn_leq_trans`
    ([#1535](https://github.com/math-comp/math-comp/pull/1535)).
