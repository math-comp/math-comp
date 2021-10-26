# Changelog (unreleased)

To avoid having old PRs put changes into the wrong section of the CHANGELOG,
new entries now go to the present file as discussed
[here](https://github.com/math-comp/math-comp/wiki/Agenda-of-the-April-23rd-2019-meeting-9h30-to-12h30#avoiding-issues-with-changelog).

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

### Added

- in `bigop.v`, added lemma `leq_prod`
- in `path.v`, added lemma `sortedP`
- in `seq.v`, added statement `size_take_min`

- in `ssralg.v`
  + number notation in scope ring_scope, numbers such as `12` or `42`
    are now read as `12%:R` or `42%:R`

- in `rat.v`
  + Number Notation for numbers of the form `-? [0-9][0-9_]* ([.][0-9_]+)?`
    in scope `rat_scope` (for instance 12%Q or 3.14%Q)

- in `ssrint.v`
  + number notation in scope int_scope, `12` or `-42`
    are now read as `Posz 12` or `Negz 41`

- in `ssrint.v`
  + number notation in scope ring_scope, numbers such as `-12` are now
    read as `(-12)%:~R`

- in `bigop.v`, added lemmas `telescope_big`, `telescope_sumn` and `telescope_sumn_in`
- in `seq.v`, added statement `size_take_min`.
- in `bigop.v`:
  + `leq_bigmax_seq`, `bigmax_leqP_seq`, `bigmax_sup_seq`

- in `fintype.v`, added lemmas `enum_ord0`, `enum_ordSl`, `enum_ordSr`

- in `ssrbool.v`, added lemma `all_sig2_cond`
- in `choice.v`, added coercion `Choice.mixin`
- In `seq.v`, added lemmas `mkseqS`, `mkseq_uniqP`
- in `eqtype.v`:
  + notations `eqbLHS` and `eqbRHS`

- in `order.v`:
  + notations `leLHS`, `leRHS`, `ltLHS`, `ltRHS`

- in `ssrnat.v`:
  + notations `leqLHS`, `leqRHS`, `ltnLHS`, `ltnRHS`

- in `seq.v`, added lemmas `nth_seq1`, `set_nthE`, `count_set_nth`,
  `count_set_nth_ltn`, `count_set_nthF`
- in `ssrbool.v`
  + lemmas `can_in_pcan`, `pcan_in_inj`, `in_inj_comp`, `can_in_comp`, `pcan_in_comp`
  + definition `pred_oapp`
  + lemams `ocan_in_comp`, `eqbLR`, `eqbRL`

- in `ssrfun.v`
  + definition `olift`
  + lemmas `obindEapp`, `omapEbind`, `omapEapp`, `oappEmap`, `omap_comp`,
    `oapp_comp`, `oapp_comp_f`, `olift_comp`, `compA`, `ocan_comp`

- in `ssralg.v`
  + missing export for `eqr_div`

- in `tuple.v`:
  + lemma `tuple_uniqP`

- in `seq.v`, added lemma `subseq_anti`
  + notation `\- f` for definition `opp_fun`
  + lemmas `opp_fun_is_additive` and `opp_fun_is_scalable`
  + canonical instances `opp_fun_additive` and `opp_fun_linear`
  + notation `f \* g` for definition `mul_fun`

- in `order.v`
  + notation `f \min g` and `f \max g` for definitions `min_fun` and `max_fun`
- in `ssrnum.v`,
  + added lemmas `mulCii`, `ReE`, `ImE`, `conjCN1`, `CrealJ`, `eqCP`,
    `eqC`, `ImM`, `ImMil`, `ReMil`, `ImMir`, `ReMir`, `ReM`,
    `invC_Crect`, `ImV`, `ReV`, `rectC_mulr`, `rectC_mull`,
    `divC_Crect`, `divC_rect`, `Im_div`, `Re_div`.
  + adding resolution of `'Re x \in Num.real` and `'Im x \in Num.real`
    as in `Hint Extern` to `core` database.

- in `ssrbool.v`, added `homo_mono1`.

### Changed

- in `rat.v`
  + `zeroq` and `oneq` (hence `0%Q` and `1%Q`) are now the evaluation
    of terms `fracq (0, 1)` and `fracq (1, 1)` (and not the term
    themselves), the old and new values are convertible and can be
    easily converted with `rewrite -[0%Q]valqK -[1%Q]valqK`

- in `order.v`
  + fix `[distrLatticeType of T with disp]` notation

- in `fintype.v`
  + `enum_ordS` now a notation
- The following notations are now declared in `type_scope`:
  + `{tuple n of T}` and `{bseq n of T}` in `tuple.v`,
  + `{subset T}` and `{subset [d] T}` in `order.v`,
  + `{morphism D >-> T}` in `morphism.v`,
  + `{acts A, on S | to}` and `{acts A, on group G | to}` in `action.v`,
  + `{additive U -> V}`, `{rmorphism R -> S}`, `{linear U -> V}`,
    `{linear U -> V | s}`, `{scalar U}`, `{lrmorphism A -> B}`,
    `{lrmorphism A -> B | s}` in `ssralg.v`,
  + `{poly R}` in `poly.v`,
  + `{quot I}` and `{ideal_quot I}` in `ring_quotient.v`, and
  + `{ratio T}` and `{fraction T}` in `fraction.v`.

- in `gproduct.v`
  + put notations `G ><| H`, `G \* H` and `G \x H` in `group_scope`
- in `ssrnum.v`
  + locked definitions `Re` and `Im`.

### Renamed

- in `ssrbool.v`, renamed `mono2W_in` to `mono1W_in` (was misnamed).

### Removed

- in `ssrbool.v`:
  + notations `{pred T}`, `[rel _ | _]`, `[rel _ in _]`, `xrelpre`
    (now in ssrbool in Coq)
  + definitions `PredType`, `simpl_rel`, `SimplRel`, `relpre`
    (now in ssrbool in Coq)
  + coercion `rel_of_simpl_rel` deprecated for `rel_of_simpl`
    (in ssrbool in Coq)
  + lemmas `simpl_pred_sortE`, `homo_sym`, `mono_sym`, `homo_sym_in`,
    `mono_sym_in`, `homo_sym_in11`, `mono_sym_in11`, `onW_can`, `onW_can_in`,
    `in_onW_can`, `onS_can`, `onS_can_in`, `in_onS_can`, `homoRL_in`,
    `homoLR_in`, `homo_mono_in`, `monoLR_in`, `monoRL_in`, `can_mono_in`,
    `inj_can_sym_in_on`, `inj_can_sym_on`, `inj_can_sym_in`, `contra_not`,
    `contraPnot`, `contraTnot`, `contraNnot`, `contraPT`, `contra_notT`,
    `contra_notN`, `contraPN`, `contraFnot`, `contraPF`, `contra_notF`
    (now in ssrbool in Coq, beware that `simpl_pred_sortE`,
    `contra_not`, `contraPnot`, `contraTnot`, `contraNnot`,
    `contraPT`, `contra_notT`, `contra_notN`, `contraPN`,
    `contraFnot`, `contraPF`, `contra_notF` have different implicit
    arguments and the order of arguments changes in `homoRL_in`,
    `homoLR_in`, `homo_mono_in`, `monoLR_in`, `monoRL_in`,
    `can_mono_in`)

- in `ssreflect.v`:
  + structure `NonPropType.call_of`, constructor `Call` and field `callee`
    (now in ssreflect in Coq)
  + definitions `maybeProp`, `call` (now in ssreflect in Coq)
  + structure `NonPropType.test_of`, constructor `Test` and field `condition`
    (now in ssreflect in Coq, beware that implicit arguments of `condition`
    differ)
  + definitions `test_Prop`, `test_negative` (now in ssreflect in Coq)
  + structure `NonPropType.type`, constructor `Check` and fields `result`,
    `test`, `frame` (now in ssreflect in Coq, beware that implicit arguments
    of `Check` differ)
  + definition `check` (now in ssreflect in Coq, beware that implicit
    arguments of `check` differ)
  + notation `[apply]`, `[swap]`, `[dup]` in scope `ssripat_scope`
    (now in ssreflect in Coq)

- in `ssrfun.v`:
  + lemmas `Some_inj`, `of_voidK`, `inj_compr` (now in ssrfun in Coq,
    beware that implicit arguments of `inj_compr` differ)
  + notation `void` (now in ssrfun in Coq)
  + definition `of_void` (now in ssrfun in Coq)

### Infrastructure

- in `builddoc_lib.sh`:
  + change the sed command that removes all starred lines

### Misc
