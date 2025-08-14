- in `ssrnat.v`
  + lemmas `neq_doubleS_double` and `predn_doubleS`
    ([#1448](https://github.com/math-comp/math-comp/pull/1448)).

- in `ssrint.v`
  + lemmas `NegzS` and `Negz_doubleS`
    ([#1448](https://github.com/math-comp/math-comp/pull/1448)).

- new file `binnums.v`
  ([#1448](https://github.com/math-comp/math-comp/pull/1448)).

- in `binnums.v`
  + definitions `pos_nat`, `int_of_Z`, `Zint`, `rat_of_Q` and `Qrat`
  + variants `pos_nat_spec`, `Zint_spec` and `Qrat_spec`
  + lemmas `pos_nat_Pos_to_nat`, `iter_opDdoubler`, `pos_natP`,
    `pos_nat_ind`, `Pos_to_nat_gt0`, `Pos_to_nat0F`, `pos_nat_exS`,
    `pos_nat_double`, `pos_nat_doubleS`, `pos_natS`, `pos_natD`,
    `pos_nat_pred_double`, `pos_natM`, `pos_nat_eq`,
    `pos_nat_compare`, `pos_nat_le`, `Pos_to_natI`, `Pos_to_nat1`,
    `Pos_to_nat_double`, `Pos_to_nat_doubleS`, `Pos_to_natS`,
    `Pos_to_natD`, `Pos_to_nat_pred_double`, `Pos_to_natM`,
    `Zint_int_of_Z`, `ZintP`, `Zint0`, `Zint_pos`, `Zint_neg`,
    `Zint_double`, `Zint_succ_double`, `Zint_pred_double`,
    `Zint_pos_sub`, `ZintD`, `ZintN`, `ZintB`, `ZintM`, `Zint_eq`,
    `Zint_le`, `Qrat_rat_of_Q`, `QratP`, `Qrat_spec_Q_to_rat`,
    `Qrat1`, `Qrat_Qmake`, `intr_pos_nat_neq0`, `QratD`, `QratM`,
    `QratN`, `QratB`, `Qrat_eq`, `Qrat_le` and `QratV`
  + multirules `pos_natE`, `Pos_to_natE` and `ZintE`
    ([#1448](https://github.com/math-comp/math-comp/pull/1448)).

- new file `lra.v`
  ([#1448](https://github.com/math-comp/math-comp/pull/1448)).

- in `lra.v`
  + tactics `lra`, `nra`, `psatz` and `psatz <n>`
    Beware that:
    * on Coq 8.20 `From mathcomp Require Import lra` is incompatible
      with the use of mathcomp-algebra-tactics or the lia/lra tactics
      from Stdlib in any reverse dependency.
    * on Rocq 9.0 and 9.1, the addition of the line
      `From mathcomp Require all_algebra. (* remove this line when requiring Rocq > 9.1`
      may be needed at the *beginning* of reverse dependency files
      that aren't (transitively) requiring it yet but use
      mathcomp-algebra-tactics or lia/lra from Stdlib.
    * on Rocq >= 9.2 things should work smoothly
    ([#1448](https://github.com/math-comp/math-comp/pull/1448)).
