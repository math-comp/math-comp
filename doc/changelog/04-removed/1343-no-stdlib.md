- in `ssrnat.v`
  + requirements for `BinNat`, `Ndec` and `Ring` from Stdlib. You may
    need to add some explicit requirements, the most common one being
    `From Coq Require Setoid`, but we also observed `BinPos`, `Pnat`,
    `Ring_theory`, `RelationClasses`, `Wf_nat` and `List`
  + lemmas `nat_of_add_bin`, `nat_of_mul_bin`, `nat_of_exp_bin`,
    `nat_semi_ring`, `nat_semi_morph` and `nat_power_theory`
  + definition `extend_number` (was a coercion)
  + tactic `nat_litteral`
  + ring instance for `nat` (use algebra-tactics instead)
    ([#1343](https://github.com/math-comp/math-comp/pull/1343),
    by Pierre Roux).

- in `rat.v`
  + lemmas `rat_ring_theory` and `rat_field_theory`
  + ring and field instances for `rat` (use algebra-tactics instead)
    ([#1343](https://github.com/math-comp/math-comp/pull/1343),
    by Pierre Roux).
