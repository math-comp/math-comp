# Contribution Guide for the Mathematical Components library

We describe here best practices for contributing to the library. In
particular we explain what conventions are used in the library. When
contributing, you should comply to these conventions to get your code
integrated to the library.

This file is not comprehensive yet and might still contain mistakes or
unclear indications, please consider contributing.

## Proof style.
### General guidelines
- **A line should have no more than 80 characters**. If a line is
longer than that, it should be cut semantically. If there is no way to
make a semantic cut (e.g. the user provides an explicit term that is
too long to fit on one line), then just cut it over several lines to
make it readable.
- Lines end with a point `.` and only have `;` inside them.
- Lines that close a goal must start with a terminator (`by` or
  `exact`). You should consider using an editor that highlight those
  terminators in a specific color (e.g. red).

### Spaces
We write
- `move=>` and `move:` (no space between `move` and `=>` or `:`)
- `apply/` and `apply:` (no space between `apply` and `/` or `:`)
- `rewrite /definition` (there is a space between `rewrite` and an unfold)

### Indentation in proof scripts
- When two subgoals are created, the first subgoal is indented by 2
  spaces, the second is not. Use `last first` to bring the
  smallest/less meaningful goal first, and keep the main flow of the
  proof unindented.
- When more than two subgoals are created, bullets are used `-` for
  the first level, `+` for the second and `*` for the third as in:
  ```
  tactic.
  - tactic.
    + tactic.
      * tactic.
      * tactic.
      * tactic.
    + tactic.
    + tactic.
  - tactic
  - tactic
  ```

  If all the subgoals have the same importance, use bullets for all of
  them, however, if one goal is more important than the others
  (i.e. is main flow of the proof). Then you might remove the bullet
  for this last one and unindent it as in:
  ```
  tactic.
  - tactic. (* secondary subgoal 1 *)
  - tactic. (* secondary subgoal 2 *)
  tactic. (* third subgoal is the main one *)
  ```

## Statements of lemmas, theorems and definitions.

- Universal quantifications with dependent variable should appear on the left hand side of the colon, until we reach the first non dependent variables. e.g.
  `Lemma example x y : x < y -> x >= y = false`

### Term style.
- Operators are surrounded by space, for example `n*m` should be written `n * m`.
This particular example can be problematic if matrix.v is imported because then, `M *m N` is matrix product.

### Naming of variables
- Variable names follow the following conventions.
  + Hypothesis should not be named `H`, `H'`,... (these collide with
  subgroup variable conventions) but have meaningful names. For
  example, an hypothesis `n > 0` should be named `n_gt0`.
  + Induction Hypotheses are prefixed by `IH` or `ih` (e.g. induction hypothesis on `n` is called `IH`).
  + Natural numbers and integers should be named `m`, `n`, `p`, `d`, ...
  + Elements of another ring should be named `x`, `y`, `z`, `u`, `v`, `w`, ...
  + Polynomials should be named by lower case letter `p`, `q`, `r` ... (to avoid collision with properties named `P`, `Q`, ...)
  + Matrices should be named `A`, `B`, ..., `M`, `N`, ...
