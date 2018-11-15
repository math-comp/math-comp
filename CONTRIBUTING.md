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

### Naming conventions (Non exhaustive)
#### Names in the library usually obey one of following the convention
 - `(condition_)?mainSymbol_suffixes`
 - `mainSymbol_suffixes(_condition)?`
Or in the presence of a property denoted by a nary or unary predicate:
 - `naryPredicate_mainSymbol+`
 - `mainSymbol_unaryPredicate`
#### Where :
 - `mainSymbol` is the most meaningful part of the lemma. It generally is the head symbol of the right-hand side of an equation or the head symbol of a theorem. It can also simply be the main object ofstudy, head symbol or not. It is usually either
  - one of the main symbols of the theory at hand. For example, it will be `opp`, `add`, `mul`, etc...
  - or a special "canonical" operation, such as a ring morphism or a
    subtype predicate. e.g. `linear`, `raddf`, `rmorph`, `rpred`, etc ...
 - "condition" is used when the lemma applies under some hypothesis.
 - "suffixes" are there to refine what shape and/or what other symbols  the lemma has. It can either be the name of a symbol ("add", "mul",  etc...), or the (short) name of a predicate ("`inj`" for "`injectivity`", "`id`" for "identity", ...) or an abbreviation.
Abbreviations are in the header of the file which introduce them. We list here the main abbreviations.
  - `A` -- associativity, as in `andbA : associative andb.`
  - `AC` -- right commutativity.
  - `ACA` -- self-interchange (inner commutativity), e.g., `orbACA : (a || b) || (c || d) = (a || c) || (b || d).`
  - `b` -- a boolean argument, as in `andbb : idempotent andb.`
  - `C` -- commutativity, as in `andbC : commutative andb`,
        -- alternatively, predicate or set complement, as in `predC.`
  - `CA` -- left commutativity.
  - `D` -- predicate or set difference, as in `predD.`
  - `E` -- elimination lemma, as in `negbFE : ~~ b = false -> b`.
  - `F` or `f` -- boolean false, as in `andbF : b && false = false.`
  - `g` -- a group argument
  - `I` -- left/right injectivity, as in `addbI : right_injective addb` 
        -- alternatively predicate or set intersection, as in `predI.`
  - `l` -- a left-hand operation, as `andb_orl : left_distributive andb orb.`
  - `N` or `n` -- boolean negation, as in `andbN : a && (~~ a) = false.`
  - `n` -- alternatively, it is a natural number argument,
  - `N` -- alternatively ring negation, as in `mulNr : (- x) * y = - (x * y).`
  - `P` -- a characteristic property, often a reflection lemma, as in
     `andP : reflect (a /\ b) (a && b)`.
  - `r` -- a right-hand operation, as `orb_andr : right_distributive orb andb.`
      -- alternatively, it is a ring argument
  - `T` or `t` -- boolean truth, as in `andbT: right_id true andb.`
        -- alternatively, total set
  - `U` -- predicate or set union, as in `predU`.
  - `W` -- weakening, as in `in1W : {in D, forall x, P} -> forall x, P.`
  - `0` -- ring or nat 0, or empty set, as in `addr0 : x + 0 = x.`
  - `1` -- ring; nat or group 1, as in `mulr1 : x * 1 = x.`
  - `D` -- addition, as in `linearD : f (u + v) = f u + f v.`
  - `B` -- subtraction, as in `opprB : - (x - y) = y - x.`
  - `M` -- multiplication, as in `invfM : (x * y)^-1 = x^-1 * y^-1.`
  - `Mn` -- ring nat multiplication, as in `raddfMn : f (x *+ n) = f x *+ n.`
  - `V` -- multiplicative inverse, as in `mulVr : x^-1 * x = 1.`
  - `X` -- exponentiation, as in `rmorphX : f (x ^+ n) = f x ^+ n.`
  - `Z` -- (left) module scaling, as in `linearZ : f (a *: v)  = s *: f v.`
  - `z` -- an int argument
#### Typical search pattern
`Search _ "prefix" "suffix"* (symbol|pattern)* in library.`

## Doc style.
### Header documentary comments
We try to document types, definitions and notations precisely, but only describe
the lemmas and theorems in general terms, because we don't want to discourage users
from actually reading the documentation.
There are some exceptions for some particularly important theorems.

### Commenting source code
The MathComp library uses exclusively block comments, with 80-character lines
enclosed in the `(*` / `*)` delimiters, e.g.
```
(* Lorem ipsum dolor sit amet, consectetuer adipiscing elit.  Donec hendrerit *)
(* tempor tellus.  Donec pretium posuere tellus.  Proin quam nisl, tincidunt  *)
(* et, mattis eget, convallis nec, purus.                                     *)
```
Multiline comments are strictly limited to out-commented code.
