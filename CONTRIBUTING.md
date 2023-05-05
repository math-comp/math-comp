# Contribution Guide for the Mathematical Components library

We describe here best practices for contributing to the library. In
particular we explain what conventions are used in the library. When
contributing, you should comply to these conventions to get your code
integrated to the library.

This file is not comprehensive yet and might still contain mistakes or
unclear indications, please consider contributing to its improvement.

## Proof style

### General guidelines
- One important guideline is to structure proofs in blocks, i.e.,
  forward steps, to limit the scope of errors.
  + See [G. Gonthier, A. Mahboubi, "An introduction to small scale reflection in Coq", p.103](https://doi.org/10.6092/issn.1972-5787/1979) for an illustration
- **A line should have no more than 80 characters**. If a line is
longer than that, it should be cut semantically. If there is no way to
make a semantic cut (e.g. the user provides an explicit term that is
too long to fit on one line), then just cut it over several lines to
make it readable.
- Lines end with a point `.` and only have `;` inside them.
- Lines that close a goal must start with a terminator (`by` or
  `exact`). You should consider using an editor that highlights those
  terminators in a specific color (e.g. red).
- Chaining too many optional rewrites makes error detection hard. The idiom is
  ```
  rewrite conditional_rule ?simplify_side_condition // next_rule.
  ```
- Do not use `Focus` or `{}`, use the relevant [indentation](#indentation-in-proof-scripts),
  along with terminators like `by` or `exact`.

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

## Statements of lemmas, theorems and definitions

- Universal quantifications with dependent variable should appear on the left hand side of the colon, until we reach the first non dependent variables. e.g.
  `Lemma example x y : x < y -> x >= y = false`

### Term style
- Operators are surrounded by space, for example `n*m` should be written `n * m`.
This particular example can be problematic if matrix.v is imported because then, `M *m N` is matrix product.

### Statement-macros

- There is a number of "macros" that are available to state lemmas, like `commutative`, `associative`,...
  (see [`ssrfun.v`](https://github.com/coq/coq/blob/master/theories/ssr/ssrfun.v))

- There are also macros that are available to localize a statement, like `{in A, P}`,...
  (see [`ssrbool.v`](https://github.com/coq/coq/blob/master/theories/ssr/ssrbool.v))

### Naming of variables
- Variable/hypothesis names follow the following conventions.
  + Hypothesis should not be named `H`, `H'`,... (these collide with
  subgroup variable conventions) but have meaningful names. For
  example, an hypothesis `n > 0` should be named `n_gt0`.
  + Induction Hypotheses are prefixed by `IH` or `ih` (e.g. induction hypothesis on `n` is called `IHn`).
  + Natural numbers and integers should be named `m`, `n`, `p`, `d`, ...
  + Elements of another ring should be named `x`, `y`, `z`, `u`, `v`, `w`, ...
  + Polynomials should be named by lower case letter `p`, `q`, `r` ... (to avoid collision with properties named `P`, `Q`, ...)
  + Matrices should be named `A`, `B`, ..., `M`, `N`, ...
  + Polymorphic variables should be named `x`, ...
- Variables/hypotheses that do not survive the line can be introduced using `?`.
- Variables/hypotheses with a very short scope (~ 1-5 lines) can have a short name.
- Variables/hypotheses with a longer scope (> 5 lines) must have a meaningful name.

### Naming conventions for lemmas (non exhaustive)
#### Names in the library usually obey one of the following conventions
 - `(condition_)?mainSymbol_suffixes`
 - `mainSymbol_suffixes(_condition)?`
Or in the presence of a property denoted by an n-ary or unary predicate:
 - `naryPredicate_mainSymbol+`
 - `mainSymbol_unaryPredicate`
There is an underscore before "suffixes" when "suffixes" starts with a one-letter small identifier (i.e., not a capital letter or a number or a longer identifier such as "if"). Since the intent is to make the "suffixes" readable enough, there are exceptions for short names (e.g., `lern1`).

#### Where:
 - `mainSymbol` is the most meaningful part of the lemma. It generally is the head symbol of the right-hand side of an equation or the head symbol of a theorem. It can also simply be the main object of study, head symbol or not. It is usually either
   + one of the main symbols of the theory at hand. For example, it will be `opp`, `add`, `mul`, etc., or
   + a special "canonical" operation, such as a ring morphism or a
     subtype predicate. e.g. `linear`, `raddf`, `rmorph`, `rpred`, etc.
 - "condition" is used when the lemma applies under some hypothesis.
 - "suffixes" are there to refine what shape and/or what other symbols the lemma has. It can either be the name of a symbol ("add", "mul", etc.), or the (short) name of a predicate ("`inj`" for "`injectivity`", "`id`" for "identity", etc.) or an abbreviation.

Abbreviations are in the header of the file which introduces them. We list here the main abbreviations.
  - `A` -- associativity, as in `andbA : associative andb`
  - `AC` -- right commutativity
  - `ACA` -- self-interchange (inner commutativity), e.g., `orbACA : (a || b) || (c || d) = (a || c) || (b || d)`
  - `b` -- a boolean argument, as in `andbb : idempotent andb`
  - `C` -- commutativity, as in `andbC : commutative andb`
        -- alternatively, predicate or set complement, as in `predC`
        -- alternatively, constant
  - `CA` -- left commutativity
  - `D` -- predicate or set difference, as in `predD`
  - `E` -- elimination lemma, as in `negbFE : ~~ b = false -> b`
  - `F` or `f` -- boolean false, as in `andbF : b && false = false`
  - `F` -- alternatively, about a finite type
  - `g` -- a group argument.
  - `I` -- left/right injectivity, as in `addbI : right_injective addb`
        -- alternatively predicate or set intersection, as in `predI`
  - `l` -- the left-hand of an operation, as in
    + `andb_orl : left_distributive andb orb`
    + ``ltr_norml x y : (`|x| < y) = (- y < x < y)``
  - `L` -- the left-hand of a relation, as in `ltn_subrL : n - m < n = (0 < m) && (0 < n)`
  - `LR` -- moving an operator from the left-hand to the right-hand of an relation, as in `leq_subLR : (m - n <= p) = (m <= n + p)`
  - `N` or `n` -- boolean negation, as in `andbN : a && (~~ a) = false`
  - `n` -- alternatively, it is a natural number argument
  - `N` -- alternatively ring negation, as in `mulNr : (- x) * y = - (x * y)`
  - `P` -- a characteristic property, often a reflection lemma, as in
     `andP : reflect (a /\ b) (a && b)`
  - `r` -- a right-hand operation, as in
    + `orb_andr : right_distributive orb andb`
    + ``ler_normr x y : (x <= `|y|) = (x <= y) || (x <= - y)``
    + alternatively, it is a ring argument
  - `R` -- the right-hand of a relation, as in `ltn_subrR : n < n - m = false`
  - `RL` -- moving an operator from the right-hand to the left-hand of an relation, as in `ltn_subRL : (n < p - m) = (m + n < p)`
  - `T` or `t` -- boolean truth, as in `andbT: right_id true andb`
  - `T` -- alternatively, total set
  - `U` -- predicate or set union, as in `predU`
  - `W` -- weakening, as in `in1W : {in D, forall x, P} -> forall x, P`
  - `0` -- ring or nat 0, or empty set, as in `addr0 : x + 0 = x`
  - `1` -- ring; nat or group 1, as in `mulr1 : x * 1 = x`
  - `D` -- addition, as in `linearD : f (u + v) = f u + f v`
  - `B` -- subtraction, as in `opprB : - (x - y) = y - x`
  - `M` -- multiplication, as in `invfM : (x * y)^-1 = x^-1 * y^-1`
  - `Mn` -- ring nat multiplication, as in `raddfMn : f (x *+ n) = f x *+ n`
  - `V` -- multiplicative inverse, as in `mulVr : x^-1 * x = 1`
  - `X` -- exponentiation, as in `rmorphXn : f (x ^+ n) = f x ^+ n`
    + `Xn` -- nat exponentiation
    + `Xz` -- int exponentiation
  - `Z` -- (left) module scaling, as in `linearZ : f (a *: v)  = s *: f v`
  - `z` -- an int argument
  - `p` -- positive number, as in `ltr_pM2l x : 0 < x -> {mono *%R x : x y / x < y}`
  - `n` -- negative number
  - `w` -- non strict (weak) monotony, as in `ler_wpM2r x : 0 <= x -> {homo *%R^~ x : y z / y <= z}`
  - `wp` -- non-negative number
  - `wn` -- non-positive number


#### Special naming conventions (non exhaustive)
- For the infix membership predicate `_ \in _`, the prefix `in_` is used for lemmas that unfold specific predicates, possibly propagating the infix membership (e.g, `in_cons` or `in_set0`). These lemmas are generally part of the `inE` multirule. Other lemmas involving the infix membership predicated use the generic prefix `mem_` (e.g., `mem_head` or `mem_map`).

#### Typical search pattern
- `Search _ "prefix" "suffix"* (symbol|pattern)* in library.` (for coq < 8.12)
- `Search "prefix" "suffix"* (symbol|pattern)* inside library.` (for coq >= 8.12)

### Naming conventions for definitions (non exhaustive)

- types of mathematical structures
  + Mixed case, the first letter lowercase and the first letter of each internal
    word capitalized, end with `Type`
  + e.g., `unitRingType`
- HB structures
  + Mixed case, the first letter of each internal word capitalized
  + e.g., `UnitRing`
- interfaces (mixins, factories)
  + when the interface sits at the bottom of a hierarchy: mixed case, starts
    with `is` or `has`, the first letter of each internal word capitalized
    * e.g., `hasChoice`, `isZsemimodule`
  + when the interface extends a structure `A`: `A_isB` or `A_hasB` where `B`
    is mixed case, the first letter of each internal word capitalised
    * e.g., `Zsemimodule_isZmodule`, `Zmodule_isRing`, `SemiRing_hasCommutativeMul`
    * exception: `Choice_` can be omitted
- Coq Modules:
  - Mixed case, the first letter of each internal word capitalized
  - e.g., `NumDomain` in `ssrnum.v`

#### Abbreviations
- The following are considered as single words and are abbreviated when used as prefixes
  - Z-module becomes `zmod`/`Zmod`, e.g., `ZmodType` in `ssralg.v`, `normedZmodType` in `ssrnum.v`
  - L-module becomes `lmod`/`Lmod`
  - L-algebra becomes `lalg`/`Lalg`
- Partial order is abbreviated to `porder` or `POrder`, e.g., `porderType`, `CanPOrderMixin` in `order.v`

## Doc style
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

## Instantiating structures with Hierarchy Builder

First
```Coq
From HB Require Import structures.
```

The structure names can be founs in the header comments, for instance,
the `eqType` structure is defined in
[`eqtype.v`](https://github.com/math-comp/math-comp/blob/master/mathcomp/ssreflect/eqtype.v).
Basic information about structures can be obtained via `HB.about`, for
instance

```Coq
HB.about eqType.
```

### Regular factories

Factories enabling to build a structure can be discovered with
`HB.howto`, for instance

```Coq
HB.howto eqType.
```

tells us that `eqType` instances can be built with `hasDecEq.Build`.
(Note that by default `HB.howto` may not return all the available factories;
it might be necessary to increase the depth search using a natural number
as in `HB.howto xyzType 5`.)
One can then

```Coq
HB.about hasDecEq.Build.
```

to learn that `hasDecEq.Build` is expecting a type `T`, a predicate
`eq_op : rel T` (implicit argument, as indicated by the square
brackets) and proof of `Equality.axiom eq_op`. One can thus
instantiate an `eqType` on some type `T` with

```Coq
HB.instance Definition _ := hasDecEq.Build T proof_of_Equality_axiom.
```

or

```Coq
HB.instance Definition _ := @hasDecEq.Build T eq_op proof_of_Equality_axiom.
```

which should output a few lines among which:

```Coq
module_T__canonical__eqtype_Equality is defined
```

(beware that the output may not be visible by default with VSCoq).
Absence of such a line indicates failure of the command.

### Aliases / feather factories

In addition to the regular factories, listed by `HB.howto`, the
library defines some aliases (aka feather factories). Those aliases
are documented in the header comments. For instance, an `eqType`
instance on some type `T` can be derived from some `T'` already
equipped with an `eqType` structure, given a function `f : T -> T'`
and a proof `injf : injective f`

```Coq
HB.instance Definition _ := Equality.copy T (inj_type injf).
```

### Listing instances on a given type

Instances a type is already equipped with can be listed with
`HB.about`, for instance

```Coq
HB.about bool.
```

lists all the structures `bool` is already equipped with.

### Graph of the hierarchy

A graph of the hierarchy can be obtained with

```Coq
HB.graph "hierarchy.dot".
```

then

```shell
tred hierarchy.dot | xdot
```

or

```shell
tred hierarchy.dot | dot -Tpng > hierarchy.png
```

## Adding new structures with Hierarchy Builder

See the
[documentation of Hierarchy Builder](https://github.com/math-comp/hierarchy-builder#readme).
