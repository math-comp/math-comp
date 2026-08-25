- in `algebra/algebraic_hierarchy/`
  + new file `algebraic_hierarchy.v` exports all the other files of the
    directory. While it enables a bulk import similar to the deprecated file
    `ssralg.v`, the new file exports `countalg.v`, `finalg.v`, and
    `ring_quotient.v`, and does not export `nmodule.v` (which belongs to the
    `boot` package) and the deprecated definitions and lemmas that have been
    moved to `ssralg.v`
    ([#1642](https://github.com/math-comp/math-comp/pull/1642),
    fixes [#1505](https://github.com/math-comp/math-comp/issues/1505)).
- in `algebra/numeric_hierarchy/`
  + new file `numeric_hierarchy.v` exports all the other files of the directory.
    While it enables a bulk import similar to the deprecated file `ssrnum.v`,
    the new file does not export `orderedzmod.v` (which belongs to the `order`
    package) and the deprecated definition `Num.ExtraDef.sqrtr`
    ([#1642](https://github.com/math-comp/math-comp/pull/1642),
    fixes [#1505](https://github.com/math-comp/math-comp/issues/1505)).
