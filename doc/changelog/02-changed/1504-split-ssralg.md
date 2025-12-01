- `ssralg.v` is split into the following four files in `algebra/alg/`:
  + `algebra.v` contains the (semi)ring, (semi)module, and (semi)algebra
    structures below `unitRingType`, their morphisms, and their theory.
  + `divalg.v` contains the structures with (partial) multiplicative inverse
    `GRing.inv` (`unitRingType`, `comUnitRingType`, `unitAlgType`,
    `comUnitAlgType`, `idomainType`, and `fieldType`) and their theory.
  + `decfield.v` contains the reflection of the first order theory of rings
    (`GRing.term`, `GRing.formula`, etc.), decidable fields (`decFieldType`),
    algebraically closed fields (`closedFieldType`), and their theory.
  + `ssralg.v` re-exports the contents of the above three files to provide the
    compatibility layer for the old `ssralg.v`.
  + NB: Users are encouraged to import only what they need among the new files
    `algebra.v`, `divalg.v`, and `decfield.v` instead of importing `ssralg.v`.
    However, users need to pay attention to the following points in porting
    their code to the new files:
    * The new files, e.g., `divalg.v`, do not re-export their dependencies,
      e.g., `algebra.v` and `nmodule.v`. Users need to explicitly import the
      files they need.
    * Each of the new files provide `GRing` and `GRing.Theory` modules as in the
      old `ssralg.v`, the `GRing.Theory` modules re-export the other
      `GRing.Theory` modules that the former ones depend on. Therefore,
      importing `GRing.Theory` without any qualifier (e.g., not
      `divalg.GRing.Theory`) should suffice to import all the required
      results, *given that the libraries are imported in the dependency order*
      (`nmodule.v`, `algebra.v`, `divalg.v`, and then `decfield.v`).
    * All the declarations deprecated at this point are moved to `ssralg.v`.
      Therefore, all the deprecation warning messages rooted from `ssralg.v`
      has to be addressed before removing the import of `ssralg.v`
    ([#1504](https://github.com/math-comp/math-comp/pull/1504)).
