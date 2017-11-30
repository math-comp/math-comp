[![Build Status](https://travis-ci.org/math-comp/math-comp.svg?branch=master)](https://travis-ci.org/math-comp/math-comp)

# The Mathematical Components repository

The Mathematical Components Library is an extensive body of
mathematics formalized in the Coq/SSReflect language.

This repository also contains a
[mechanization](https://hal.archives-ouvertes.fr/hal-00816699/) of the
[Odd Order
Theorem](https://en.wikipedia.org/wiki/Feit%E2%80%93Thompson_theorem),
which utilizes the library extensively.

## Installation

If you already have OPAM installed:

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-ssreflect
```

Additional packages go by the name of `coq-mathcomp-algebra`,
`coq-mathcomp-field`, etc... See [INSTALL](INSTALL.md) for detailed
installation instructions in other scenarios.

## How to get help

- The [ssreflect mailing
  list](https://sympa.inria.fr/sympa/info/ssreflect) is the primary
  venue for help and questions about the library.
- The [MathComp wiki](https://github.com/math-comp/math-comp/wiki)
  contains many useful information, including including a list of
  [tutorials](https://github.com/math-comp/math-comp/wiki/tutorials)
- The [Mathematical Components Book](https://math-comp.github.io/mcb/)
  provides a comprehensive introduction to the library.
- Experienced users hang around at
  [StackOverflow](https://stackoverflow.com/questions/tagged/ssreflect)
  listening to the `ssreflect` and `coq` tags.

## Publications and Tools using MathComp

[Papers](https://github.com/math-comp/math-comp/wiki/Publications) 
using the Mathematical Components library can be found at the
[wiki](https://github.com/math-comp/math-comp/wiki)
