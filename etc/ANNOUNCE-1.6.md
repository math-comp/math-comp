# Ssreflect/MathComp 1.6 released

We are proud to announce the immediate availability of the
Ssreflect proof language and the Mathematical Components library
version 1.6 for Coq 8.4pl6 and 8.5beta3.

This release adds no new theory files.  The proof language
received minor fixes while the libraries received minor additions.

A detailed ChangeLog is available at:
  https://github.com/math-comp/math-comp/blob/master/etc/ChangeLog
This document contains the list of new theorems as well as the list
of theorems that were renamed or replaced by more general variants.

Our development repository is now public, and mirrored on github:
  https://github.com/math-comp/math-comp
An announcement specific to this new setting will follow shortly.

One major change for users is that the library has been split into
several components, by order of dependency:

  1. ssreflect: Ssreflect proof language, lists, boolean predicates, natural
     numbers, types with a decidable equality, finite types, finite
     sets and finite functions (over finite types), finite graphs,
     basic arithmetics and prime numbers, big (iterated) operators
  2. fingroup: finite groups, their quotients, morphisms,
     presentations, and actions
  3. algebra: discrete algebraic structures (rings, fields, modules,
     ordered fields, vector spaces...) and some of their instances like
     integers, rational numbers, polynomials, matrices
  4. solvable: more finite group theory: Sylow and Hall groups,
     composition series, A-series, maximal subgroups, nilpotent,
     abelian and solvable groups
  5. field: field extensions, Galois theory, algebraic numbers, cyclotomic
     polynomials
  6. character: group representations, class functions and characters

As a consequence users may select and download or compile only the
components they are interested in. Each component comes with a summary
file to be Require(d) and Import(ed) in order to load, at once, the
entire component. For example the command
  Require Import all_ssreflect.
loads all the theory files in the contained in the 'ssreflect'
component.

This modularity comes at the price of an incompatibility for users of
previous version of the Mathematical Components library, due to the
change of logical/physical paths implied by the reorganization of the
library. In particular the command line
  Require Ssreflect.ssreflect.
does not work anymore.  We propose a replacement schema for such
command lines that is compatible with both versions 8.4 and 8.5 of
Coq, namely replacing the previous line with:

  Require Import mathcomp.ssreflect.ssreflect.
  From mathcomp Require Import ssrfun ssrbool ...

The first line loads the ssreflect plugin using its full path.
Then all other files are loaded from the mathcomp name space.
The component part (like ssreflect or algebra) is omitted.  All theory files in
the library follow this schema.
Note that the From directive has effect only in Coq 8.5. Coq 8.4 ignores it
and searches for files in all known paths: hence beware of the
possible name collisions.

The tarball can be download at the following URL:
  http://ssr.msr-inria.inria.fr/FTP/mathcomp-1.6.tar.gz

The html documentation of the theory files can be browsed at:
  http://ssr.msr-inria.inria.fr/doc/mathcomp-1.6/

-- The Mathematical Components team
