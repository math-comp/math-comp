# Ssreflect/MathComp 1.6 released

We are proud to announce the immediate availability of the
Ssreflect proof language and the Mathematical Components library
version 1.6 for Coq 8.4pl6 and 8.5beta3.

This release adds no new theory files.  The proof language 
received minor fixes while the libraries received minor additions.

A detailed ChageLog is available at:
  https://github.com/math-comp/math-comp/blob/master/etc/ChangeLog
Such document contains the list of new theorems as well as the list
of theorems that were renamed or replaced by more general variants.

The development is now taking place in the public and is mirrored
on github.  Another announcement specific to this will follow shortly.

The main user visible change is that the library was split into the following components:

  1. ssreflect: Ssreflect proof language, lists, boolean predicates, natural
     numbers, types with a decidable equality, finite types, finite sets, finite
     functions, finite graphs, basic arithmetics and prime numbers, big operators
  2. fingroup: finite groups, group quotients, group morphisms, group
     presentation, group action
  3. algebra: discrete algebraic structures as ring, fields, ordered fields,
     real fields, modules, algebras, vector spaces and integers, rational
     numbers, polynomials, matrices, vector spaces
  4. solvable: more definitions and theorems about finite groups
  5. field: field extensions, Galois theory, algebraic numbers, cyclotomic
     polynomials
  6. character: group representations, characters and class functions

A user not needing the entire library can build only the components she is
interested in.  Each component comes with a file one can Require and Import to
load, at once, the entire component.
For example "Require Import all_ssreflect." loads all the theory files in the
ssreflect component.

The main incompatibility concerning users is the change of logical/physical
path implied by the reorganization of the library.  In particular "Require
Ssreflect.ssreflect" does not work anymore.  We propose a schema that is
compatible with both Coq 8.4 and Coq 8.5, namely:
  Require Import mathcomp.ssreflect.ssreflect.
  From mathcomp Require Import ssrfun ssrbool ...
The first line loads the ssreflect plugin using its full path.
Then all other files are loaded from the mathcomp name space.
The component part (like ssreflect or algebra) is omitted.  All theory files in
the library follow this schema.
Note that the From directive has effect only in Coq 8.5.  Coq 8.4 ignores it
and searches for files in all known paths.  Beware of name collisions.

The tarball can be download at the following URL:
  http://ssr.msr-inria.inria.fr/FTP/mathcomp-1.6.tar.gz

The html documentation of the theory files can be browsed at:
  http://ssr.msr-inria.inria.fr/doc/mathcomp-1.6/

-- The Mathematical Components team

