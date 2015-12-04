# Ssreflect/MathComp 1.6 released

We are proud to announce the immediate availability of the
Ssreflect proof language and the Mathematical Components library
version 1.6 for Coq 8.4pl6 and 8.5beta3.

This release adds no new theory files.  The proof language 
received minor fixes while the libraries received minor additions.

The developmet is now happening in the public and is mirrored
on github.  Another annoucment specific to this will follow shortly.

A detailed ChageLog is available at:
  https://github.com/math-comp/math-comp/blob/master/etc/ChangeLog
Such document contains the list of new theorems as well as the list
of theorems that were renamed or replaced by more general variants.

The main user visible change is that the library was split into the following components:

  1. ssreflect: the ssreflect proof language and ...
  2. fingroup: finite groups theory...
  3. algebra: ..
  4. solvable: ...
  5. field: ...
  6. character: ...

A user not needing the entire library can build only the components she
is interested in.  Each component comes with a file one can Require and Import to load, at once, the entire component.  For example "Require Import all_ssreflect." loads all the theory files in the ssreflect component.

The main incompatibility concerning users is the change of logical/phisical path implied by the reorganization of the library.  In particular "Require Ssreflect.ssreflect" does not work anymore.  We propose a schema
that is compatible with both Coq 8.4 and Coq 8.5, namely:
  Require Import mathcomp.ssreflect.ssreflect.
  From mathcomp Require Import ssrfun ssrbool ...
The first line loads the ssreflect plugin using its full path.
Then all other files are loaded from the mathcomp namespace.
The component part (like ssreflect or algebra) can be safely omitted.
All theory files in the library follow this schema.  Note that the
From directive has effect only in Coq 8.5.  Coq 8.4 ignores it and
searches for files in all known paths.  Beware of name collisions.

The tarball can be download at the following URL:
  http://ssr.msr-inria.inria.fr/FTP/mathcomp-1.6.tar.gz

The html documentation of the theory files can be browsed at:
  http://ssr.msr-inria.inria.fr/doc/mathcomp-1.6/

-- The Mathematical Components team

