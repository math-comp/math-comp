# INSTALLATION PROCEDURE

Users familiar with OPAM can use such tool to install Coq and the Mathematical Components library with commands like

    opam repo add coq-released http://coq.inria.fr/opam/released
    opam install coq-mathcomp-fingroup

This document is for users that installed Coq in another way, for example
compiling it from sources.

## REQUIREMENTS

Coq version 8.5 to 8.7.0

## BUILDING

The Mathematical Components library is divided into various installation
units.  On can install the entire library (compilation time is around 35 minutes) or only some of its units.

In both cases, if Coq is not installed such that its binaries like `coqc`
and `coq_makefile` are in the PATH, then the COQBIN environment variable
must be set to point to the directory containing such binaries.
For example:

    export COQBIN=/home/user/coq/bin/

Now, to install the entire library, including the SSReflect proof language:

    cd mathcomp-1.6/mathcomp
    make -j2 && make install

If one wants to only install a few modules he should instead run make
inside the modules he wants to install *in the following order*:

  1. ssreflect
  2. fingroup
  3. algebra
  4. solvable
  5. field
  6. character

This means that one cannot install, say, algebra without having already
installed fingroup. An example:

    cd mathcomp-1.6/mathcomp
    cd ssreflect && make -j2 && make install
    cd ../fingroup && make -j2 && make install

## CUSTOMIZATION OF THE PROOF GENERAL EMACS INTERFACE

The `mathcomp/ssreflect/` directory comes with a small configuration file
`pg-ssr.el` to extend ProofGeneral (PG), a generic interface for
proof assistants based on the customizable text editor Emacs, to the
syntax of ssreflect.

The >= 3.7 versions of ProofGeneral support this extension.

- Following the installation instructions, unpack the sources of PG in
a directory, for instance <my-pgssr-location>/ProofGeneral-3.7, and add
the following line to your .emacs file.
Under Unix/MacOS:

    (load-file
      "<my-pg-location>/ProofGeneral-3.7/generic/proof-site.el" )
    (load-file "<my-pgssr-location>/pg-ssr.el")

Under Windows+Cygwin:

    (load-file
      "C:\\<my-pg-location>\\ProofGeneral-3.7\\generic\\proof-site.el")
    (load-file "<my-pgssr-location>\\pg-ssr.el")

Where <my-pg-location> is the location of your own ProofGeneral
directory, and where <my-pgssr-location> is the location of your pg-ssr.el
file.

Coq sources have a .v extension. Opening any .v file should
automatically launch ProofGeneral.
