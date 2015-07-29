# The Mathematical Components repository

This repository holds the Mathematical Components Library for the Coq system:
and extensive body of mathematics formalized in the Coq/SSReflect language.

It also contains the proof of the Odd Order Theorem, that builds on top
of the Mathematical Components library.

# Layout and compilation of the library

The library is divided into packages that group together related
files and that define a distribution and compilation unit.

Packages can be compiled using the traditional `make` utility or
the more recent `OPAM` one.

We provide a convenience root Makefile to compile all packages
at once using `make`.  This is the simplest option.

We provide `opam` files to compile each package using `OPAM`.
Note that `OPAM` packages for the Mathematical Components library
are available in the standard repositories of Coq related packages
under the `coq:mathcmop:` name space.  If you are just interested
in installing a Mathematical Components package via `OPAM`, follow
the standard instructions on the Coq website.

## Compilation and installation with make

The instructions assume you are in the `mathcomp` directory and that
you have a supported version of Coq.
The list of Coq versions that a known to work can be obtained with:
```
ls ssreflect/plugin/
```
Alternatively, if you are familiar with the `OPAM` slang:
```
grep depends: ssreflect/opam
```

If `coqc` is in your `PATH`, then you are good to go.  Alternatively you
can export the `COQBIN` variable to tell make where the `coqc` binary is:
```
export COQBIN=/home/gares/COQ/coq/bin/
```

To compile the entire library just type `make`. If you have parallel
hardware then `make -j 3` is probably a faster option. 

The files can be edited using CoqIDE or Proof General, or any
other editor that understands the `_CoqProject` file, with no
further configuration from the `mathcomp` directory.
```
coqide basic/div.v
```
Note that you may need to enable `_CoqProject` processing in your
editor (e.g. the default for CoqIDE is to ignore it).

To install the compiled library, just type `make install`.

## Compilation and installation with OPAM

The instructions assume you are in the `mathcomp` directory
and that you have `OPAM` installed and configured with the
standard Coq repositories.

For each package, pin the `opam` file:
```
opam pin -n add ssreflect
```
This can be achieved in one go as follows:
```
for P in */opam; do opam pin -n add ${P%%/opam}; done
```

Then you can use `opam install` to compile and install any package.
For example:
```
opam install coq.8.5.dev coq:mathcomp:basic
```
