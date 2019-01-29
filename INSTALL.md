# Layout and compilation of the library

The library is divided into packages which group together related
files. Each package defines a distribution and compilation unit.

Packages can be compiled using the traditional make utility or
the more recent OPAM one. The released and current dev versions are
also available as OPAM packages.

## Compilation and installation of released and current dev version with OPAM
If you just installed OPAM you may have to do the following. You may also want
to read [OPAM user manual](https://opam.ocaml.org/doc/Usage.html) first. 
```
opam init
eval $(opam config env)
```
Once your OPAM environment is configured
you can install any math-comp package via
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam pin add -n coq -k version 8.8.0
opam install coq -j3
opam install coq-mathcomp-ssreflect.1.7.0 -j3
```
Replace `ssreflect` here by the package you want, the dependencies will be
installed automatically. We recommend pinning a particular version of Coq
(here `8.8.0`).
To get the latest development version you need to execute the following:
```
opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
opam install coq-mathcomp-ssreflect.dev -j3
```

## Compilation and installation in a dedicated OPAM root

If you want to install the library in a dedicated environment
(let's name it `MC`) which will remain independent from your
current OPAM setup you can run the following commands:
```
opam init --root=$PWD/MC
eval $(opam config env --root=$PWD/MC`)
```
After that the installations instructions above apply.

Coq and the library are installed in the `$PWD/MC` directory
(called an OPAM root). To discard the OPAM root, simply delete
the directory.

## Compilation and installation with make

The instructions assume you are in the `mathcomp` directory and that
you have a supported version of Coq: 8.6, 8.7 or 8.8.

If `coqc` is in your `PATH`, then you are good to go.  Alternatively, you
can export the `COQBIN` variable to tell `make` where the `coqc` binary is:
```
export COQBIN=/home/gares/COQ/coq/bin/
```

To compile the entire library just type `make`. If you have parallel
hardware then `make -j 3` is probably a faster option. 

The files can be edited using CoqIDE or Proof General, or any
other editor that understands the `_CoqProject` file, with no
further configuration from the `mathcomp` directory.
```
coqide ssreflect/div.v
```
Note that you may need to enable `_CoqProject` processing in your
editor (e.g. the default for CoqIDE is to ignore it).

To install the compiled library, just execute `make install`.

## Compilation and installation of a custom version using OPAM

The instructions assume you are in the parent directory (that contains
this file `INSTALL.md`) and that you have OPAM installed and
configured with the standard Coq repositories.

First, we recommend pinning a particular version of Coq
(here `8.8.0`):
```
opam pin add -n coq -k version 8.8.0
```

Then for each math-comp package, pin the `opam` file:
```
opam pin add -n -k path coq-mathcomp-ssreflect .
```

This can be achieved in one go as follows:
```
for P in *.opam; do opam pin add -n -k path ${P%.opam} .; done
```

Then you can use `opam install` to compile and install any package.
For example:
```
opam install coq-mathcomp-character -j3
```
