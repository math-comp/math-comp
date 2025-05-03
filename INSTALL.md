# Layout and compilation of the library

The library is divided into packages which group together related
files. Each package defines a distribution and compilation unit.

Packages can be compiled using the traditional make utility or
the more recent OPAM one (version 2). The released and current dev versions are
also available as OPAM packages.

## Compilation and installation of released and current dev version with OPAM

If you just installed OPAM version 2 you should proceed as follows: 
```
opam --version  # should print 2.x.y
opam init -n --comp=ocaml-base-compiler.4.14.2
eval $(opam config env)
```
Once your OPAM environment is configured
you can install any math-comp package via
```
opam repo add rocq-released https://rocq-prover.org/opam/released
opam pin add -n rocq-core -k version 9.0.0
opam install rocq-core -j3
opam install rocq-mathcomp-boot -j3
```
Replace `boot` here by the package you want, the dependencies will be
installed automatically. We recommend pinning a particular version of Rocq
(we give `9.0.0` as an example, see `CHANGELOG.md` for the supported versions).
To get the latest development version you need to execute the following:
```
opam repo add rocq-extra-dev https://rocq-prover.org/opam/extra-dev
opam install rocq-mathcomp-boot.dev -j3
```
You can learn more about OPAM by reading its
[user manual](https://opam.ocaml.org/doc/Usage.html).

## Compilation and installation in a dedicated OPAM root

If you want to install the library in a dedicated environment
(let's name it `MC`) which will remain independent from your
current OPAM setup you can run the following commands:
```
opam init --root=$PWD/MC
eval $(opam config env --root=$PWD/MC`)
```
After that the installations instructions above apply.

Rocq and the library are installed in the `$PWD/MC` directory
(called an OPAM root). To discard the OPAM root, simply delete
the directory.

## Compilation and installation with make

The instructions assume you have a supported version of Rocq
(listed in `CHANGELOG.md`).

If `rocq` is in your `PATH`, then you are good to go. Alternatively, you
can export the `COQBIN` variable to tell `make` where the `coqc` binary is:
```
export COQBIN=/home/username/COQ/coq/bin/
```

You also need to install
[Hierarchy-Builder](https://github.com/math-comp.hierarchy-builder).

To compile the entire library just type `make`. If you have parallel
hardware then `make -j 3` is probably a faster option. 

The files can be edited using CoqIDE or Proof General, or any
other editor that understands the `_CoqProject` file, with no
further configuration from the `mathcomp` directory.
```
coqide boot/div.v
```
Note that you may need to enable `_CoqProject` processing in your
editor (e.g. the default for CoqIDE is to ignore it).

To install the compiled library, just execute `make install`.

## Compilation and installation of a custom version using OPAM

The instructions assume you are in the parent directory (that contains
this file `INSTALL.md`) and that you have OPAM installed and
configured with the standard Coq repositories.

First, we recommend pinning a particular version of Coq
(e.g. `9.0.0`):
```
opam pin add -n rocq-core -k version 9.0.0
```

Then for each math-comp package, pin the `opam` file:
```
opam pin add -n -k path rocq-mathcomp-boot .
```

This can be achieved in one go as follows:
```
for P in rocq*.opam; do opam pin add -n -k path ${P%.opam} .; done
```

Then you can use `opam install` to compile and install any package.
For example:
```
opam install rocq-mathcomp-character -j3
```
