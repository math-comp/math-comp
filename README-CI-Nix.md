# MathComp CI

There are two main CI systems on math-comp repo:
* An OPAM based CI using gitlab, configured in `.gitlab-ci.yml`
  and using Docker images from https://hub.docker.com/r/coqorg/coq/
  and OPAM packages from https://github.com/coq/opam-coq-archive
  This CI is outside the scope of the current document.
* A Nix based CI based on top of packages of nixpkgs
  https://github.com/NixOS/nixpkgs and the coq-nix-toolbox
  https://github.com/coq-community/coq-nix-toolbox
  This is further document here.

## Nix Based CI

### Local Installation and Nix Usage

See this great wiki page
https://github.com/math-comp/math-comp/wiki/Using-nix for how to
install Nix and use it locally to enjoy CI caching and speed up your
development process.

### Rerunning a CI Task Locally

You can take example of the files `.github/workflows/nix-action-coq-*.yml`
For instance, to rerun multinomials for Coq 8.12 :
```shell
% nix-build --argstr bundle "coq-8.12" --argstr job multinomials
```
The list of bundles can be found in `.nix/config.nix`.

### Test CI Configurations with Overlays

For simple overlays, it's enough to add a line in the .nix/config.nix
file (look for "overlay" there).

For more elaborate overlays (for instance editing package dependencies),
a simple way to test modification of the CI configuration (new version
or configuration change of some package for instance) is through
overlays, see the corresponding paragraph at
https://github.com/coq-community/coq-nix-toolbox#overlays (for sha256
hashes, one can just put an empty string, run the `nix-build` command
above and an error will give the correct value).

### Updating coq-nix-toolbox

Once overlays are satisfactory, they should eventually be merged into
the nixpkgs package repository.

The file `.nix/coq-nix-toolbox.nix` contains the git commit hash of
the version of coq-nix-toolbox used (c.f.,
https://github.com/coq-community/coq-nix-toolbox ). Coq-nix-toolbox
itself contains the git commit hash of the version of nixpkgs it uses
(c.f. https://github.com/NixOS/nixpkgs/ ). So in order to add or
remove a Nix derivation (package), one needs to first update nixpkgs,
then coq-nix-toolbox and finally the `.nix/coq-nix-toolbox.nix` file
here. See the [coq-nix-toolbox README](https://github.com/coq-community/coq-nix-toolbox#testing-coqpackages-updates-in-nixpkgs)
for details of the process.

### Learning Nix basics

Basic concepts of the Nix package manager:
https://nixos.org/manual/nix/stable/ (I particularly recommend
[Part I. introduction](https://nixos.org/manual/nix/stable/#chap-introduction) and
[Chapter 9. Basic Package Management](https://nixos.org/manual/nix/stable/#ch-basic-package-mgmt))

Nix is based on its own functional language:
[Part IV. Writing Nix Expressions](https://nixos.org/manual/nix/stable/#chap-writing-nix-expressions)

Specifics for Coq packages: [15.5. Coq and coq packages](https://nixos.org/manual/nixpkgs/unstable/#sec-language-coq)

### Caching

The CI uses caching provided by https://www.cachix.org/ and there is a
token in the math-comp organization to authenticate and store the
results. Any CI build is stored globally and can be used on one's own
computer as described in
https://github.com/math-comp/math-comp/wiki/Using-nix
