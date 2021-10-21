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

A simple way to test modification of the CI configuration (new version
or configuration change of some package for instance) is through
overlays, see the corresponding paragraph at
https://github.com/coq-community/coq-nix-toolbox#overlays (for sha256
hashes, one can just put an empty string, run the `nix-build` command
above and an error will give the correct value).

### Updating nixpkgs

The nixpkgs version used is the one defined by the coq-nix-toolbox.
This can be overriden in `.nix/nixpkgs.nix`, which can be updated by
```shell
% nix-shell --run "updateNixpkgsMaster"
```
for the current master branch or
```shell
% nix-shell --run "updateNixpkgs owner branch"
```
for a specifi branch.
See the [coq-nix-toolbox README](https://github.com/coq-community/coq-nix-toolbox#available-shell-hooks)
for details.

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
