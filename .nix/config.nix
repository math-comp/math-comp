with builtins; with (import <nixpkgs> {}).lib;
{
  ## DO NOT CHANGE THIS
  format = "1.0.0";
  ## unless you made an automated or manual update
  ## to another supported format.

  ## The attribute to build, either from nixpkgs
  ## of from the overlays located in `.nix/coq-overlays`
  attribute = "mathcomp";

  ## If you want to select a different attribute
  ## to serve as a basis for nix-shell edit this
  shell-attribute = "mathcomp-single";

  ## Set this when the package has no rocqPackages version yet
  ## (either in nixpkgs or in .nix/rocq-overlays)
  no-rocq-yet = true;

  ## Indicate the relative location of your _CoqProject
  ## If not specified, it defaults to "_CoqProject"
  coqproject = "_CoqProject";

  cachix.coq = {};
  cachix.coq-community = {};
  cachix.math-comp.authToken = "CACHIX_AUTH_TOKEN";

  ## select an entry to build in the following `bundles` set
  ## defaults to "default"
  default-bundle = "rocq-9.0";

  ## write one `bundles.name` attribute set per
  ## alternative configuration, the can be used to
  ## compute several ci jobs as well

  ## You can override Coq and other Coq coqPackages
  ## through the following attribute

  bundles = let
    master = [
      "coq-bits"
      "coqeal"
      "coquelicot"
      "ExtLib"
      "fourcolor"
      "gaia"
      "graph-theory"
      "interval"
      "mathcomp-abel"
      "mathcomp-algebra-tactics"
      "mathcomp-analysis"
      "mathcomp-apery"
      "mathcomp-bigenough"
      "mathcomp-classical"
      "mathcomp-finmap"
      "mathcomp-infotheo"
      "mathcomp-real-closed"
      "mathcomp-word"
      "mathcomp-zify"
      "multinomials"
      "odd-order"
      "QuickChick"
      "reglang"
      "simple-io"
      "mathcomp-tarjan"
      "deriving"
      "extructures"
    ];
    common-bundles = listToAttrs (forEach master (p:
      { name = p; value.override.version = "master"; }))
    // { mathcomp-boot.main-job = true;
         mathcomp-doc.job = true;
         mathcomp.job = false;
         stdlib.job = true;
         # jasmin.override.version = "main";
         jasmin.job = false;  # broken since https://github.com/math-comp/math-comp/pull/1256
         # (see https://github.com/jasmin-lang/jasmin/pull/1093 for details)
         ssprove.override.version = "main";
         # To add an overlay applying to all bundles,
         # add below a line like
         #<package>.override.version = "<github_login>:<branch>";
         # where
         # * <package> will typically be one of the strings above (without the quotes)
         #   or look at https://github.com/NixOS/nixpkgs/tree/master/pkgs/development/coq-modules
         #   for a complete list of Coq packages available in Nix
         # * <github_login>:<branch> is such that this will use the branch <branch>
         #   from https://github.com/<github_login>/<repository>
       };
  in {
    "rocq-master" = { rocqPackages = {
      rocq-core.override.version = "master";
      stdlib.override.version = "master";
      bignums.override.version = "master";
      rocq-elpi.override.version = "master";
      rocq-elpi.override.elpi-version = "3.0.1";
      hierarchy-builder.override.version = "master";
      mathcomp.job = false;
    }; coqPackages = common-bundles // {
      coq.override.version = "master";
      stdlib.override.version = "master";
      bignums.override.version = "master";
      coq-elpi.override.version = "master";
      coq-elpi.override.elpi-version = "3.0.1";
      hierarchy-builder.override.version = "master";
      interval.job = false;
      coquelicot.job = false;
      ssprove.job = false;
      mathcomp-infotheo.job = false;  # not compatible with master
    }; };
    "rocq-9.1" = { rocqPackages = {
      rocq-core.override.version = "9.1";
    }; coqPackages = common-bundles // {
      coq.override.version = "9.1";
      coq-elpi.job = true;
      hierarchy-builder.job = true;
      # check that we compile without warnings on last release of Coq
      mathcomp-warnings.job = true;
      interval.job = false;  # not yet compatible with 9.1
      mathcomp-infotheo.job = false;  # not yet compatible with 9.1
      ssprove.job = false;  # not yet compatible with 9.1
    }; };
    "rocq-9.0" = { rocqPackages = {
      rocq-core.override.version = "9.0";
    }; coqPackages = common-bundles // {
      coq.override.version = "9.0";
      coq-elpi.job = true;
      hierarchy-builder.job = true;
      # check that we compile without warnings on last release of Coq
      mathcomp-warnings.job = true;
      mathcomp-infotheo.job = false;  # not yet compatible with 9.0
      odd-order.job = false;  # odd-order dropped support for 9.0
    }; };
    "coq-8.20".coqPackages = common-bundles // {
      coq.override.version = "8.20";
      coq-elpi.override.version = "2.5.0";  # required by CoqEAL
      coq-elpi.override.elpi-version = "2.0.7";
      odd-order.job = false;  # odd-order dropped support for 8.20
    };
  };
}
