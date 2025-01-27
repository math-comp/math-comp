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

  ## Indicate the relative location of your _CoqProject
  ## If not specified, it defaults to "_CoqProject"
  coqproject = "mathcomp/_CoqProject";

  cachix.coq = {};
  cachix.coq-community = {};
  cachix.math-comp.authToken = "CACHIX_AUTH_TOKEN";

  ## select an entry to build in the following `bundles` set
  ## defaults to "default"
  default-bundle = "coq-8.20";

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
      "mathcomp-real-closed"
      "mathcomp-zify"
      "multinomials"
      "odd-order"
      "reglang"
      "mathcomp-tarjan"
      "deriving"
      "extructures"
    ];
    common-bundles = listToAttrs (forEach master (p:
      { name = p; value.override.version = "master"; }))
    // { mathcomp-ssreflect.main-job = true;
         mathcomp-doc.job = true;
         coqeal.job = false;  # currently broken by https://github.com/coq/coq/pull/19228
         mathcomp-apery.job = false;  # reverse dependency of coqeal
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
    "coq-master".coqPackages = common-bundles // {
      coq.override.version = "master";
      stdlib.override.version = "master";
      bignums.override.version = "master";
      paramcoq.override.version = "master";
      coq-elpi.override.version = "master";
      coq-elpi.override.elpi-version = "2.0.7";
      hierarchy-builder.override.version = "master";
      interval.job = false;
      coquelicot.job = false;
      mathcomp-doc.job = false;  # currently broken (it's an unmaintainable pile of scripts)
    };
    "coq-9.0".coqPackages = common-bundles // {
      coq.override.version = "9.0";
      mathcomp-doc.job = false;  # currently broken (it's an unmaintainable pile of scripts)
      interval.job = false;
    };
    "coq-8.20".coqPackages = common-bundles // {
      coq.override.version = "8.20";
      # check that we compile without warnings on last release of Coq
      mathcomp-warnings.job = true;
      interval.job = false;
    };
    "coq-8.19".coqPackages = common-bundles // {
      coq.override.version = "8.19";
      interval.job = false;
    };
  };
}
