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
  default-bundle = "coq-8.18";

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
         # To add an overlay applying to all bundles,
         # add below a line like
         #<package>.override.version = "<github_login>:<branch>";
         # where
         # * <package> will typically be one of the strings above (without the quotes)
         #   or look at https://github.com/NixOS/nixpkgs/tree/master/pkgs/development/coq-modules
         #   for a complete list of Coq packages available in Nix
         # * <github_login>:<branch> is such that this will use the branch <branch>
         #   from https://github.com/<github_login>/<repository>
         mathcomp-analysis.override.version = "math-comp:hb-semilattices";
         mathcomp-classical.override.version = "math-comp:hb-semilattices";
         multinomials.override.version = "math-comp:hb-semilattices";
         deriving.override.version = "pi8027:hb-semilattices";
       };
  in {
    "coq-master".push-branches = [ "master" "mathcomp-1" ];
    "coq-master".coqPackages = common-bundles // {
      coq.override.version = "master";
      bignums.override.version = "master";
      paramcoq.override.version = "master";
      coq-elpi.override.version = "coq-master";
      hierarchy-builder.override.version = "master";
      interval.job = false;
      coquelicot.job = false;
    };
    "coq-8.19".push-branches = [ "master" "mathcomp-1" ];
    "coq-8.19".coqPackages = common-bundles // {
      coq.override.version = "8.19";
      interval.job = false;
    };
    "coq-8.18".push-branches = [ "master" "mathcomp-1" ];
    "coq-8.18".coqPackages = common-bundles // {
      coq.override.version = "8.18";
    };
  };
}
