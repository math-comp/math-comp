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
  default-bundle = "coq-master";

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
      "mathcomp-apery"
      "mathcomp-bigenough"
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
    hierarchy-builder = [
      "mathcomp-classical"
      "mathcomp-analysis"
    ];
    common-bundles = listToAttrs (forEach master (p:
      { name = p; value.override.version = "master"; }))
    // listToAttrs (forEach hierarchy-builder (p:
      { name = p; value.override.version = "hierarchy-builder"; }))
    // { mathcomp-ssreflect.main-job = true;
         mathcomp-doc.job = true;
       };
  in {
    "coq-master".push-branches = [ "master" "mathcomp-1" ];
    "coq-master".coqPackages = common-bundles // {
      coq.override.version = "proux01:dir";
      bignums.override.version = "master";
      paramcoq.override.version = "master";
      coq-elpi.override.version = "coq-master";
      hierarchy-builder.override.version = "master";
      interval.job = false;
      coquelicot.job = false;
    };
  };
}
