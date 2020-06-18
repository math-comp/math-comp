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
  default-bundle = "coq-8.16";

  ## write one `bundles.name` attribute set per
  ## alternative configuration, the can be used to
  ## compute several ci jobs as well

  ## You can override Coq and other Coq coqPackages
  ## through the following attribute

  bundles = let
    master = [
      "mathcomp-bigenough"
      "deriving"
      "extructures"
    ];
    hierarchy-builder = [
      "coqeal"
      "coquelicot"
      "interval"
      "reglang"
      "fourcolor"
      "gaia"
      "graph-theory"
      "coq-bits"
      "mathcomp-classical"
      "mathcomp-analysis"
    ];
    hirarchy-builder = [
      "odd-order"
    ];
    proux01-hierarchy-builder = [
      "mathcomp-finmap"
      "mathcomp-real-closed"
      "multinomials"
      "mathcomp-zify"
      "mathcomp-abel"
    ];
    common-bundles = listToAttrs (forEach master (p:
      { name = p; value.override.version = "master"; }))
    // listToAttrs (forEach hierarchy-builder (p:
      { name = p; value.override.version = "hierarchy-builder"; }))
    // listToAttrs (forEach hirarchy-builder (p:
      { name = p; value.override.version = "hirarchy-builder"; }))
    // listToAttrs (forEach proux01-hierarchy-builder (p:
      { name = p; value.override.version = "proux01:hierarchy-builder"; }))
    // { mathcomp-ssreflect.main-job = true;
         mathcomp-doc.job = true;
       };
  in {
    "coq-master".coqPackages = common-bundles // {
      coq.override.version = "master";
      bignums.override.version = "master";
      paramcoq.override.version = "master";
      coq-elpi.override.version = "coq-master";
      hierarchy-builder.override.version = "coq-master";
      interval.job = false;
    };
    "coq-8.17".coqPackages = common-bundles // {
      coq.override.version = "8.17";
    };
    "coq-8.16".coqPackages = common-bundles // {
      coq.override.version = "8.16";
    };
  };
}
