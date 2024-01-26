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
      "coquelicot"
      "interval"
    ];
    common-bundles = listToAttrs (forEach master (p:
      { name = p; value.override.version = "master"; }))
    // { mathcomp-ssreflect.main-job = true;
         mathcomp-doc.job = true;
         mathcomp-bigenough.job = false;
         reglang.job = false;
         deriving.job = false;
       };
  in {
    "coq-master".push-branches = [ "mathcomp-1" "master" ];
    "coq-master".coqPackages = common-bundles // {
      coq.override.version = "master";
      coq-elpi.override.version = "coq-master";
      hierarchy-builder.override.version = "master";
      interval.job = false;
    };
    "coq-8.19".push-branches = [ "mathcomp-1" "master" ];
    "coq-8.19".coqPackages = common-bundles // {
      coq.override.version = "8.19";
      interval.job = false;
    };
    "coq-8.18".push-branches = [ "mathcomp-1" "master" ];
    "coq-8.18".coqPackages = common-bundles // {
      coq.override.version = "8.18";
    };
    "coq-8.17".push-branches = [ "mathcomp-1" "master" ];
    "coq-8.17".coqPackages = common-bundles // {
      coq.override.version = "8.17";
    };
    "coq-8.16".push-branches = [ "mathcomp-1" "master" ];
    "coq-8.16".coqPackages = common-bundles // {
      coq.override.version = "8.16";
    };
  };
}
