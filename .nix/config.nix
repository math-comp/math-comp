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

  ## select an entry to build in the following `tasks` set
  ## defaults to "default"
  default-task = "coq-8.13";

  ## write one `tasks.name` attribute set per
  ## alternative configuration, the can be used to
  ## compute several ci jobs as well

  ## You can override Coq and other Coq coqPackages
  ## through the following attribute

  tasks."coq-8.13".coqPackages.coq.override.version = "8.13";
  tasks."coq-8.12".coqPackages.coq.override.version = "8.12";
  tasks."coq-8.11".coqPackages.coq.override.version = "8.11";
}
