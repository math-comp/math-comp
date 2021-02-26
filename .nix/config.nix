{
  format = "1.0.0";
  coq-attribute = "mathcomp-single";
  pname = "mathcomp";
  namespace = "mathcomp";
  realpath = "mathcomp";
  select = "coq-8.13";
  inputs."coq-8.13".coqPackages = {
    coq.override.version = "8.13";
    hierarchy-builder.override.version = "master";
  };
  inputs."coq-8.13".ocamlPackages.elpi.override.version = "v1.13.0";
}
