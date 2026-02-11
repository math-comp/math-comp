{ mathcomp, coq, graphviz, version ? null }:
(mathcomp.override {single = true; withDoc = true; }).overrideAttrs (old: {
  nativeBuildInputs = [ graphviz coq.ocamlPackages.rocqnavi ];
  preBuild = old.preBuild
    + ''
      if [[ -f etc/rocqnavi_generate-hierarchy-graph.sh ]] then
        patchShebangs etc/rocqnavi_generate-hierarchy-graph.sh
      fi
    '';
  postBuild = "echo 'no post build'";
  postInstall = "echo 'no post install'";
})
