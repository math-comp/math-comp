{ config ? {}, withEmacs ? false, print-env ? false, do-nothing ? false,
  update-nixpkgs ? false, ci-matrix ? false, ci-job ? null,
  override ? {}, ocaml-override ? {}, global-override ? {},
  ci ? (!isNull ci-job), inNixShell ? null, src ? ./.,
}@args:
let auto = fetchGit {
  url = "https://github.com/coq-community/coq-nix-toolbox.git";
  ref = "master";
# putting a ref here is strongly advised
  rev = import .nix/coq-nix-toolbox.nix;
};
in
(import auto ({inherit src;} // args)).nix-auto
