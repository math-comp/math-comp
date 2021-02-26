{ config ? {}, withEmacs ? false, print-env ? false, do-nothing ? false,
  update-nixpkgs ? false, ci-matrix ? false, ci-step ? null,
  override ? {}, ocaml-override ? {}, global-override ? {},
  ci ? (!isNull ci-step), inNixShell ? null, src ? ./.,
}@args:
let auto = fetchGit {
  url = "https://github.com/coq-community/coq-nix-toolbox.git";
  ref = "master";
# putting a ref here is strongly advised
  rev = "94cd57651a9468c8e6dca2e533561a887649efbc";
};
in
(import auto ({inherit src;} // args)).nix-auto
