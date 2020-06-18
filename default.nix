# This file was generated from `meta.yml`, please do not edit manually.
# Follow the instructions on https://github.com/coq-community/templates to regenerate.
{ config ? {}, withEmacs ? false, print-env ? false, do-nothing ? false,
  update-nixpkgs ? false, ci ? false, ci-step ? null, inNixShell ? null
}@args:
let src = fetchGit "https://github.com/coq-community/nix-toolbox.git"; in
(import "${src}/auto-config.nix" ./. args).nix-auto