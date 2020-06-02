{
  nixpkgs ? (if builtins.pathExists ./nixpkgs.nix then import ./nixpkgs.nix
             else fetchTarball https://github.com/CohenCyril/nixpkgs/archive/mathcomp-fix-rec.tar.gz),
  config ? (if builtins.pathExists ./config.nix then import ./config.nix else {}),
  withEmacs ? false,
  print-env ? false,
  package ? (if builtins.pathExists ./package.nix then import ./package.nix else "mathcomp-fast"),
  src ? (if builtins.pathExists ./package.nix then ./. else false)
}:
with builtins;
let
  cfg-fun = if isFunction config then config else (pkgs: config);
  pkg-src = if src == false then {}
            else { ${if package == "mathcomp.single" then "mathcomp" else package} = src; };
  pkgs = if isAttrs nixpkgs then nixpkgs else import nixpkgs {
    overlays = [ (pkgs: super-pkgs: with pkgs.lib;
      let coqPackages = with pkgs; {
        "8.7" = coqPackages_8_7;
        "8.8" = coqPackages_8_8;
        "8.9" = coqPackages_8_9;
        "8.10" = coqPackages_8_10;
        "8.11" = coqPackages_8_11;
        "default" = coqPackages_8_10;
      }.${(cfg-fun pkgs).coq or "default"}.overrideScope'
        (coqPackages: super-coqPackages:
          let
            all-pkgs = pkgs // { inherit coqPackages; };
            cfg = pkg-src // {
              mathcomp-fast = {
                src = ./.;
                propagatedBuildInputs = with coqPackages; ([ mathcomp ] ++ mathcomp-extra-fast);
              };
              mathcomp-full = {
                src = ./.;
                propagatedBuildInputs = with coqPackages; ([ mathcomp ] ++ mathcomp-extra-all);
              };
            } // (cfg-fun all-pkgs);
          in {
            mathcomp-extra-config =
              let mec = super-coqPackages.mathcomp-extra-config; in
              lib.recursiveUpdate mec {
                initial = {
                  # fixing mathcomp analysis to depend on real-closed
                  mathcomp-analysis = {version, coqPackages} @ args:
                    let mca = mec.initial.mathcomp-analysis args; in
                    mca // (
                      if elem version [ "master" "cauchy_etoile" "holomorphy" ]
                      then {
                        propagatedBuildInputs = mca.propagatedBuildInputs ++
                                                [coqPackages.mathcomp-real-closed];
                      } else {});
                };
                for-coq-and-mc.${coqPackages.coq.coq-version}.${coqPackages.mathcomp.version} =
                  (super-coqPackages.mathcomp-extra-config.${coqPackages.coq.coq-version}.${coqPackages.mathcomp.version} or {}) //
                  (removeAttrs cfg [ "mathcomp" "coq" "mathcomp-fast" "mathcomp-full" ]);
              };
            mathcomp = if cfg?mathcomp then coqPackages.mathcomp_ cfg.mathcomp else super-coqPackages.mathcomp;
          } // mapAttrs
            (package: version: coqPackages.mathcomp-extra package version)
            (removeAttrs cfg ["mathcomp" "coq"])
        ); in {
          coqPackages = coqPackages.filterPackages coqPackages.coq coqPackages;
          coq = coqPackages.coq;
          mc-clean = src: {
            version = baseNameOf src;
            src = cleanSourceWith {
              src = cleanSource src;
              filter = path: type: let baseName = baseNameOf (toString path); in ! (
                hasSuffix ".aux" baseName ||
                hasSuffix ".d" baseName ||
                hasSuffix ".vo" baseName ||
                hasSuffix ".glob" baseName ||
                elem baseName ["Makefile.coq" "Makefile.coq.conf" ".mailmap" ".git"]
              );
            };
          };
        })];
  };

  mathcompnix = ./.;

  shellHook = ''
    nixEnv () {
      echo "Here is your work environement"
      echo "buildInputs:"
      for x in $buildInputs; do printf "  "; echo $x | cut -d "-" -f "2-"; done
      echo "propagatedBuildInputs:"
      for x in $propagatedBuildInputs; do printf "  "; echo $x | cut -d "-" -f "2-"; done
      echo "you can pass option --arg config '{coq = \"x.y\"; math-comp = \"x.y.z\";}' to nix-shell to change coq and/or math-comp versions"
    }
    printEnv () {
      for x in $buildInputs; do echo $x; done
      for x in $propagatedBuildInputs; do echo $x; done
    }
    cachixEnv () {
      echo "Pushing environement to cachix"
      printEnv | cachix push math-comp
    }
    nixDefault () {
      cat $mathcompnix/default.nix
    }
  ''
  + pkgs.lib.optionalString print-env "nixEnv";

  emacs = with pkgs; emacsWithPackages
    (epkgs: with epkgs.melpaStablePackages; [proof-general]);

  pkg = with pkgs;
        if package == "mathcomp.single" then coqPackages.mathcomp.single
        else coqPackages.${package} or (coqPackages.current-mathcomp-extra package);
in
if pkgs.lib.trivial.inNixShell then pkg.overrideAttrs (old: {
  inherit shellHook mathcompnix;
  buildInputs = (old.buildInputs or []) ++ pkgs.lib.optional withEmacs emacs;
}) else pkg
