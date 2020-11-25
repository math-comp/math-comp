{
  nixpkgs ? (if builtins.pathExists ./nixpkgs.nix then import ./nixpkgs.nix
             else fetchTarball https://github.com/NixOS/nixpkgs-channels/archive/502845c3e31ef3de0e424f3fcb09217df2ce6df6.tar.gz),
  config ? (if builtins.pathExists ./config.nix then import ./config.nix else {}),
  withEmacs ? false,
  print-env ? false,
  do-nothing ? false,
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
        "8.12" = coqPackages_8_12;
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
                    mca // {
                      propagatedBuildInputs = mca.propagatedBuildInputs ++
                                              (if builtins.elem coq.version ["8.10" "8.11" "8.12"] then (with coqPackages; [ coq-elpi hierarchy-builder ]) else []);
                    };
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
    } > default.nix

    updateNixPkgs (){
      HASH=$(git ls-remote https://github.com/NixOS/nixpkgs-channels refs/heads/nixpkgs-unstable | cut -f1);
      URL=https://github.com/NixOS/nixpkgs-channels/archive/$HASH.tar.gz
      SHA256=$(nix-prefetch-url --unpack $URL)
      echo "fetchTarball {
        url = $URL;
        sha256 = \"$SHA256\";
      }" > nixpkgs.nix
    }
    updateNixPkgsMaster (){
      HASH=$(git ls-remote https://github.com/NixOS/nixpkgs refs/heads/master | cut -f1);
      URL=https://github.com/NixOS/nixpkgs/archive/$HASH.tar.gz
      SHA256=$(nix-prefetch-url --unpack $URL)
      echo "fetchTarball {
        url = $URL;
        sha256 = \"$SHA256\";
      }" > nixpkgs.nix
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
  
  buildInputs = if do-nothing then []
                else (old.buildInputs ++
                (if pkgs.lib.trivial.inNixShell then pkgs.lib.optional withEmacs pkgs.emacs
                 else []));

  propagatedBuildInputs = if do-nothing then [] else old.propagatedBuildInputs;

}) else pkg
