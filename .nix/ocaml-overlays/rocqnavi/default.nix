{
  lib,
  stdenv,
  fetchFromGitHub,
  ocaml,
  findlib,
  dune-glob,
  yojson,
}:

let
  version = "0.4.0";
  sha256 = "sha256-b4IqVAwL3iCI5CnZ9crEUlUxxwlyuS11xnomnqozcWs=";
  rev = "rocqnavi.${version}";
in
stdenv.mkDerivation {
  pname = "ocaml${ocaml.version}-rocqnavi";
  inherit version;

  src = fetchFromGitHub {
    owner = "affeldt-aist";
    repo = "rocqnavi";
    inherit rev sha256;
  };

  nativeBuildInputs = [
    ocaml
    findlib
  ];
  propagatedBuildInputs = [ dune-glob yojson ];

  installFlags = [ "PREFIX=$(out)" ];

  meta = {
    homepage = "https://github.com/affeldt-aist/rocqnavi";
    description = "Extension of coq2html Document Generator";
    license = lib.licenses.gpl2;
    maintainers = [ lib.maintainers.proux01 ];
  };
}
