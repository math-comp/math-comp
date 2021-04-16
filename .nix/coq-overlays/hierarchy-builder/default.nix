{ lib, mkCoqDerivation, which, coq, coq-elpi,
  version ? null, shim ? false }:

let installFlags =
      [ "DESTDIR=$(out)" "COQMF_COQLIB=lib/coq/${coq.coq-version}" ];
in
with lib; mkCoqDerivation ({
  pname = "hierarchy-builder" + optionalString shim "-shim";
  repo = "hierarchy-builder";
  owner = "math-comp";
  inherit version;
  defaultVersion = with versions; switch coq.coq-version [
    { case = isGe "8.12";         out = "1.0.0"; }
    { case = range "8.11" "8.12"; out = "0.10.0"; }
  ] null;
  release."1.0.0".sha256  = "0yykygs0z6fby6vkiaiv3azy1i9yx4rqg8xdlgkwnf2284hffzpp";
  release."0.10.0".sha256 = "1a3vry9nzavrlrdlq3cys3f8kpq3bz447q8c4c7lh2qal61wb32h";
  releaseRev = v: "v${v}";

  nativeBuildInputs = [ which ];
  propagatedBuildInputs = [ coq-elpi coq.ocaml ];
  inherit installFlags;

  meta = {
    description = "Coq plugin embedding ELPI.";
    maintainers = [ maintainers.cohencyril ];
    license = licenses.lgpl21;
  };
}
// optionalAttrs shim {
  buildFlags = [ "-C shim" ];
  installFlags = installFlags ++ [ "-C shim" ];
})
