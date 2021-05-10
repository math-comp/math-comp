{ mathcomp, coq, coq-elpi, hierarchy-builder, version ? null }:
(mathcomp.override {single = true;}).overrideAttrs (old: {
  name = "coq${coq.coq-version}-mathcomp-planB-src";
  buildPhase = ''
    COQ_ELPI_ATTRIBUTES='hb(log(raw))' \
    make -j$NIX_BUILD_CORES -C mathcomp
    coq.hb patch `find . -name \*.v`
    make -C mathcomp clean
  '';
  propagatedBuildInputs = old.propagatedBuildInputs ++
                          [ coq-elpi hierarchy-builder ];
  installPhase = ''
    mkdir -p $out
    cp -r . $out
  '';
})
