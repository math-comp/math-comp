{ mathcomp, coq, coq-elpi, hierarchy-builder-shim,
  mathcomp-single-planB-src }:
(mathcomp.override {single = true;}).overrideAttrs (old: {
  src = mathcomp-single-planB-src;
  name = "coq${coq.coq-version}-mathcomp-planB";
  propagatedBuildInputs = old.propagatedBuildInputs ++
                          [ coq-elpi hierarchy-builder-shim ];
})
