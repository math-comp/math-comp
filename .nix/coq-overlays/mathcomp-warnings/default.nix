{ mathcomp }: (mathcomp.override { single = true; }).overrideAttrs {
  preConfigure = ''
    echo "-arg -w -arg +default" > Make.tmp
    cat Make >> Make.tmp
    mv Make.tmp Make
  '';
}
