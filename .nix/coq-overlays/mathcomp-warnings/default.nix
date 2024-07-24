{ mathcomp }: (mathcomp.override { single = true; }).overrideAttrs {
  preConfigure = ''
    echo "-arg -w -arg +default" > mathcomp/Make.tmp
    cat mathcomp/Make >> mathcomp/Make.tmp
    mv mathcomp/Make.tmp mathcomp/Make
  '';
}
