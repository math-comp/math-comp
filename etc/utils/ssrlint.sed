#!/bin/sed -i

# USAGE: FIRST COMMIT THE FILES YOU ARE ABOUT TO PROCESS, then:
# > sed -i -f $(git root)/etc/utils/ssrlint.sed file1.v file2.v ...
#
# This script automatically fix the following kind of style issues:
# `move /` `move :` `apply /` `apply :` `rewrite/` `=>/bla` ...
#

/\((\*\|Notation\|format\)/!{
  s/\. *$/./g
  s/ *; */; /g
  s/\; *$/;/g
  s/\(elim\|apply\|move\|case\) *\(:\|=>\) */\1\2 /g
  s/\(elim\|apply\|move\|case\) *\(\/\) */\1\2/g
  s/rewrite */rewrite /g
  # s/move\/\([^=]*\) *=>/move=> \/\1/g
  # s/case\/\([0-9a-zA-Z]*\) *=>/move=> \/\1\[\]/g
  s/=>\//=> \//g
  s/do *\([0-9]*\) *\([\?!]\) */do \1\2/g
  /do [0-9]*[\?!]*/!{
    s/\(=> *[^;]*\) *; move=> *\//\1 - \//g
    s/\(=> *[^;]*\) *; move=> */\1 /g
    s/; *move=> *\(->\|\/\/\|\/=\)/ => \1/g
    s/; *move=> */ => - /g
  }
}