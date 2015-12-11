
mangle_sources() {
# pre processing, mainly comments
for f in $@; do 


sed -r -e '
        # We remove comments inside proofs 
       /^Proof.$/,/^Qed./s/\(\*[^*](([^(]|\([^*]){1,}?[^^])\*+\)//g;
        ' $f |

sed -r -e '
        # read the whole file into the pattern space
        # :a is the label, N glues the current line; b branches
        # to a if not EOF
        :a; N; $!ba;                                                                                                         
        # remove all starred lines
        s/\(\*{5,}?\)//g;
    
        # remove *)\n(*
        s/\*+\)\n\(\*+/\n/g;
        
        # double star not too short comments, that are left
        # as singly starred comments, like (*a.3*)
        s/\n\(\*+(([^(]|\([^*]){5,}?[^^])\*+\)/\n(**\ \1\ **)/g;

        # restore hide
        s/\(\*+[ ]*begin hide[ ]*\*+\)/\(\* begin hide \*\)/g;
        s/\(\*+[ ]*end hide[ ]*\*+\)/\(\* end hide \*\)/g;
	' |

sed -r -e '
	# since ranges apply to lines only we create lines
	s/\(\*\*/\n(**\n/g;
	s/\*\*\)/\n**)\n/g;
	' |

sed -r -e '
	# quote sharp, percent and dollar on comment blocks
	# hiding underscore
	/\(\*\*/,/\*\*\)/s/#/##/g;
	/\(\*\*/,/\*\*\)/s/%/%%/g;
	/\(\*\*/,/\*\*\)/s/\$/$$/g;
	/\(\*\*/,/\*\*\)/s/\[/#[#/g;
	/\(\*\*/,/\*\*\)/s/]/#]#/g;

	# only in 8.4
        #	/\(\*\*/,/\*\*\)/s/\_/#\_#/g;

	# the lexer glues sharp with other symbols
	/\(\*\*/,/\*\*\)/s/([^A-Za-z0-9 ])#\[#/\1 #[#/g;
	/\(\*\*/,/\*\*\)/s/([^A-Za-z0-9 ])#]#/\1 #]#/g;
	' |

sed -r -e '
	# we glue comment lines back together
        :a; N; $!ba; 
	s/\n\(\*\*\n/(**/g;
	s/\n\*\*\)\n/**)/g;
	' > $f.tmp
	mv $f.tmp $f
done
}

# example invocation:
# MAKEDOT=../etc/utils/ PATH=$COQBIN:$PATH MANGLEDOT=touch COQDOCOPTS="-R . mathcomp" \
#	build_doc */*.v
build_doc() {
rm -rf html
mkdir html
coqdoc -t "$TITLE" -g --utf8 $COQDOCOPTS \
        --parse-comments \
	--multi-index $@ -d html

# graph
coqdep -noglob $COQOPTS $@ > depend
sed -i -e 's/ [^ ]*\.cmxs//g' -e 's/ [^ ]*\.cm.//g' depend
ocamlc -o $MAKEDOT/makedot -pp camlp5o $MAKEDOT/dependtodot.ml
$MAKEDOT/makedot depend
mv *.dot theories.dot || true
$MANGLEDOT theories.dot
dot -Tpng -o html/depend.png -Tcmapx -o html/depend.map theories.dot
dot -Tsvg -o html/depend.svg theories.dot

# post processing
for f in html/*.html; do sed -r -i -e '
	# read the whole file into the pattern space
	# :a is the label, N glues the current line; b branches
	# to a if not EOF
	:a; N; $!ba;

        #Add the favicon
        s/^<\/head>/<link rel="icon" type="image\/png" href="favicon.png" \/>\n<\/head>/mg;

	# add the Joint Center logo
	s/<h1([^>]*?)>/<h1\1><img src="jc.png" alt="(Joint Center)"\/>/g;

	# extra blank line
    	s/<div\ class="doc">\n/<div class="doc">/g;

	# weird underscore
    	s/ /_/g;
 
        # putting back underscore
	s/#\_#/\_/g;


	# abundance of <br/>
    	s/\n<br\/> <br\/>//g;
	' $f
done

mv html/index.html html/index_lib.html
cat >html/index.html <<EOT
<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Strict//EN"
"http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd">
<html xmlns="http://www.w3.org/1999/xhtml">
<head>
<meta http-equiv="Content-Type" content="text/html; charset=utf-8"/>
<link href="coqdoc.css" rel="stylesheet" type="text/css"/>
<link rel="icon" type="image/png" href="favicon.png" />
<title>$TITLE</title>
</head>

<body>

<div id="page">

<div id="header">
</div>

<div id="main">

<h1><img src="jc.png" alt="(Joint Center)"/>
$TITLE Documentation</h1>
<hr/>
<img class="graph" src="depend.png" usemap="#theories" />
EOT
cat html/depend.map >> html/index.html
cat >>html/index.html <<EOT
<hr/>
<center><a href="index_lib.html">
Library index
</a></center>
</div>
</div>
</body>
</html>
EOT

}
