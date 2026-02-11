print "digraph depend {\n";
print "  node [shape = ellipse,style=filled,colorscheme = paired12];\n";
print "  subgraph cluster_boot { label=\"Boot\" }\n";
print "  subgraph cluster_order { label=\"Order\" }\n";
print "  subgraph cluster_algebra { label=\"Algebra\" }\n";
print "  subgraph cluster_field { label=\"Field\" }\n";
print "  subgraph cluster_character { label=\"Character\" }\n";
print "  subgraph cluster_fingroup { label=\"FinGroup\" }\n";
print "  subgraph cluster_solvable { label=\"Solvable\" }\n";
while (<>) {
  if (m/([^\s]*)\.vo.*:(.*)/) {
    $dests = $2 ;
    ($path,$src) = ($1 =~ s/\//\//rg =~ m/^(?:(.*)\/)?([^.]*)$/);
    $url="mathcomp.$path.$src.html";
    if ($path =~ m/boot/) {
        print "subgraph cluster_boot { \"$path\/$src\"[label=\"$src\",URL=\"$url\",fillcolor=1]}\n";
    }elsif ($path =~ m/order/) {
        print "subgraph cluster_order { \"$path\/$src\"[label=\"$src\",URL=\"$url\",fillcolor=2,fontcolor=white]}\n";
    }elsif ($path =~ m/algebra/) {
        print "subgraph cluster_algebra { \"$path\/$src\"[label=\"$src\",URL=\"$url\",fillcolor=3,fontcolor=white]}\n";
    }elsif ($path =~ m/field/) {
        print "subgraph cluster_field { \"$path\/$src\"[label=\"$src\",URL=\"$url\",fillcolor=4,fontcolor=white]}\n";
    }elsif ($path =~ m/character/) {
        print "subgraph cluster_character { \"$path\/$src\"[label=\"$src\",URL=\"$url\",fillcolor=5]}\n";
    }elsif ($path =~ m/fingroup/) {
        print "subgraph cluster_fingroup { \"$path\/$src\"[label=\"$src\",URL=\"$url\",fillcolor=9]}\n";
    }elsif ($path =~ m/solvable/) {
        print "subgraph cluster_solvable { \"$path\/$src\"[label=\"$src\",URL=\"$url\",fillcolor=10,fontcolor=white]}\n";
    }else {
        print "\"$path\/$src\"[label=\"$path=$src\",fillcolor=6,fontcolor=white]\n";
    }
    for my $dest (split(" ", $dests)) {
        print "  \"$1\" -> \"$path\/$src\";\n" if ($dest =~ m/(.*)\.vo/);
    }
  }
}
print "}\n";
