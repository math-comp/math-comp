BEGIN {
    deprecated = 0
    note = ""
}
/(Definition|Notation|Lemma|Theorem|Corollary)/ {
    s = gensub(/^([ +-]) *(Definition|Notation|Lemma|Theorem|Corollary) +([^ :\(\{\["]+).*/, "\\1 \\2 \\3", 1)
    if (s != $0) {
      class = gensub(/^[ +-] (Definition|Notation|Lemma|Theorem|Corollary).*/,"\\1", 1, s)
      name = gensub(/^[ +-] (Definition|Notation|Lemma|Theorem|Corollary) (.*)/,"\\2", 1, s)
      added_to = ""
      removed_from = ""
      deprecated_in = ""
      if (match(name, /_(subproof|subdef)/)) { }
      else {
        if (match(s, /^\+.*/)) { added_to = file }
        if (match(s, /^\-.*/)) { removed_from = file }
        if (deprecated == 1) { deprecated_in = file }
        if (deprecated == 1 || added_to != "" || removed_from != "") {
           printf("insert or ignore into changes values (\"%s\", \"%s\", \"%s\", \"%s\", \"%s\", \"%s\", %d);\n",
                   name, class, added_to, delete_from, deprecated_in, note, NR)
           if (added_to != "") {
               printf("update changes set added_file = \"%s\" where name = \"%s\";\n", added_to, name)
               printf("update changes set class = \"%s\" where name = \"%s\";\n", class, name)
           }
           if (removed_from != "") {
               printf("update changes set removed_file = \"%s\" where name = \"%s\";\n", removed_from, name)
           }
           if (note != "") {
               printf("update changes set deprecated_file = \"%s\" where name = \"%s\";\n", file, name)
               printf("update changes set deprecated_note = \"%s\" where name = \"%s\";\n", note, name)
           }
        }
      }
    }
    deprecated = 0
    note = ""
}
/^+#.*deprecated/ {
  deprecated = 1
    note = gensub(/.*note *= *"([^"]+)".*/, "\\1", 1)
    if (note == $0) { note = "deprecated" }
}
/^+.*note=/ {
  if (deprecated == 1) {
    note = gensub(/.*note *= *"([^"]+)".*/, "\\1", 1)
    if (note == $0) { note = "deprecated" }
  }
}
