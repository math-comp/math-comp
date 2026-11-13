- in `boot/path.v`
  + lemmas `sorted_last` and `sorted_subseq_nth_rev` for bounds in sequences
    sorted by a reflexive, transitive relation
- in `order/preorder.v`
  + lemmas `le_sorted_last` and `le_sorted_subseq_nth_rev` specializing
    the corresponding `boot/path.v` lemmas to preorders
  + lemma `le_sorted_nth_gap` excluding members between consecutive items
    of a sorted sequence
