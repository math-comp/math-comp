(lang dune 3.2)
(using coq 0.3)
(name math-comp)

; Enable to generate the OPAM files automatically
; (generate_opam_files true)

(license CECILL-B)
(maintainers "Mathematical Components <mathcomp-dev@sympa.inria.fr>")

(authors
   "Jeremy Avigad <>"
   "Andrea Asperti <>"
   "Stephane Le Roux <>"
   "Yves Bertot <>"
   "Laurence Rideau <>"
   "Enrico Tassi <>"
   "Ioana Pasca <>"
   "Georges Gonthier <>"
   "Sidi Ould Biha <>"
   "Cyril Cohen <>"
   "Francois Garillot <>"
   "Alexey Solovyev <>"
   "Russell O'Connor <>"
   "Laurent Théry <>"
   "Assia Mahboubi <>")

; This generates bug-reports and dev-repo
(source (github math-comp/math-comp))
(homepage https://math-comp.github.io/)
; todo
; (documentation "")
(version dev)

(package
 (name coq-mathcomp-ssreflect)
 (depends (coq (or (and (>= "8.13") (< "8.17~")) (= :dev))))
 (synopsis "Small Scale Reflection")
  (description "This library includes the small scale reflection proof language
extension and the minimal set of libraries to take advantage of it.
This includes libraries on lists (seq), boolean and boolean
predicates, natural numbers and types with decidable equality,
finite types, finite sets, finite functions, finite graphs, basic arithmetics
and prime numbers, big operators")
 (tags ("keyword:algebra" "keyword:small scale reflection" "keyword:mathematical components" "keyword:odd order theorem" "logpath:mathcomp.algebra")))

(package
 (name coq-mathcomp-fingroup)
 (depends (coq-mathcomp-ssreflect (= :version)))
 (synopsis "Mathematical Components Library on finite groups")
  (description "This library contains definitions and theorems about finite groups,
group quotients, group morphisms, group presentation, group action...")
 (tags ("keyword:finite groups" "keyword:small scale reflection" "keyword:mathematical components" "keyword:odd order theorem" "logpath:mathcomp.fingroup")))

(package
 (name coq-mathcomp-algebra)
 (depends (coq-mathcomp-fingroup (= :version)))
 (synopsis "Mathematical Components Library on Algebra")
  (description "This library contains definitions and theorems about discrete
(i.e. with decidable equality) algebraic structures : ring, fields,
ordered fields, real fields,  modules, algebras, integers, rational
numbers, polynomials, matrices, vector spaces...")
 (tags ("keyword:algebra" "keyword:small scale reflection" "keyword:mathematical components" "keyword:odd order theorem" "logpath:mathcomp.algebra")))

(package
 (name coq-mathcomp-solvable)
 (depends (coq-mathcomp-algebra (= :version)))
 (synopsis "Mathematical Components Library on finite groups (II)")
  (description "This library contains more definitions and theorems about finite groups.")
 (tags ("keyword:finite groups" "keyword:Feit Thompson theorem" "keyword:small scale reflection" "keyword:mathematical components" "keyword:odd order theorem" "logpath:mathcomp.solvable")))

(package
 (name coq-mathcomp-field)
 (depends (coq-mathcomp-solvable (= :version)))
 (synopsis "Mathematical Components Library on Fields")
  (description "This library contains definitions and theorems about field extensions,
galois theory, algebraic numbers, cyclotomic polynomials...")
 (tags ("keyword:algebra" "keyword:field" "keyword:small scale reflection" "keyword:mathematical components" "keyword:odd order theorem" "logpath:mathcomp.field")))

(package
 (name coq-mathcomp-character)
 (depends (coq-mathcomp-field (= :version)))
 (synopsis "Mathematical Components Library on character theory")
 (description "This library contains definitions and theorems about group
representations, characters and class functions.")
 (tags ("keyword:algebra" "keyword:character" "keyword:small scale reflection" "keyword:mathematical components" "keyword:odd order theorem" "logpath:mathcomp.character")))

