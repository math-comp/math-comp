(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun eqtype ssrnat seq path div choice.
From mathcomp
Require Import fintype tuple finfun bigop prime ssralg poly polydiv finset.
From mathcomp
Require Import fingroup morphism perm automorphism quotient finalg action zmodp.
From mathcomp
Require Import commutator cyclic center pgroup matrix mxalgebra mxpoly.

(******************************************************************************)
(*  This file provides linkage between classic Group Theory and commutative   *)
(* algebra -- representation theory. Since general abstract linear algebra is *)
(* still being sorted out, we develop the required theory here on the         *)
(* assumption that all vector spaces are matrix spaces, indeed that most are  *)
(* row matrix spaces; our representation theory is specialized to the latter  *)
(* case. We provide many definitions and results of representation theory:    *)
(* enveloping algebras, reducible, irreducible and absolutely irreducible     *)
(* representations, representation centralisers, submodules and kernels,      *)
(* simple and semisimple modules, the Schur lemmas, Maschke's theorem,        *)
(* components, socles, homomorphisms and isomorphisms, the Jacobson density   *)
(* theorem, similar representations, the Jordan-Holder theorem, Clifford's    *)
(* theorem and Wedderburn components, regular representations and the         *)
(* Wedderburn structure theorem for semisimple group rings, and the           *)
(* construction of a splitting field of an irreducible representation, and of *)
(* reduced, tensored, and factored representations.                           *)
(* mx_representation F G n == the Structure type for representations of G     *)
(*                 with n x n matrices with coefficients in F. Note that      *)
(*                 rG : mx_representation F G n coerces to a function from    *)
(*                 the element type of G to 'M_n, and conversely all such     *)
(*                 functions have a Canonical mx_representation.              *)
(*  mx_repr G r <-> r : gT -> 'M_n defines a (matrix) group representation    *)
(*                 on G : {set gT} (Prop predicate).                          *)
(* enveloping_algebra_mx rG == a #|G| x (n ^ 2) matrix whose rows are the     *)
(*                 mxvec encodings of the image of G under rG, and whose      *)
(*                 row space therefore encodes the enveloping algebra of      *)
(*                 the representation of G.                                   *)
(*      rker rG == the kernel of the representation of r on G, i.e., the      *)
(*                 subgroup of elements of G mapped to the identity by rG.    *)
(* mx_faithful rG == the representation rG of G is faithful (its kernel is    *)
(*                 trivial).                                                  *)
(* rfix_mx rG H == an n x n matrix whose row space is the set of vectors      *)
(*                 fixed (centralised) by the representation of H by rG.      *)
(*   rcent rG A == the subgroup of G whose representation via rG commutes     *)
(*                 with the square matrix A.                                  *)
(*   rcenter rG == the subgroup of G whose representation via rG consists of  *)
(*                 scalar matrices.                                           *)
(* centgmx rG f <=> f commutes with every matrix in the representation of G   *)
(*                 (i.e., f is a total rG-homomorphism).                      *)
(*   rstab rG U == the subgroup of G whose representation via r fixes all     *)
(*                 vectors in U, pointwise.                                   *)
(*  rstabs rG U == the subgroup of G whose representation via r fixes the row *)
(*                 space of U globally.                                       *)
(* mxmodule rG U <=> the row-space of the matrix U is a module (globally      *)
(*                 invariant) under the representation rG of G.               *)
(* max_submod rG U V <-> U < V is not a proper is a proper subset of any      *)
(*                 proper rG-submodule of V (if both U and V are modules,     *)
(*                 then U is a maximal proper submodule of V).                *)
(* mx_subseries rG Us <=> Us : seq 'M_n is a list of rG-modules               *)
(* mx_composition_series rG Us <-> Us is an increasing composition series     *)
(*                 for an rG-module (namely, last 0 Us).                      *)
(* mxsimple rG M <-> M is a simple rG-module (i.e., minimal and nontrivial)   *)
(*                 This is a Prop predicate on square matrices.               *)
(* mxnonsimple rG U <-> U is constructively not a submodule, that is, U       *)
(*                 contains a proper nontrivial submodule.                    *)
(* mxnonsimple_sat rG U == U is not a simple as an rG-module.                 *)
(*                 This is a bool predicate, which requires a decField        *)
(*                 structure on the scalar field.                             *)
(* mxsemisimple rG W <-> W is constructively a direct sum of simple modules.  *)
(* mxsplits rG V U <-> V splits over U in rG, i.e., U has an rG-invariant     *)
(*                 complement in V.                                           *)
(* mx_completely_reducible rG V <-> V splits over all its submodules; note    *)
(*                 that this is only classically equivalent to stating that   *)
(*                 V is semisimple.                                           *)
(* mx_irreducible rG <-> the representation rG is irreducible, i.e., the full *)
(*                 module 1%:M of rG is simple.                               *)
(* mx_absolutely_irreducible rG == the representation rG of G is absolutely   *)
(*                 irreducible: its enveloping algebra is the full matrix     *)
(*                 ring. This is only classically equivalent to the more      *)
(*                 standard ``rG does not reduce in any field extension''.    *)
(* group_splitting_field F G <-> F is a splitting field for the group G:      *)
(*                 every irreducible representation of G is absolutely        *)
(*                 irreducible. Any field can be embedded classically into a  *)
(*                 splitting field.                                           *)
(* group_closure_field F gT <-> F is a splitting field for every group        *)
(*                 G : {group gT}, and indeed for any section of such a       *)
(*                 group. This is a convenient constructive substitute for    *)
(*                 algebraic closures, that can be constructed classically.   *)
(* dom_hom_mx rG f == a square matrix encoding the set of vectors for which   *)
(*                 multiplication by the n x n matrix f commutes with the     *)
(*                 representation of G, i.e., the largest domain on which     *)
(*                 f is an rG homomorphism.                                   *)
(*   mx_iso rG U V <-> U and V are (constructively) rG-isomorphic; this is    *)
(*                 a Prop predicate.                                          *)
(* mx_simple_iso rG U V == U and V are rG-isomorphic if one of them is        *)
(*                 simple; this is a bool predicate.                          *)
(*  cyclic_mx rG u == the cyclic rG-module generated by the row vector u      *)
(* annihilator_mx rG u == the annihilator of the row vector u in the          *)
(*                 enveloping algebra the representation rG.                  *)
(* row_hom_mx rG u == the image of u by the set of all rG-homomorphisms on    *)
(*                 its cyclic module, or, equivalently, the null-space of the *)
(*                 annihilator of u.                                          *)
(* component_mx rG M == when M is a simple rG-module, the component of M in   *)
(*                 the representation rG, i.e. the module generated by all    *)
(*                 the (simple) modules rG-isomorphic to M.                   *)
(*    socleType rG == a Structure that represents the type of all components  *)
(*                 of rG (more precisely, it coerces to such a type via       *)
(*                 socle_sort). For sG : socleType, values of type sG (to be  *)
(*                 exact, socle_sort sG) coerce to square matrices. For any   *)
(*                 representation rG we can construct sG : socleType rG       *)
(*                 classically; the socleType structure encapsulates this     *)
(*                 use of classical logic.                                    *)
(* DecSocleType rG == a socleType rG structure, for a representation over a   *)
(*                 decidable field type. DecSocleType rG is opaque.           *)
(*    socle_base W == for W : (sG : socleType), a simple module whose         *)
(*                 component is W; socle_simple W and socle_module W are      *)
(*                 proofs that socle_base W is a simple module.               *)
(*    socle_mult W == the multiplicity of socle_base W in W : sG.             *)
(*                 := \rank W %/ \rank (socle_base W)                         *)
(*        Socle sG == the Socle of rG, given sG : socleType rG, i.e., the     *)
(*                 (direct) sum of all the components of rG.                  *)
(* mx_rsim rG rG' <-> rG and rG' are similar representations of the same      *)
(*                 group G. Note that rG and rG' must then have equal, but    *)
(*                 not necessarily convertible, degree.                       *)
(* submod_repr modU == a representation of G on 'rV_(\rank U) equivalent to   *)
(*                 the restriction of rG to U (here modU : mxmodule rG U).    *)
(*    socle_repr W := submod_repr (socle_module W)                            *)
(* val/in_submod rG U == the projections resp. from/onto 'rV_(\rank U),       *)
(*                 that correspond to submod_repr r G U (these work both on   *)
(*                 vectors and row spaces).                                   *)
(* factmod_repr modV == a representation of G on 'rV_(\rank (cokermx V)) that *)
(*                 is equivalent to the factor module 'rV_n / V induced by V  *)
(*                 and rG (here modV : mxmodule rG V).                        *)
(* val/in_factmod rG U == the projections for factmod_repr r G U.             *)
(* section_repr modU modV == the restriction to in_factmod V U of the factor  *)
(*                 representation factmod_repr modV (for modU : mxmodule rG U *)
(*                 and modV : mxmodule rG V); section_repr modU modV is       *)
(*                 irreducible iff max_submod rG U V.                         *)
(* subseries_repr modUs i == the representation for the section module        *)
(*                 in_factmod (0 :: Us)`_i Us`_i, where                       *)
(*                 modUs : mx_subseries rG Us.                                *)
(* series_repr compUs i == the representation for the section module          *)
(*                 in_factmod (0 :: Us)`_i Us`_i, where                       *)
(*                 compUs : mx_composition_series rG Us. The Jordan-Holder    *)
(*                 theorem asserts the uniqueness of the set of such          *)
(*                 representations, up to similarity and permutation.         *)
(* regular_repr F G == the regular F-representation of the group G.           *)
(*   group_ring F G == a #|G| x #|G|^2 matrix that encodes the free group     *)
(*                 ring of G -- that is, the enveloping algebra of the        *)
(*                 regular F-representation of G.                             *)
(*   gring_index x == the index corresponding to x \in G in the matrix        *)
(*                 encoding of regular_repr and group_ring.                   *)
(*     gring_row A == the row vector corresponding to A \in group_ring F G in *)
(*                 the regular FG-module.                                     *)
(*  gring_proj x A == the 1 x 1 matrix holding the coefficient of x \in G in  *)
(*                 (A \in group_ring F G)%MS.                                 *)
(*   gring_mx rG u == the image of a row vector u of the regular FG-module,   *)
(*                 in the enveloping algebra of another representation rG.    *)
(*   gring_op rG A == the image of a matrix of the free group ring of G,      *)
(*                 in the enveloping algebra of rG.                           *)
(*   gset_mx F G C == the group sum of C in the free group ring of G -- the   *)
(*                 sum of the images of all the x \in C in group_ring F G.    *)
(* classg_base F G == a #|classes G| x #|G|^2 matrix whose rows encode the    *)
(*                 group sums of the conjugacy classes of G -- this is a      *)
(*                 basis of 'Z(group_ring F G)%MS.                            *)
(*     irrType F G == a type indexing irreducible representations of G over a *)
(*                 field F, provided its characteristic does not divide the   *)
(*                 order of G; it also indexes Wedderburn subrings.           *)
(*                 :=  socleType (regular_repr F G)                           *)
(*      irr_repr i == the irreducible representation corresponding to the     *)
(*                 index i : irrType sG                                       *)
(*                 := socle_repr i as i coerces to a component matrix.        *)
(* 'n_i, irr_degree i == the degree of irr_repr i; the notation is only       *)
(*                 active after Open Scope group_ring_scope.                  *)
(*   linear_irr sG == the set of sG-indices of linear irreducible             *)
(*                 representations of G.                                      *)
(*  irr_comp sG rG == the sG-index of the unique irreducible representation   *)
(*                 similar to rG, at least when rG is irreducible and the     *)
(*                 characteristic is coprime.                                 *)
(*    irr_mode i z == the unique eigenvalue of irr_repr i z, at least when    *)
(*                 irr_repr i z is scalar (e.g., when z \in 'Z(G)).           *)
(*      [1 sG]%irr == the index of the principal representation of G, in      *)
(*                 sG : irrType F G. The i argument of irr_repr, irr_degree   *)
(*                 and irr_mode is in the %irr scope. This notation may be    *)
(*                 replaced locally by an interpretation of 1%irr as [1 sG]   *)
(*                 for some specific irrType sG.                              *)
(* 'R_i, Wedderburn_subring i == the subring (indeed, the component) of the   *)
(*                 free group ring of G corresponding to the component i : sG *)
(*                 of the regular FG-module, where sG : irrType F g. In       *)
(*                 coprime characteristic the Wedderburn structure theorem    *)
(*                 asserts that the free group ring is the direct sum of      *)
(*                 these subrings; as with 'n_i above, the notation is only   *)
(*                 active in group_ring_scope.                                *)
(* 'e_i, Wedderburn_id i == the projection of the identity matrix 1%:M on the *)
(*                 Wedderburn subring of i : sG (with sG a socleType). In     *)
(*                 coprime characteristic this is the identity element of     *)
(*                 the subring, and the basis of its center if the field F is *)
(*                 a splitting field. As 'R_i, 'e_i is in group_ring_scope.   *)
(* subg_repr rG sHG == the restriction to H of the representation rG of G;    *)
(*                 here sHG : H \subset G.                                    *)
(* eqg_repr rG eqHG == the representation rG of G viewed a a representation   *)
(*                 of H; here eqHG : G == H.                                  *)
(* morphpre_repr f rG == the representation of f @*^-1 G obtained by          *)
(*                 composing the group morphism f with rG.                    *)
(* morphim_repr rGf sGD == the representation of G induced by a               *)
(*                 representation rGf of f @* G; here sGD : G \subset D where *)
(*                 D is the domain of the group morphism f.                   *)
(* rconj_repr rG uB == the conjugate representation x |-> B * rG x * B^-1;    *)
(*                 here uB : B \in unitmx.                                    *)
(* quo_repr sHK nHG == the representation of G / H induced by rG, given       *)
(*                 sHK : H \subset rker rG, and nHG : G \subset 'N(H).        *)
(* kquo_repr rG == the representation induced on G / rker rG by rG.           *)
(* map_repr f rG == the representation f \o rG, whose module is the tensor    *)
(*                 product of the module of rG with the extension field into  *)
(*                 which f : {rmorphism F -> Fstar} embeds F.                 *)
(*      'Cl%act == the transitive action of G on the Wedderburn components of *)
(*                 H, with nsGH : H <| G, given by Clifford's theorem. More   *)
(*                 precisely this is a total action of G on socle_sort sH,    *)
(*                 where sH : socleType (subg_repr rG (normal_sub sGH)).      *)
(* We build on the MatrixFormula toolkit to define decision procedures for    *)
(* the reducibility property:                                                 *)
(*  mxmodule_form rG U == a formula asserting that the interpretation of U is *)
(*                 a module of the representation rG.                         *)
(*  mxnonsimple_form rG U == a formula asserting that the interpretation of U *)
(*                 contains a proper nontrivial rG-module.                    *)
(*  mxnonsimple_sat rG U <=> mxnonsimple_form rG U is satisfied.              *)
(* More involved constructions are encapsulated in two Coq submodules:        *)
(* MatrixGenField == a module that encapsulates the lengthy details of the    *)
(*                 construction of appropriate extension fields. We assume we *)
(*                 have an irreducible representation rG of a group G, and a  *)
(*                 non-scalar matrix A that centralises rG(G), as this data   *)
(*                 is readily extracted from the Jacobson density theorem. It *)
(*                 then follows from Schur's lemma that the ring generated by *)
(*                 A is a field on which the extension of the representation  *)
(*                 rG of G is reducible. Note that this is equivalent to the  *)
(*                 more traditional quotient of the polynomial ring by an     *)
(*                 irreducible polynomial (the minimal polynomial of A), but  *)
(*                 much better suited to our needs.                           *)
(*   Here are the main definitions of MatrixGenField; they all have three     *)
(* proofs as arguments: (implicit) rG : mx_repr n G, irrG : mx_irreducible rG *)
(* and cGA : centgmx rG A. These ensure the validity of the construction and  *)
(* allow us to define Canonical instances; we assume degree_mxminpoly A > 1   *)
(* (which is equivalent to ~~ is_scalar_mx A) only to prove reducibility.     *)
(*  + gen_of irrG cGA == the carrier type of the field generated by A. It is  *)
(*                 at least equipped with a fieldType structure; we also      *)
(*                 propagate any decFieldType/finFieldType structures on the  *)
(*                 original field.                                            *)
(*  + gen irrG cGA == the morphism injecting into gen_of irrG cGA.            *)
(*  + groot irrG cGA == the root of mxminpoly A in the gen_of irrG cGA field. *)
(*  + pval x, rVval x, mxval x == the interpretation of x : gen_of irrG cGA   *)
(*                 as a polynomial, a row vector, and a matrix, respectively. *)
(*                 Both irrG and cGA are implicit arguments here.             *)
(*  + gen_repr irrG cGA == an alternative to the field extension              *)
(*                 representation, which consists in reconsidering the        *)
(*                 original module as a module over the new gen_of field,     *)
(*                 thereby DIVIDING the original dimension n by the degree of *)
(*                 the minimal polynomial of A. This can be simpler than the  *)
(*                 extension method, is actually required by the proof that   *)
(*                 odd groups are p-stable (B & G 6.1-2, and Appendix A), but *)
(*                 is only applicable if G is the LARGEST group represented   *)
(*                 by rG (e.g., NOT for B & G 2.6).                           *)
(*  + gen_dim A == the dimension of gen_repr irrG cGA (only depends on A).    *)
(*  + in_gen irrG cGA W == the ROWWISE image of a matrix W : 'M[F]_(m, n),    *)
(*                 i.e., interpreting W as a sequence of m tow vectors,       *)
(*                 under the bijection from rG to gen_repr irrG cGA.          *)
(*                 The sequence length m is a maximal implicit argument       *)
(*                 passed between the explicit argument cGA and W.            *)
(*  + val_gen W == the ROWWISE image of an 'M[gen_of irrG cGA]_(m, gen_dim A) *)
(*                 matrix W under the bijection from gen_repr irrG cGA to rG. *)
(*  + rowval_gen W == the ROWSPACE image of W under the bijection from        *)
(*                 gen_repr irrG cGA to rG, i.e., a 'M[F]_n matrix whose row  *)
(*                 space is the image of the row space of W.                  *)
(*                 This is the A-ideal generated by val_gen W.                *)
(*  + gen_sat e f <=> f : GRing.formula (gen_of irrG cGA) is satisfied in     *)
(*                 environment e : seq (gen_of irrG cGA), provided F has a    *)
(*                 decFieldType structure.                                    *)
(*  + gen_env e, gen_term t, gen_form f == interpretations of environments,   *)
(*                 terms, and RING formulas over gen_of irrG cGA as row       *)
(*                 vector formulae, used to construct gen_sat.                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.

Reserved Notation "''n_' i" (at level 8, i at level 2, format "''n_' i").
Reserved Notation "''R_' i" (at level 8, i at level 2, format "''R_' i").
Reserved Notation "''e_' i" (at level 8, i at level 2, format "''e_' i").

Delimit Scope irrType_scope with irr.

Section RingRepr.

Variable R : comUnitRingType.

Section OneRepresentation.

Variable gT : finGroupType.

Definition mx_repr (G : {set gT}) n (r : gT -> 'M[R]_n) :=
  r 1%g = 1%:M /\ {in G &, {morph r : x y / (x * y)%g >-> x *m y}}.

Structure mx_representation G n :=
  MxRepresentation { repr_mx :> gT -> 'M_n; _ : mx_repr G repr_mx }.

Variables (G : {group gT}) (n : nat) (rG : mx_representation G n).
Arguments rG _%group_scope : extra scopes.

Lemma repr_mx1 : rG 1 = 1%:M.
Proof. by case: rG => r []. Qed.

Lemma repr_mxM : {in G &, {morph rG : x y / (x * y)%g >-> x *m y}}.
Proof. by case: rG => r []. Qed.

Lemma repr_mxK m x :
  x \in G ->  cancel ((@mulmx R m n n)^~ (rG x)) (mulmx^~ (rG x^-1)).
Proof.
by move=> Gx U; rewrite -mulmxA -repr_mxM ?groupV // mulgV repr_mx1 mulmx1.
Qed.

Lemma repr_mxKV m x :
  x \in G -> cancel ((@mulmx R m n n)^~ (rG x^-1)) (mulmx^~ (rG x)).
Proof. by rewrite -groupV -{3}[x]invgK; apply: repr_mxK. Qed.

Lemma repr_mx_unit x : x \in G -> rG x \in unitmx.
Proof. by move=> Gx; case/mulmx1_unit: (repr_mxKV Gx 1%:M). Qed.

Lemma repr_mxV : {in G, {morph rG : x / x^-1%g >-> invmx x}}.
Proof.
by move=> x Gx /=; rewrite -[rG x^-1](mulKmx (repr_mx_unit Gx)) mulmxA repr_mxK.
Qed.

(* This is only used in the group ring construction below, as we only have   *)
(* developped the theory of matrix subalgebras for F-algebras.               *)
Definition enveloping_algebra_mx := \matrix_(i < #|G|) mxvec (rG (enum_val i)).

Section Stabiliser.

Variables (m : nat) (U : 'M[R]_(m, n)).

Definition rstab := [set x in G | U *m rG x == U].

Lemma rstab_sub : rstab \subset G.
Proof. by apply/subsetP=> x; case/setIdP. Qed.

Lemma rstab_group_set : group_set rstab.
Proof.
apply/group_setP; rewrite inE group1 repr_mx1 mulmx1; split=> //= x y.
case/setIdP=> Gx cUx; case/setIdP=> Gy cUy; rewrite inE repr_mxM ?groupM //.
by rewrite mulmxA (eqP cUx).
Qed.
Canonical rstab_group := Group rstab_group_set.

End Stabiliser.

(* Centralizer subgroup and central homomorphisms. *)
Section CentHom.

Variable f : 'M[R]_n.

Definition rcent := [set x in G | f *m rG x == rG x *m f].

Lemma rcent_sub : rcent \subset G.
Proof. by apply/subsetP=> x; case/setIdP. Qed.

Lemma rcent_group_set : group_set rcent.
Proof.
apply/group_setP; rewrite inE group1 repr_mx1 mulmx1 mul1mx; split=> //= x y.
case/setIdP=> Gx; move/eqP=> cfx; case/setIdP=> Gy; move/eqP=> cfy.
by rewrite inE repr_mxM ?groupM //= -mulmxA -cfy !mulmxA cfx.
Qed.
Canonical rcent_group := Group rcent_group_set.

Definition centgmx := G \subset rcent.

Lemma centgmxP : reflect (forall x, x \in G -> f *m rG x = rG x *m f) centgmx.
Proof.
apply: (iffP subsetP) => cGf x Gx;
  by have:= cGf x Gx; rewrite !inE Gx /=; move/eqP.
Qed.

End CentHom.

(* Representation kernel, and faithful representations. *)

Definition rker := rstab 1%:M.
Canonical rker_group := Eval hnf in [group of rker].

Lemma rkerP x : reflect (x \in G /\ rG x = 1%:M) (x \in rker).
Proof. by apply: (iffP setIdP) => [] [->]; move/eqP; rewrite mul1mx. Qed.

Lemma rker_norm : G \subset 'N(rker).
Proof.
apply/subsetP=> x Gx; rewrite inE sub_conjg; apply/subsetP=> y.
case/rkerP=> Gy ry1; rewrite mem_conjgV !inE groupJ //=.
by rewrite !repr_mxM ?groupM ?groupV // ry1 !mulmxA mulmx1 repr_mxKV.
Qed.

Lemma rker_normal : rker <| G.
Proof. by rewrite /normal rstab_sub rker_norm. Qed.

Definition mx_faithful := rker \subset [1].

Lemma mx_faithful_inj : mx_faithful -> {in G &, injective rG}.
Proof.
move=> ffulG x y Gx Gy eq_rGxy; apply/eqP; rewrite eq_mulgV1 -in_set1.
rewrite (subsetP ffulG) // inE groupM ?repr_mxM ?groupV //= eq_rGxy.
by rewrite mulmxA repr_mxK.
Qed.

Lemma rker_linear : n = 1%N -> G^`(1)%g \subset rker.
Proof.
move=> n1; rewrite gen_subG; apply/subsetP=> xy; case/imset2P=> x y Gx Gy ->.
rewrite !inE groupR //= /commg mulgA -invMg repr_mxM ?groupV ?groupM //.
rewrite mulmxA (can2_eq (repr_mxK _) (repr_mxKV _)) ?groupM //.
rewrite !repr_mxV ?repr_mxM ?groupM //; move: (rG x) (rG y).
by rewrite n1 => rx ry; rewrite (mx11_scalar rx) scalar_mxC.
Qed.

(* Representation center. *)

Definition rcenter := [set g in G | is_scalar_mx (rG g)].

Fact rcenter_group_set : group_set rcenter.
Proof.
apply/group_setP; split=> [|x y].
  by rewrite inE group1 repr_mx1 scalar_mx_is_scalar.
move=> /setIdP[Gx /is_scalar_mxP[a defx]] /setIdP[Gy /is_scalar_mxP[b defy]].
by rewrite !inE groupM ?repr_mxM // defx defy -scalar_mxM ?scalar_mx_is_scalar.
Qed.
Canonical rcenter_group := Group rcenter_group_set.

Lemma rcenter_normal : rcenter <| G.
Proof.
rewrite /normal /rcenter {1}setIdE subsetIl; apply/subsetP=> x Gx; rewrite inE.
apply/subsetP=> _ /imsetP[y /setIdP[Gy /is_scalar_mxP[c rGy]] ->].
rewrite inE !repr_mxM ?groupM ?groupV //= mulmxA rGy scalar_mxC repr_mxKV //.
exact: scalar_mx_is_scalar.
Qed.

End OneRepresentation.

Arguments rkerP {gT G n rG x}.

Section Proper.

Variables (gT : finGroupType) (G : {group gT}) (n' : nat).
Local Notation n := n'.+1.
Variable rG : mx_representation G n.

Lemma repr_mxMr : {in G &, {morph rG : x y / (x * y)%g >-> x * y}}.
Proof. exact: repr_mxM. Qed.

Lemma repr_mxVr : {in G, {morph rG : x / (x^-1)%g >-> x^-1}}.
Proof. exact: repr_mxV.
 Qed.

Lemma repr_mx_unitr x : x \in G -> rG x \is a GRing.unit.
Proof. exact: repr_mx_unit. Qed.

Lemma repr_mxX m : {in G, {morph rG : x / (x ^+ m)%g >-> x ^+ m}}.
Proof.
elim: m => [|m IHm] x Gx; rewrite /= ?repr_mx1 // expgS exprS -IHm //.
by rewrite repr_mxM ?groupX.
Qed.

End Proper.

Section ChangeGroup.

Variables (gT : finGroupType) (G H : {group gT}) (n : nat).
Variables (rG : mx_representation G n).

Section SubGroup.

Hypothesis sHG : H \subset G.

Lemma subg_mx_repr : mx_repr H rG.
Proof.
by split=> [|x y Hx Hy]; rewrite (repr_mx1, repr_mxM) ?(subsetP sHG).
Qed.
Definition subg_repr := MxRepresentation subg_mx_repr.
Local Notation rH := subg_repr.

Lemma rcent_subg U : rcent rH U = H :&: rcent rG U.
Proof. by apply/setP=> x; rewrite !inE andbA -in_setI (setIidPl sHG). Qed.

Section Stabiliser.

Variables (m : nat) (U : 'M[R]_(m, n)).

Lemma rstab_subg : rstab rH U = H :&: rstab rG U.
Proof. by apply/setP=> x; rewrite !inE andbA -in_setI (setIidPl sHG). Qed.

End Stabiliser.

Lemma rker_subg : rker rH = H :&: rker rG. Proof. exact: rstab_subg. Qed.

Lemma subg_mx_faithful : mx_faithful rG -> mx_faithful rH.
Proof. by apply: subset_trans; rewrite rker_subg subsetIr. Qed.

End SubGroup.

Section SameGroup.

Hypothesis eqGH : G :==: H.

Lemma eqg_repr_proof : H \subset G. Proof. by rewrite (eqP eqGH). Qed.

Definition eqg_repr := subg_repr eqg_repr_proof.
Local Notation rH := eqg_repr.

Lemma rcent_eqg U : rcent rH U = rcent rG U.
Proof. by rewrite rcent_subg -(eqP eqGH) (setIidPr _) ?rcent_sub. Qed.

Section Stabiliser.

Variables (m : nat) (U : 'M[R]_(m, n)).

Lemma rstab_eqg : rstab rH U = rstab rG U.
Proof. by rewrite rstab_subg -(eqP eqGH) (setIidPr _) ?rstab_sub. Qed.

End Stabiliser.

Lemma rker_eqg : rker rH = rker rG. Proof. exact: rstab_eqg. Qed.

Lemma eqg_mx_faithful : mx_faithful rH = mx_faithful rG.
Proof. by rewrite /mx_faithful rker_eqg. Qed.

End SameGroup.

End ChangeGroup.

Section Morphpre.

Variables (aT rT : finGroupType) (D : {group aT}) (f : {morphism D >-> rT}).
Variables (G : {group rT}) (n : nat) (rG : mx_representation G n).

Lemma morphpre_mx_repr : mx_repr (f @*^-1 G) (rG \o f).
Proof.
split=> [|x y]; first by rewrite /= morph1 repr_mx1.
case/morphpreP=> Dx Gfx; case/morphpreP=> Dy Gfy.
by rewrite /= morphM ?repr_mxM.
Qed.
Canonical morphpre_repr := MxRepresentation morphpre_mx_repr.
Local Notation rGf := morphpre_repr.

Section Stabiliser.

Variables (m : nat) (U : 'M[R]_(m, n)).

Lemma rstab_morphpre : rstab rGf U = f @*^-1 (rstab rG U).
Proof. by apply/setP=> x; rewrite !inE andbA. Qed.

End Stabiliser.

Lemma rker_morphpre : rker rGf = f @*^-1 (rker rG).
Proof. exact: rstab_morphpre. Qed.

End Morphpre.

Section Morphim.

Variables (aT rT : finGroupType) (G D : {group aT}) (f : {morphism D >-> rT}).
Variables (n : nat) (rGf : mx_representation (f @* G) n).

Definition morphim_mx of G \subset D := fun x => rGf (f x).

Hypothesis sGD : G \subset D.

Lemma morphim_mxE x : morphim_mx sGD x = rGf (f x). Proof. by []. Qed.

Let sG_f'fG : G \subset f @*^-1 (f @* G).
Proof. by rewrite -sub_morphim_pre. Qed.

Lemma morphim_mx_repr : mx_repr G (morphim_mx sGD).
Proof. exact: subg_mx_repr (morphpre_repr f rGf) sG_f'fG. Qed.
Canonical morphim_repr := MxRepresentation morphim_mx_repr.
Local Notation rG := morphim_repr.

Section Stabiliser.
Variables (m : nat) (U : 'M[R]_(m, n)).

Lemma rstab_morphim : rstab rG U = G :&: f @*^-1 rstab rGf U.
Proof. by rewrite -rstab_morphpre -(rstab_subg _ sG_f'fG). Qed.

End Stabiliser.

Lemma rker_morphim : rker rG = G :&: f @*^-1 (rker rGf).
Proof. exact: rstab_morphim. Qed.

End Morphim.

Section Conjugate.

Variables (gT : finGroupType) (G : {group gT}) (n : nat).
Variables (rG : mx_representation G n) (B : 'M[R]_n).

Definition rconj_mx of B \in unitmx := fun x => B *m rG x *m invmx B.

Hypothesis uB : B \in unitmx.

Lemma rconj_mx_repr : mx_repr G (rconj_mx uB).
Proof.
split=> [|x y Gx Gy]; rewrite /rconj_mx ?repr_mx1 ?mulmx1 ?mulmxV ?repr_mxM //.
by rewrite !mulmxA mulmxKV.
Qed.
Canonical rconj_repr := MxRepresentation rconj_mx_repr.
Local Notation rGB := rconj_repr.

Lemma rconj_mxE x : rGB x = B *m rG x *m invmx B.
Proof. by []. Qed.

Lemma rconj_mxJ m (W : 'M_(m, n)) x : W *m rGB x *m B = W *m B *m rG x.
Proof. by rewrite !mulmxA mulmxKV. Qed.

Lemma rcent_conj A : rcent rGB A = rcent rG (invmx B *m A *m B).
Proof.
apply/setP=> x; rewrite !inE /= rconj_mxE !mulmxA.
rewrite (can2_eq (mulmxKV uB) (mulmxK uB)) -!mulmxA.
by rewrite -(can2_eq (mulKVmx uB) (mulKmx uB)).
Qed.

Lemma rstab_conj m (U : 'M_(m, n)) : rstab rGB U = rstab rG (U *m B).
Proof.
apply/setP=> x; rewrite !inE /= rconj_mxE !mulmxA.
by rewrite (can2_eq (mulmxKV uB) (mulmxK uB)).
Qed.

Lemma rker_conj : rker rGB = rker rG.
Proof.
apply/setP=> x; rewrite !inE /= mulmxA (can2_eq (mulmxKV uB) (mulmxK uB)).
by rewrite mul1mx -scalar_mxC (inj_eq (can_inj (mulKmx uB))) mul1mx.
Qed.

Lemma conj_mx_faithful : mx_faithful rGB = mx_faithful rG.
Proof. by rewrite /mx_faithful rker_conj. Qed.

End Conjugate.

Section Quotient.

Variables (gT : finGroupType) (G : {group gT}) (n : nat).
Variable rG : mx_representation G n.

Definition quo_mx (H : {set gT}) of H \subset rker rG & G \subset 'N(H) :=
  fun Hx : coset_of H => rG (repr Hx).

Section SubQuotient.

Variable H : {group gT}.
Hypotheses (krH : H \subset rker rG) (nHG : G \subset 'N(H)).
Let nHGs := subsetP nHG.

Lemma quo_mx_coset x : x \in G -> quo_mx krH nHG (coset H x) = rG x.
Proof.
move=> Gx; rewrite /quo_mx val_coset ?nHGs //; case: repr_rcosetP => z Hz.
by case/rkerP: (subsetP krH z Hz) => Gz rz1; rewrite repr_mxM // rz1 mul1mx.
Qed.

Lemma quo_mx_repr : mx_repr (G / H)%g (quo_mx krH nHG).
Proof.
split=> [|Hx Hy]; first by rewrite /quo_mx repr_coset1 repr_mx1.
case/morphimP=> x Nx Gx ->{Hx}; case/morphimP=> y Ny Gy ->{Hy}.
by rewrite -morphM // !quo_mx_coset ?groupM ?repr_mxM.
Qed.
Canonical quo_repr := MxRepresentation quo_mx_repr.
Local Notation rGH := quo_repr.

Lemma quo_repr_coset x : x \in G -> rGH (coset H x) = rG x.
Proof. exact: quo_mx_coset. Qed.

Lemma rcent_quo A : rcent rGH A = (rcent rG A / H)%g.
Proof.
apply/setP=> Hx; rewrite !inE.
apply/andP/idP=> [[]|]; case/morphimP=> x Nx Gx ->{Hx}.
  by rewrite quo_repr_coset // => cAx; rewrite mem_morphim // inE Gx.
by case/setIdP: Gx => Gx cAx; rewrite quo_repr_coset ?mem_morphim.
Qed.

Lemma rstab_quo m (U : 'M_(m, n)) : rstab rGH U = (rstab rG U / H)%g.
Proof.
apply/setP=> Hx; rewrite !inE.
apply/andP/idP=> [[]|]; case/morphimP=> x Nx Gx ->{Hx}.
  by rewrite quo_repr_coset // => nUx; rewrite mem_morphim // inE Gx.
by case/setIdP: Gx => Gx nUx; rewrite quo_repr_coset ?mem_morphim.
Qed.

Lemma rker_quo : rker rGH = (rker rG / H)%g.
Proof. exact: rstab_quo. Qed.

End SubQuotient.

Definition kquo_mx := quo_mx (subxx (rker rG)) (rker_norm rG).
Lemma kquo_mxE : kquo_mx = quo_mx (subxx (rker rG)) (rker_norm rG).
Proof. by []. Qed.

Canonical kquo_repr := @MxRepresentation _ _ _ kquo_mx (quo_mx_repr _ _).

Lemma kquo_repr_coset x :
  x \in G -> kquo_repr (coset (rker rG) x) = rG x.
Proof. exact: quo_repr_coset. Qed.

Lemma kquo_mx_faithful : mx_faithful kquo_repr.
Proof. by rewrite /mx_faithful rker_quo trivg_quotient. Qed.

End Quotient.

Section Regular.

Variables (gT : finGroupType) (G : {group gT}).
Local Notation nG := #|pred_of_set (gval G)|.

Definition gring_index (x : gT) := enum_rank_in (group1 G) x.

Lemma gring_valK : cancel enum_val gring_index.
Proof. exact: enum_valK_in. Qed.

Lemma gring_indexK : {in G, cancel gring_index enum_val}.
Proof. exact: enum_rankK_in. Qed.
  
Definition regular_mx x : 'M[R]_nG :=
  \matrix_i delta_mx 0 (gring_index (enum_val i * x)).

Lemma regular_mx_repr : mx_repr G regular_mx.
Proof.
split=> [|x y Gx Gy]; apply/row_matrixP=> i; rewrite !rowK.
  by rewrite mulg1 row1 gring_valK.
by rewrite row_mul rowK -rowE rowK mulgA gring_indexK // groupM ?enum_valP.
Qed.
Canonical regular_repr := MxRepresentation regular_mx_repr.
Local Notation aG := regular_repr.

Definition group_ring := enveloping_algebra_mx aG.
Local Notation R_G := group_ring.

Definition gring_row : 'M[R]_nG -> 'rV_nG := row (gring_index 1).
Canonical gring_row_linear := [linear of gring_row].

Lemma gring_row_mul A B : gring_row (A *m B) = gring_row A *m B.
Proof. exact: row_mul. Qed.

Definition gring_proj x := row (gring_index x) \o trmx \o gring_row.
Canonical gring_proj_linear x := [linear of gring_proj x].

Lemma gring_projE : {in G &, forall x y, gring_proj x (aG y) = (x == y)%:R}.
Proof.
move=> x y Gx Gy; rewrite /gring_proj /= /gring_row rowK gring_indexK //=.
rewrite mul1g trmx_delta rowE mul_delta_mx_cond [delta_mx 0 0]mx11_scalar !mxE.
by rewrite /= -(inj_eq (can_inj gring_valK)) !gring_indexK.
Qed.

Lemma regular_mx_faithful : mx_faithful aG.
Proof.
apply/subsetP=> x /setIdP[Gx].
rewrite mul1mx inE => /eqP/(congr1 (gring_proj 1%g)).
rewrite -(repr_mx1 aG) !gring_projE ?group1 // eqxx eq_sym.
by case: (x == _) => // /eqP; rewrite eq_sym oner_eq0.
Qed.

Section GringMx.

Variables (n : nat) (rG : mx_representation G n).

Definition gring_mx := vec_mx \o mulmxr (enveloping_algebra_mx rG).
Canonical gring_mx_linear := [linear of gring_mx].

Lemma gring_mxJ a x :
  x \in G -> gring_mx (a *m aG x) = gring_mx a *m rG x.
Proof.
move=> Gx; rewrite /gring_mx /= ![a *m _]mulmx_sum_row.
rewrite !(mulmx_suml, linear_sum); apply: eq_bigr => i _.
rewrite linearZ -!scalemxAl linearZ /=; congr (_ *: _) => {a}.
rewrite !rowK /= !mxvecK -rowE rowK mxvecK.
by rewrite gring_indexK ?groupM ?repr_mxM ?enum_valP.
Qed.

End GringMx.

Lemma gring_mxK : cancel (gring_mx aG) gring_row.
Proof.
move=> a; rewrite /gring_mx /= mulmx_sum_row !linear_sum.
rewrite {2}[a]row_sum_delta; apply: eq_bigr => i _.
rewrite !linearZ /= /gring_row !(rowK, mxvecK).
by rewrite gring_indexK // mul1g gring_valK.
Qed.

Section GringOp.

Variables (n : nat) (rG : mx_representation G n).

Definition gring_op := gring_mx rG \o gring_row.
Canonical gring_op_linear := [linear of gring_op].

Lemma gring_opE a : gring_op a = gring_mx rG (gring_row a).
Proof. by []. Qed.

Lemma gring_opG x : x \in G -> gring_op (aG x) = rG x.
Proof.
move=> Gx; rewrite gring_opE /gring_row rowK gring_indexK // mul1g.
by rewrite /gring_mx /= -rowE rowK mxvecK gring_indexK.
Qed.

Lemma gring_op1 : gring_op 1%:M = 1%:M.
Proof. by rewrite -(repr_mx1 aG) gring_opG ?repr_mx1. Qed.

Lemma gring_opJ A b :
  gring_op (A *m gring_mx aG b) = gring_op A *m gring_mx rG b.
Proof.
rewrite /gring_mx /= ![b *m _]mulmx_sum_row !linear_sum.
apply: eq_bigr => i _; rewrite !linearZ /= !rowK !mxvecK.
by rewrite gring_opE gring_row_mul gring_mxJ ?enum_valP.
Qed.

Lemma gring_op_mx b : gring_op (gring_mx aG b) = gring_mx rG b.
Proof. by rewrite -[_ b]mul1mx gring_opJ gring_op1 mul1mx. Qed.

Lemma gring_mxA a b :
  gring_mx rG (a *m gring_mx aG b) = gring_mx rG a *m gring_mx rG b.
Proof.
by rewrite -(gring_op_mx a) -gring_opJ gring_opE gring_row_mul gring_mxK.
Qed.

End GringOp.

End Regular.

End RingRepr.

Arguments mx_representation R {gT} G%g n%N.
Arguments mx_repr {R gT} G%g {n%N} r.
Arguments group_ring R {gT} G%g.
Arguments regular_repr R {gT} G%g.

Arguments centgmxP {R gT G n rG f}.
Arguments rkerP {R gT G n rG x}.
Arguments repr_mxK {R gT G%G n%N} rG {m%N} [x%g] Gx.
Arguments repr_mxKV {R gT G%G n%N} rG {m%N} [x%g] Gx.
Arguments gring_valK {gT G%G} i%R : rename.
Arguments gring_indexK {gT G%G} x%g.
Arguments gring_mxK {R gT G%G} v%R : rename.

Section ChangeOfRing.

Variables (aR rR : comUnitRingType) (f : {rmorphism aR -> rR}).
Local Notation "A ^f" := (map_mx (GRing.RMorphism.apply f) A) : ring_scope.
Variables (gT : finGroupType) (G : {group gT}).

Lemma map_regular_mx x : (regular_mx aR G x)^f = regular_mx rR G x.
Proof. by apply/matrixP=> i j; rewrite !mxE rmorph_nat. Qed.

Lemma map_gring_row (A : 'M_#|G|) : (gring_row A)^f = gring_row A^f.
Proof. by rewrite map_row. Qed.

Lemma map_gring_proj x (A : 'M_#|G|) : (gring_proj x A)^f = gring_proj x A^f.
Proof. by rewrite map_row -map_trmx map_gring_row. Qed.

Section OneRepresentation.

Variables (n : nat) (rG : mx_representation aR G n).

Definition map_repr_mx (f0 : aR -> rR) rG0 (g : gT) : 'M_n := map_mx f0 (rG0 g).

Lemma map_mx_repr : mx_repr G (map_repr_mx f rG).
Proof.
split=> [|x y Gx Gy]; first by rewrite /map_repr_mx repr_mx1 map_mx1.
by rewrite -map_mxM -repr_mxM.
Qed.
Canonical map_repr := MxRepresentation map_mx_repr.
Local Notation rGf := map_repr.

Lemma map_reprE x : rGf x = (rG x)^f. Proof. by []. Qed.

Lemma map_reprJ m (A : 'M_(m, n)) x : (A *m rG x)^f = A^f *m rGf x.
Proof. exact: map_mxM. Qed.

Lemma map_enveloping_algebra_mx :
  (enveloping_algebra_mx rG)^f = enveloping_algebra_mx rGf.
Proof. by apply/row_matrixP=> i; rewrite -map_row !rowK map_mxvec. Qed.

Lemma map_gring_mx a : (gring_mx rG a)^f = gring_mx rGf a^f.
Proof. by rewrite map_vec_mx map_mxM map_enveloping_algebra_mx. Qed.

Lemma map_gring_op A : (gring_op rG A)^f = gring_op rGf A^f.
Proof. by rewrite map_gring_mx map_gring_row. Qed.

End OneRepresentation.

Lemma map_regular_repr : map_repr (regular_repr aR G) =1 regular_repr rR G.
Proof. exact: map_regular_mx. Qed.

Lemma map_group_ring : (group_ring aR G)^f = group_ring rR G.
Proof.
rewrite map_enveloping_algebra_mx; apply/row_matrixP=> i.
by rewrite !rowK map_regular_repr.
Qed.

(* Stabilisers, etc, are only mapped properly for fields. *)

End ChangeOfRing.

Section FieldRepr.

Variable F : fieldType.

Section OneRepresentation.

Variable gT : finGroupType.

Variables (G : {group gT}) (n : nat) (rG : mx_representation F G n).
Arguments rG _%group_scope : extra scopes.

Local Notation E_G := (enveloping_algebra_mx rG).

Lemma repr_mx_free x : x \in G -> row_free (rG x).
Proof. by move=> Gx; rewrite row_free_unit repr_mx_unit. Qed.

Section Stabilisers.

Variables (m : nat) (U : 'M[F]_(m, n)).

Definition rstabs := [set x in G | U *m rG x <= U]%MS.

Lemma rstabs_sub : rstabs \subset G.
Proof. by apply/subsetP=> x /setIdP[]. Qed.

Lemma rstabs_group_set : group_set rstabs.
Proof.
apply/group_setP; rewrite inE group1 repr_mx1 mulmx1.
split=> //= x y /setIdP[Gx nUx] /setIdP[Gy]; rewrite inE repr_mxM ?groupM //.
by apply: submx_trans; rewrite mulmxA submxMr.
Qed.
Canonical rstabs_group := Group rstabs_group_set.

Lemma rstab_act x m1 (W : 'M_(m1, n)) :
  x \in rstab rG U -> (W <= U)%MS -> W *m rG x = W.
Proof. by case/setIdP=> _ /eqP cUx /submxP[w ->]; rewrite -mulmxA cUx. Qed.

Lemma rstabs_act x m1 (W : 'M_(m1, n)) :
  x \in rstabs -> (W <= U)%MS -> (W *m rG x <= U)%MS.
Proof.
by case/setIdP=> [_ nUx] sWU; apply: submx_trans nUx; apply: submxMr.
Qed.

Definition mxmodule := G \subset rstabs.

Lemma mxmoduleP : reflect {in G, forall x, U *m rG x <= U}%MS mxmodule.
Proof.
by apply: (iffP subsetP) => modU x Gx; have:= modU x Gx; rewrite !inE ?Gx.
Qed.

End Stabilisers.
Arguments mxmoduleP {m U}.

Lemma rstabS m1 m2 (U : 'M_(m1, n)) (V : 'M_(m2, n)) :
  (U <= V)%MS -> rstab rG V \subset rstab rG U.
Proof.
case/submxP=> u ->; apply/subsetP=> x.
by rewrite !inE => /andP[-> /= /eqP cVx]; rewrite -mulmxA cVx.
Qed.

Lemma eqmx_rstab m1 m2 (U : 'M_(m1, n)) (V : 'M_(m2, n)) :
  (U :=: V)%MS -> rstab rG U = rstab rG V.
Proof. by move=> eqUV; apply/eqP; rewrite eqEsubset !rstabS ?eqUV. Qed.

Lemma eqmx_rstabs m1 m2 (U : 'M_(m1, n)) (V : 'M_(m2, n)) :
  (U :=: V)%MS -> rstabs U = rstabs V.
Proof. by move=> eqUV; apply/setP=> x; rewrite !inE eqUV (eqmxMr _ eqUV). Qed.

Lemma eqmx_module m1 m2 (U : 'M_(m1, n)) (V : 'M_(m2, n)) :
  (U :=: V)%MS -> mxmodule U = mxmodule V.
Proof. by move=> eqUV; rewrite /mxmodule (eqmx_rstabs eqUV). Qed.

Lemma mxmodule0 m : mxmodule (0 : 'M_(m, n)).
Proof. by apply/mxmoduleP=> x _; rewrite mul0mx. Qed.

Lemma mxmodule1 : mxmodule 1%:M.
Proof. by apply/mxmoduleP=> x _; rewrite submx1. Qed.

Lemma mxmodule_trans m1 m2 (U : 'M_(m1, n)) (W : 'M_(m2, n)) x :
  mxmodule U -> x \in G -> (W <= U -> W *m rG x <= U)%MS.
Proof.
by move=> modU Gx sWU; apply: submx_trans (mxmoduleP modU x Gx); apply: submxMr.
Qed.

Lemma mxmodule_eigenvector m (U : 'M_(m, n)) :
    mxmodule U -> \rank U = 1%N ->
  {u : 'rV_n & {a | (U :=: u)%MS & {in G, forall x, u *m rG x = a x *: u}}}.
Proof.
move=> modU linU; set u := nz_row U; exists u.
have defU: (U :=: u)%MS.
  apply/eqmxP; rewrite andbC -(geq_leqif (mxrank_leqif_eq _)) ?nz_row_sub //.
  by rewrite linU lt0n mxrank_eq0 nz_row_eq0 -mxrank_eq0 linU.
pose a x := (u *m rG x *m pinvmx u) 0 0; exists a => // x Gx.
by rewrite -mul_scalar_mx -mx11_scalar mulmxKpV // -defU mxmodule_trans ?defU.
Qed.

Lemma addsmx_module m1 m2 U V :
  @mxmodule m1 U -> @mxmodule m2 V -> mxmodule (U + V)%MS.
Proof.
move=> modU modV; apply/mxmoduleP=> x Gx.
by rewrite addsmxMr addsmxS ?(mxmoduleP _ x Gx).
Qed.

Lemma sumsmx_module I r (P : pred I) U :
  (forall i, P i -> mxmodule (U i)) -> mxmodule (\sum_(i <- r | P i) U i)%MS.
Proof.
by move=> modU; elim/big_ind: _; [apply: mxmodule0 | apply: addsmx_module | ].
Qed.

Lemma capmx_module m1 m2 U V :
  @mxmodule m1 U -> @mxmodule m2 V -> mxmodule (U :&: V)%MS.
Proof.
move=> modU modV; apply/mxmoduleP=> x Gx.
by rewrite sub_capmx !mxmodule_trans ?capmxSl ?capmxSr.
Qed.

Lemma bigcapmx_module I r (P : pred I) U :
  (forall i, P i -> mxmodule (U i)) -> mxmodule (\bigcap_(i <- r | P i) U i)%MS.
Proof.
by move=> modU; elim/big_ind: _; [apply: mxmodule1 | apply: capmx_module | ].
Qed.

(* Sub- and factor representations induced by a (sub)module. *)
Section Submodule.

Variable U : 'M[F]_n.

Definition val_submod m : 'M_(m, \rank U) -> 'M_(m, n) := mulmxr (row_base U).
Definition in_submod m : 'M_(m, n) -> 'M_(m, \rank U) :=
   mulmxr (invmx (row_ebase U) *m pid_mx (\rank U)).
Canonical val_submod_linear m := [linear of @val_submod m].
Canonical in_submod_linear m := [linear of @in_submod m].

Lemma val_submodE m W : @val_submod m W = W *m val_submod 1%:M.
Proof. by rewrite mulmxA mulmx1. Qed.

Lemma in_submodE m W : @in_submod m W = W *m in_submod 1%:M.
Proof. by rewrite mulmxA mulmx1. Qed.

Lemma val_submod1 : (val_submod 1%:M :=: U)%MS.
Proof. by rewrite /val_submod /= mul1mx; apply: eq_row_base. Qed.

Lemma val_submodP m W : (@val_submod m W <= U)%MS.
Proof. by rewrite mulmx_sub ?eq_row_base. Qed.

Lemma val_submodK m : cancel (@val_submod m) (@in_submod m).
Proof.
move=> W; rewrite /in_submod /= -!mulmxA mulKVmx ?row_ebase_unit //.
by rewrite pid_mx_id ?rank_leq_row // pid_mx_1 mulmx1.
Qed.

Lemma val_submod_inj m : injective (@val_submod m).
Proof. exact: can_inj (@val_submodK m). Qed.

Lemma val_submodS m1 m2 (V : 'M_(m1, \rank U)) (W : 'M_(m2, \rank U)) :
  (val_submod V <= val_submod W)%MS = (V <= W)%MS.
Proof.
apply/idP/idP=> sVW; last exact: submxMr.
by rewrite -[V]val_submodK -[W]val_submodK submxMr.
Qed.

Lemma in_submodK m W : (W <= U)%MS -> val_submod (@in_submod m W) = W.
Proof.
case/submxP=> w ->; rewrite /val_submod /= -!mulmxA.
congr (_ *m _); rewrite -{1}[U]mulmx_ebase !mulmxA mulmxK ?row_ebase_unit //.
by rewrite -2!(mulmxA (col_ebase U)) !pid_mx_id ?rank_leq_row // mulmx_ebase.
Qed.

Lemma val_submod_eq0 m W : (@val_submod m W == 0) = (W == 0).
Proof. by rewrite -!submx0 -val_submodS linear0 !(submx0, eqmx0). Qed.

Lemma in_submod_eq0 m W : (@in_submod m W == 0) = (W <= U^C)%MS.
Proof.
apply/eqP/submxP=> [W_U0 | [w ->{W}]].
  exists (W *m invmx (row_ebase U)).
  rewrite mulmxA mulmxBr mulmx1 -(pid_mx_id _ _ _ (leqnn _)).
  rewrite mulmxA -(mulmxA W) [W *m (_ *m _)]W_U0 mul0mx subr0.
  by rewrite mulmxKV ?row_ebase_unit.
rewrite /in_submod /= -!mulmxA mulKVmx ?row_ebase_unit //.
by rewrite mul_copid_mx_pid ?rank_leq_row ?mulmx0.
Qed.

Lemma mxrank_in_submod m (W : 'M_(m, n)) :
  (W <= U)%MS -> \rank (in_submod W) = \rank W.
Proof.
by move=> sWU; apply/eqP; rewrite eqn_leq -{3}(in_submodK sWU) !mxrankM_maxl.
Qed.

Definition val_factmod m : _ -> 'M_(m, n) :=
  mulmxr (row_base (cokermx U) *m row_ebase U).
Definition in_factmod m : 'M_(m, n) -> _ := mulmxr (col_base (cokermx U)).
Canonical val_factmod_linear m := [linear of @val_factmod m].
Canonical in_factmod_linear m := [linear of @in_factmod m].

Lemma val_factmodE m W : @val_factmod m W = W *m val_factmod 1%:M.
Proof. by rewrite mulmxA mulmx1. Qed.

Lemma in_factmodE m W : @in_factmod m W = W *m in_factmod 1%:M.
Proof. by rewrite mulmxA mulmx1. Qed.

Lemma val_factmodP m W : (@val_factmod m W <= U^C)%MS.
Proof.
by rewrite mulmx_sub {m W}// (eqmxMr _ (eq_row_base _)) -mulmxA submxMl.
Qed.

Lemma val_factmodK m : cancel (@val_factmod m) (@in_factmod m).
Proof.
move=> W /=; rewrite /in_factmod /=; set Uc := cokermx U.
apply: (row_free_inj (row_base_free Uc)); rewrite -mulmxA mulmx_base.
rewrite /val_factmod /= 2!mulmxA -/Uc mulmxK ?row_ebase_unit //.
have /submxP[u ->]: (row_base Uc <= Uc)%MS by rewrite eq_row_base.
by rewrite -!mulmxA copid_mx_id ?rank_leq_row.
Qed.

Lemma val_factmod_inj m : injective (@val_factmod m).
Proof. exact: can_inj (@val_factmodK m). Qed.

Lemma val_factmodS m1 m2 (V : 'M_(m1, _)) (W : 'M_(m2, _)) :
  (val_factmod V <= val_factmod W)%MS = (V <= W)%MS.
Proof.
apply/idP/idP=> sVW; last exact: submxMr.
by rewrite -[V]val_factmodK -[W]val_factmodK submxMr.
Qed.

Lemma val_factmod_eq0 m W : (@val_factmod m W == 0) = (W == 0).
Proof. by rewrite -!submx0 -val_factmodS linear0 !(submx0, eqmx0). Qed.

Lemma in_factmod_eq0 m (W : 'M_(m, n)) : (in_factmod W == 0) = (W <= U)%MS.
Proof.
rewrite submxE -!mxrank_eq0 -{2}[_ U]mulmx_base mulmxA.
by rewrite (mxrankMfree _ (row_base_free _)).
Qed.

Lemma in_factmodK m (W : 'M_(m, n)) :
  (W <= U^C)%MS -> val_factmod (in_factmod W) = W.
Proof.
case/submxP=> w ->{W}; rewrite /val_factmod /= -2!mulmxA.
congr (_ *m _); rewrite (mulmxA (col_base _)) mulmx_base -2!mulmxA.
by rewrite mulKVmx ?row_ebase_unit // mulmxA copid_mx_id ?rank_leq_row.
Qed.

Lemma in_factmod_addsK m (W : 'M_(m, n)) :
  (in_factmod (U + W)%MS :=: in_factmod W)%MS.
Proof.
apply: eqmx_trans (addsmxMr _ _ _) _.
by rewrite ((_ *m _ =P 0) _) ?in_factmod_eq0 //; apply: adds0mx.
Qed.

Lemma add_sub_fact_mod m (W : 'M_(m, n)) :
  val_submod (in_submod W) + val_factmod (in_factmod W) = W.
Proof.
rewrite /val_submod /val_factmod /= -!mulmxA -mulmxDr.
rewrite addrC (mulmxA (pid_mx _)) pid_mx_id // (mulmxA (col_ebase _)).
rewrite (mulmxA _ _ (row_ebase _)) mulmx_ebase.
rewrite (mulmxA (pid_mx _)) pid_mx_id // mulmxA -mulmxDl -mulmxDr.
by rewrite subrK mulmx1 mulmxA mulmxKV ?row_ebase_unit.
Qed.

Lemma proj_factmodS m (W : 'M_(m, n)) :
  (val_factmod (in_factmod W) <= U + W)%MS.
Proof.
by rewrite -{2}[W]add_sub_fact_mod addsmx_addKl ?val_submodP ?addsmxSr.
Qed.

Lemma in_factmodsK m (W : 'M_(m, n)) :
  (U <= W)%MS -> (U + val_factmod (in_factmod W) :=: W)%MS.
Proof.
move/addsmx_idPr; apply: eqmx_trans (eqmx_sym _).
by rewrite -{1}[W]add_sub_fact_mod; apply: addsmx_addKl; apply: val_submodP.
Qed.

Lemma mxrank_in_factmod m (W : 'M_(m, n)) :
  (\rank (in_factmod W) + \rank U)%N = \rank (U + W).
Proof.
rewrite -in_factmod_addsK in_factmodE; set fU := in_factmod 1%:M.
suffices <-: ((U + W) :&: kermx fU :=: U)%MS by rewrite mxrank_mul_ker.
apply: eqmx_trans (capmx_idPr (addsmxSl U W)).
apply: cap_eqmx => //; apply/eqmxP/rV_eqP => u.
by rewrite (sameP sub_kermxP eqP) -in_factmodE in_factmod_eq0.
Qed.

Definition submod_mx of mxmodule U :=
  fun x => in_submod (val_submod 1%:M *m rG x).

Definition factmod_mx of mxmodule U :=
  fun x => in_factmod (val_factmod 1%:M *m rG x).

Hypothesis Umod : mxmodule U.

Lemma in_submodJ m (W : 'M_(m, n)) x :
  (W <= U)%MS -> in_submod (W *m rG x) = in_submod W *m submod_mx Umod x.
Proof.
move=> sWU; rewrite mulmxA; congr (in_submod _).
by rewrite mulmxA -val_submodE in_submodK.
Qed.

Lemma val_submodJ m (W : 'M_(m, \rank U)) x :
  x \in G -> val_submod (W *m submod_mx Umod x) = val_submod W *m rG x.
Proof.
move=> Gx; rewrite 2!(mulmxA W) -val_submodE in_submodK //.
by rewrite mxmodule_trans ?val_submodP.
Qed.

Lemma submod_mx_repr : mx_repr G (submod_mx Umod).
Proof.
rewrite /submod_mx; split=> [|x y Gx Gy /=].
  by rewrite repr_mx1 mulmx1 val_submodK.
rewrite -in_submodJ; first by rewrite repr_mxM ?mulmxA.
by rewrite mxmodule_trans ?val_submodP.
Qed.

Canonical submod_repr := MxRepresentation submod_mx_repr.

Lemma in_factmodJ m (W : 'M_(m, n)) x :
  x \in G -> in_factmod (W *m rG x) = in_factmod W *m factmod_mx Umod x.
Proof.
move=> Gx; rewrite -{1}[W]add_sub_fact_mod mulmxDl linearD /=.
apply: (canLR (subrK _)); apply: etrans (_ : 0 = _).
  apply/eqP; rewrite in_factmod_eq0 (submx_trans _ (mxmoduleP Umod x Gx)) //.
  by rewrite submxMr ?val_submodP.
by rewrite /in_factmod /val_factmod /= !mulmxA mulmx1 ?subrr.
Qed.

Lemma val_factmodJ m (W : 'M_(m, \rank (cokermx U))) x :
  x \in G ->
  val_factmod (W *m factmod_mx Umod x) =
     val_factmod (in_factmod (val_factmod W *m rG x)).
Proof. by move=> Gx; rewrite -{1}[W]val_factmodK -in_factmodJ. Qed.

Lemma factmod_mx_repr : mx_repr G (factmod_mx Umod).
Proof.
split=> [|x y Gx Gy /=].
  by rewrite /factmod_mx repr_mx1 mulmx1 val_factmodK.
by rewrite -in_factmodJ // -mulmxA -repr_mxM.
Qed.
Canonical factmod_repr := MxRepresentation factmod_mx_repr.

(* For character theory. *)
Lemma mxtrace_sub_fact_mod x :
  \tr (submod_repr x) + \tr (factmod_repr x) = \tr (rG x).
Proof.
rewrite -[submod_repr x]mulmxA mxtrace_mulC -val_submodE addrC.
rewrite -[factmod_repr x]mulmxA mxtrace_mulC -val_factmodE addrC.
by rewrite -mxtraceD add_sub_fact_mod.
Qed.

End Submodule.

(* Properties of enveloping algebra as a subspace of 'rV_(n ^ 2). *)

Lemma envelop_mx_id x : x \in G -> (rG x \in E_G)%MS.
Proof.
by move=> Gx; rewrite (eq_row_sub (enum_rank_in Gx x)) // rowK enum_rankK_in.
Qed.

Lemma envelop_mx1 : (1%:M \in E_G)%MS.
Proof. by rewrite -(repr_mx1 rG) envelop_mx_id. Qed.

Lemma envelop_mxP A :
  reflect (exists a, A = \sum_(x in G) a x *: rG x) (A \in E_G)%MS.
Proof.
have G_1 := group1 G; have bijG := enum_val_bij_in G_1.
set h := enum_val in bijG; have Gh: h _ \in G by apply: enum_valP.
apply: (iffP submxP) => [[u defA] | [a ->]].
  exists (fun x => u 0 (enum_rank_in G_1 x)); apply: (can_inj mxvecK).
  rewrite defA mulmx_sum_row linear_sum (reindex h) //=.
  by apply: eq_big => [i | i _]; rewrite ?Gh // rowK linearZ enum_valK_in.
exists (\row_i a (h i)); rewrite mulmx_sum_row linear_sum (reindex h) //=.
by apply: eq_big => [i | i _]; rewrite ?Gh // mxE rowK linearZ.
Qed.

Lemma envelop_mxM A B : (A \in E_G -> B \in E_G -> A *m B \in E_G)%MS.
Proof.
case/envelop_mxP=> a ->{A}; case/envelop_mxP=> b ->{B}.
rewrite mulmx_suml !linear_sum summx_sub //= => x Gx.
rewrite !linear_sum summx_sub //= => y Gy.
rewrite -scalemxAl !(linearZ, scalemx_sub) //= -repr_mxM //.
by rewrite envelop_mx_id ?groupM.
Qed.

Lemma mxmodule_envelop m1 m2 (U : 'M_(m1, n)) (W : 'M_(m2, n)) A :
  (mxmodule U -> mxvec A <= E_G -> W <= U -> W *m A <= U)%MS.
Proof.
move=> modU /envelop_mxP[a ->] sWU; rewrite linear_sum summx_sub // => x Gx.
by rewrite linearZ scalemx_sub ?mxmodule_trans.
Qed.

(* Module homomorphisms; any square matrix f defines a module homomorphism   *)
(* over some domain, namely, dom_hom_mx f.                                   *)

Definition dom_hom_mx f : 'M_n :=
  kermx (lin1_mx (mxvec \o mulmx (cent_mx_fun E_G f) \o lin_mul_row)).

Lemma hom_mxP m f (W : 'M_(m, n)) :
  reflect (forall x, x \in G -> W *m rG x *m f = W *m f *m rG x)
          (W <= dom_hom_mx f)%MS.
Proof.
apply: (iffP row_subP) => [cGf x Gx | cGf i].
  apply/row_matrixP=> i; apply/eqP; rewrite -subr_eq0 -!mulmxA -!linearB /=.
  have:= sub_kermxP (cGf i); rewrite mul_rV_lin1 /=.
  move/(canRL mxvecK)/row_matrixP/(_ (enum_rank_in Gx x))/eqP; rewrite !linear0.
  by rewrite !row_mul rowK mul_vec_lin /= mul_vec_lin_row enum_rankK_in.
apply/sub_kermxP; rewrite mul_rV_lin1 /=; apply: (canLR vec_mxK).
apply/row_matrixP=> j; rewrite !row_mul rowK mul_vec_lin /= mul_vec_lin_row.
by rewrite -!row_mul mulmxBr !mulmxA cGf ?enum_valP // subrr !linear0.
Qed.
Arguments hom_mxP {m f W}.

Lemma hom_envelop_mxC m f (W : 'M_(m, n)) A :
  (W <= dom_hom_mx f -> A \in E_G -> W *m A *m f = W *m f *m A)%MS.
Proof.
move/hom_mxP=> cWfG /envelop_mxP[a ->]; rewrite !linear_sum mulmx_suml.
by apply: eq_bigr => x Gx; rewrite !linearZ -scalemxAl /= cWfG.
Qed.

Lemma dom_hom_invmx f :
  f \in unitmx -> (dom_hom_mx (invmx f) :=: dom_hom_mx f *m f)%MS.
Proof.
move=> injf; set U := dom_hom_mx _; apply/eqmxP.
rewrite -{1}[U](mulmxKV injf) submxMr; apply/hom_mxP=> x Gx.
  by rewrite -[_ *m rG x](hom_mxP _) ?mulmxK.
by rewrite -[_ *m rG x](hom_mxP _) ?mulmxKV.
Qed.

Lemma dom_hom_mx_module f : mxmodule (dom_hom_mx f).
Proof.
apply/mxmoduleP=> x Gx; apply/hom_mxP=> y Gy.
rewrite -[_ *m rG y]mulmxA -repr_mxM // 2?(hom_mxP _) ?groupM //.
by rewrite repr_mxM ?mulmxA.
Qed.

Lemma hom_mxmodule m (U : 'M_(m, n)) f :
  (U <= dom_hom_mx f)%MS -> mxmodule U -> mxmodule (U *m f).
Proof.
move/hom_mxP=> cGfU modU; apply/mxmoduleP=> x Gx.
by rewrite -cGfU // submxMr // (mxmoduleP modU).
Qed.

Lemma kermx_hom_module m (U : 'M_(m, n)) f :
  (U <= dom_hom_mx f)%MS -> mxmodule U -> mxmodule (U :&: kermx f)%MS.
Proof.
move=> homUf modU; apply/mxmoduleP=> x Gx.
rewrite sub_capmx mxmodule_trans ?capmxSl //=.
apply/sub_kermxP; rewrite (hom_mxP _) ?(submx_trans (capmxSl _ _)) //.
by rewrite (sub_kermxP (capmxSr _ _)) mul0mx.
Qed.

Lemma scalar_mx_hom a m (U : 'M_(m, n)) : (U <= dom_hom_mx a%:M)%MS.
Proof. by apply/hom_mxP=> x Gx; rewrite -!mulmxA scalar_mxC. Qed.

Lemma proj_mx_hom (U V : 'M_n) :
    (U :&: V = 0)%MS -> mxmodule U -> mxmodule V ->
  (U + V <= dom_hom_mx (proj_mx U V))%MS.
Proof.
move=> dxUV modU modV; apply/hom_mxP=> x Gx.
rewrite -{1}(add_proj_mx dxUV (submx_refl _)) !mulmxDl addrC.
rewrite {1}[_ *m _]proj_mx_0 ?add0r //; last first.
  by rewrite mxmodule_trans ?proj_mx_sub.
by rewrite [_ *m _](proj_mx_id dxUV) // mxmodule_trans ?proj_mx_sub.
Qed.

(* The subspace fixed by a subgroup H of G; it is a module if H <| G.         *)
(* The definition below is extensionally equivalent to the straightforward    *)
(*    \bigcap_(x in H) kermx (rG x - 1%:M)                                    *)
(* but it avoids the dependency on the choice function; this allows it to     *)
(* commute with ring morphisms.                                               *)

Definition rfix_mx (H : {set gT}) :=
  let commrH := \matrix_(i < #|H|) mxvec (rG (enum_val i) - 1%:M) in
  kermx (lin1_mx (mxvec \o mulmx commrH \o lin_mul_row)).

Lemma rfix_mxP m (W : 'M_(m, n)) (H : {set gT}) :
  reflect (forall x, x \in H -> W *m rG x = W) (W <= rfix_mx H)%MS.
Proof.
rewrite /rfix_mx; set C := \matrix_i _.
apply: (iffP row_subP) => [cHW x Hx | cHW j].
  apply/row_matrixP=> j; apply/eqP; rewrite -subr_eq0 row_mul.
  move/sub_kermxP: {cHW}(cHW j); rewrite mul_rV_lin1 /=; move/(canRL mxvecK).
  move/row_matrixP/(_ (enum_rank_in Hx x)); rewrite row_mul rowK !linear0.
  by rewrite enum_rankK_in // mul_vec_lin_row mulmxBr mulmx1 => ->.
apply/sub_kermxP; rewrite mul_rV_lin1 /=; apply: (canLR vec_mxK).
apply/row_matrixP=> i; rewrite row_mul rowK mul_vec_lin_row -row_mul.
by rewrite mulmxBr mulmx1 cHW ?enum_valP // subrr !linear0.
Qed.
Arguments rfix_mxP {m W}.

Lemma rfix_mx_id (H : {set gT}) x : x \in H -> rfix_mx H *m rG x = rfix_mx H.
Proof. exact/rfix_mxP. Qed.

Lemma rfix_mxS (H K : {set gT}) : H \subset K -> (rfix_mx K <= rfix_mx H)%MS.
Proof.
by move=> sHK; apply/rfix_mxP=> x Hx; apply: rfix_mxP (subsetP sHK x Hx).
Qed.

Lemma rfix_mx_conjsg (H : {set gT}) x :
  x \in G -> H \subset G -> (rfix_mx (H :^ x) :=: rfix_mx H *m rG x)%MS.
Proof.
move=> Gx sHG; pose rf y := rfix_mx (H :^ y).
suffices{x Gx} IH: {in G &, forall y z, rf y *m rG z <= rf (y * z)%g}%MS.
  apply/eqmxP; rewrite -/(rf x) -[H]conjsg1 -/(rf 1%g).
  rewrite -{4}[x] mul1g -{1}[rf x](repr_mxKV rG Gx) -{1}(mulgV x).
  by rewrite submxMr IH ?groupV.
move=> x y Gx Gy; apply/rfix_mxP=> zxy; rewrite actM => /imsetP[zx Hzx ->].
have Gzx: zx \in G by apply: subsetP Hzx; rewrite conj_subG.
rewrite -mulmxA -repr_mxM ?groupM ?groupV // -conjgC repr_mxM // mulmxA.
by rewrite rfix_mx_id.
Qed.

Lemma norm_sub_rstabs_rfix_mx (H : {set gT}) :
  H \subset G -> 'N_G(H) \subset rstabs (rfix_mx H).
Proof.
move=> sHG; apply/subsetP=> x /setIP[Gx nHx]; rewrite inE Gx.
apply/rfix_mxP=> y Hy; have Gy := subsetP sHG y Hy.
have Hyx: (y ^ x^-1)%g \in H by rewrite memJ_norm ?groupV.
rewrite -mulmxA -repr_mxM // conjgCV repr_mxM ?(subsetP sHG _ Hyx) // mulmxA.
by rewrite (rfix_mx_id Hyx).
Qed.

Lemma normal_rfix_mx_module H : H <| G -> mxmodule (rfix_mx H).
Proof.
case/andP=> sHG nHG.
by rewrite /mxmodule -{1}(setIidPl nHG) norm_sub_rstabs_rfix_mx.
Qed.

Lemma rfix_mx_module : mxmodule (rfix_mx G).
Proof. exact: normal_rfix_mx_module. Qed.

Lemma rfix_mx_rstabC (H : {set gT}) m (U : 'M[F]_(m, n)) :
  H \subset G -> (H \subset rstab rG U) = (U <= rfix_mx H)%MS.
Proof.
move=> sHG; apply/subsetP/rfix_mxP=> cHU x Hx.
  by rewrite (rstab_act (cHU x Hx)).
by rewrite !inE (subsetP sHG) //= cHU.
Qed.

(* The cyclic module generated by a single vector. *)
Definition cyclic_mx u := <<E_G *m lin_mul_row u>>%MS.

Lemma cyclic_mxP u v :
  reflect (exists2 A, A \in E_G & v = u *m A)%MS (v <= cyclic_mx u)%MS.
Proof.
rewrite genmxE; apply: (iffP submxP) => [[a] | [A /submxP[a defA]]] -> {v}.
  exists (vec_mx (a *m E_G)); last by rewrite mulmxA mul_rV_lin1.
  by rewrite vec_mxK submxMl.
by exists a; rewrite mulmxA mul_rV_lin1 /= -defA mxvecK.
Qed.
Arguments cyclic_mxP {u v}.

Lemma cyclic_mx_id u : (u <= cyclic_mx u)%MS.
Proof. by apply/cyclic_mxP; exists 1%:M; rewrite ?mulmx1 ?envelop_mx1. Qed.

Lemma cyclic_mx_eq0 u : (cyclic_mx u == 0) = (u == 0).
Proof.
rewrite -!submx0; apply/idP/idP.
  by apply: submx_trans; apply: cyclic_mx_id.
move/submx0null->; rewrite genmxE; apply/row_subP=> i.
by rewrite row_mul mul_rV_lin1 /= mul0mx ?sub0mx.
Qed.

Lemma cyclic_mx_module u : mxmodule (cyclic_mx u).
Proof.
apply/mxmoduleP=> x Gx; apply/row_subP=> i; rewrite row_mul.
have [A E_A ->{i}] := @cyclic_mxP u _ (row_sub i _); rewrite -mulmxA.
by apply/cyclic_mxP; exists (A *m rG x); rewrite ?envelop_mxM ?envelop_mx_id.
Qed.

Lemma cyclic_mx_sub m u (W : 'M_(m, n)) :
  mxmodule W -> (u <= W)%MS -> (cyclic_mx u <= W)%MS.
Proof.
move=> modU Wu; rewrite genmxE; apply/row_subP=> i.
by rewrite row_mul mul_rV_lin1 /= mxmodule_envelop // vec_mxK row_sub.
Qed.

Lemma hom_cyclic_mx u f :
  (u <= dom_hom_mx f)%MS -> (cyclic_mx u *m f :=: cyclic_mx (u *m f))%MS.
Proof.
move=> domf_u; apply/eqmxP; rewrite !(eqmxMr _ (genmxE _)).
apply/genmxP; rewrite genmx_id; congr <<_>>%MS; apply/row_matrixP=> i.
by rewrite !row_mul !mul_rV_lin1 /= hom_envelop_mxC // vec_mxK row_sub.
Qed.

(* The annihilator of a single vector. *)

Definition annihilator_mx u := (E_G :&: kermx (lin_mul_row u))%MS.

Lemma annihilator_mxP u A :
  reflect (A \in E_G /\ u *m A = 0)%MS (A \in annihilator_mx u)%MS.
Proof.
rewrite sub_capmx; apply: (iffP andP) => [[-> /sub_kermxP]|[-> uA0]].
  by rewrite mul_rV_lin1 /= mxvecK.
by split=> //; apply/sub_kermxP; rewrite mul_rV_lin1 /= mxvecK.
Qed.

(* The subspace of homomorphic images of a row vector.                        *)

Definition row_hom_mx u :=
  (\bigcap_j kermx (vec_mx (row j (annihilator_mx u))))%MS.

Lemma row_hom_mxP u v :
  reflect (exists2 f, u <= dom_hom_mx f & u *m f = v)%MS (v <= row_hom_mx u)%MS.
Proof.
apply: (iffP sub_bigcapmxP) => [iso_uv | [f hom_uf <-] i _].
  have{iso_uv} uv0 A: (A \in E_G)%MS /\ u *m A = 0 -> v *m A = 0.
    move/annihilator_mxP=> /submxP[a defA].
    rewrite -[A]mxvecK {A}defA [a *m _]mulmx_sum_row !linear_sum big1 // => i _.
    by rewrite !linearZ /= (sub_kermxP _) ?scaler0 ?iso_uv.
  pose U := E_G *m lin_mul_row u; pose V :=  E_G *m lin_mul_row v.
  pose f := pinvmx U *m V.
  have hom_uv_f x: x \in G -> u *m rG x *m f = v *m rG x.
    move=> Gx; apply/eqP; rewrite 2!mulmxA mul_rV_lin1 -subr_eq0 -mulmxBr.
    rewrite uv0 // 2!linearB /= vec_mxK; split.
      by rewrite addmx_sub ?submxMl // eqmx_opp envelop_mx_id.
    have Uux: (u *m rG x <= U)%MS.
      by rewrite -(genmxE U) mxmodule_trans ?cyclic_mx_id ?cyclic_mx_module.
    by rewrite -{2}(mulmxKpV Uux) [_ *m U]mulmxA mul_rV_lin1 subrr.
  have def_uf: u *m f = v.
    by rewrite -[u]mulmx1 -[v]mulmx1 -(repr_mx1 rG) hom_uv_f.
  by exists f => //; apply/hom_mxP=> x Gx; rewrite def_uf hom_uv_f.
apply/sub_kermxP; set A := vec_mx _.
have: (A \in annihilator_mx u)%MS by rewrite vec_mxK row_sub.
by case/annihilator_mxP => E_A uA0; rewrite -hom_envelop_mxC // uA0 mul0mx.
Qed.

(* Sub-, isomorphic, simple, semisimple and completely reducible modules.     *)
(* All these predicates are intuitionistic (since, e.g., testing simplicity   *)
(* requires a splitting algorithm fo r the mas field). They are all           *)
(* specialized to square matrices, to avoid spurrious height parameters.      *)

(* Module isomorphism is an intentional property in general, but it can be    *)
(* decided when one of the two modules is known to be simple.                 *)

Variant mx_iso (U V : 'M_n) : Prop :=
  MxIso f of f \in unitmx & (U <= dom_hom_mx f)%MS & (U *m f :=: V)%MS.

Lemma eqmx_iso U V : (U :=: V)%MS -> mx_iso U V.
Proof.
by move=> eqUV; exists 1%:M; rewrite ?unitmx1 ?scalar_mx_hom ?mulmx1.
Qed.

Lemma mx_iso_refl U : mx_iso U U.
Proof. exact: eqmx_iso. Qed.

Lemma mx_iso_sym U V : mx_iso U V -> mx_iso V U.
Proof.
case=> f injf homUf defV; exists (invmx f); first by rewrite unitmx_inv.
  by rewrite dom_hom_invmx // -defV submxMr.
by rewrite -[U](mulmxK injf); apply: eqmxMr (eqmx_sym _).
Qed.

Lemma mx_iso_trans U V W : mx_iso U V -> mx_iso V W -> mx_iso U W.
Proof.
case=> f injf homUf defV [g injg homVg defW].
exists (f *m g); first by rewrite unitmx_mul injf.
  by apply/hom_mxP=> x Gx; rewrite !mulmxA 2?(hom_mxP _) ?defV.
by rewrite mulmxA; apply: eqmx_trans (eqmxMr g defV) defW.
Qed.

Lemma mxrank_iso U V : mx_iso U V -> \rank U = \rank V.
Proof. by case=> f injf _ <-; rewrite mxrankMfree ?row_free_unit. Qed.

Lemma mx_iso_module U V : mx_iso U V -> mxmodule U -> mxmodule V.
Proof.
by case=> f _ homUf defV; rewrite -(eqmx_module defV); apply: hom_mxmodule.
Qed.

(* Simple modules (we reserve the term "irreducible" for representations).    *)

Definition mxsimple (V : 'M_n) :=
  [/\ mxmodule V, V != 0 &
      forall U : 'M_n, mxmodule U -> (U <= V)%MS -> U != 0 -> (V <= U)%MS].

Definition mxnonsimple (U : 'M_n) :=
  exists V : 'M_n, [&& mxmodule V, (V <= U)%MS, V != 0 & \rank V < \rank U].

Lemma mxsimpleP U :
  [/\ mxmodule U, U != 0 & ~ mxnonsimple U] <-> mxsimple U.
Proof.
do [split => [] [modU nzU simU]; split] => // [V modV sVU nzV | [V]].
  apply/idPn; rewrite -(ltn_leqif (mxrank_leqif_sup sVU)) => ltVU.
  by case: simU; exists V; apply/and4P.
by case/and4P=> modV sVU nzV; apply/negP; rewrite -leqNgt mxrankS ?simU.
Qed.

Lemma mxsimple_module U : mxsimple U -> mxmodule U.
Proof. by case. Qed.

Lemma mxsimple_exists m (U : 'M_(m, n)) :
  mxmodule U -> U != 0 -> classically (exists2 V, mxsimple V & V <= U)%MS.
Proof.
move=> modU nzU [] // simU; move: {2}_.+1 (ltnSn (\rank U)) => r leUr.
elim: r => // r IHr in m U leUr modU nzU simU.
have genU := genmxE U; apply simU; exists <<U>>%MS; last by rewrite genU.
apply/mxsimpleP; split; rewrite ?(eqmx_eq0 genU) ?(eqmx_module genU) //.
case=> V; rewrite !genU=> /and4P[modV sVU nzV ltVU]; case: notF.
apply: IHr nzV _ => // [|[W simW sWV]]; first exact: leq_trans ltVU _.
by apply: simU; exists W => //; apply: submx_trans sWV sVU.
Qed.

Lemma mx_iso_simple U V : mx_iso U V -> mxsimple U -> mxsimple V.
Proof.
move=> isoUV [modU nzU simU]; have [f injf homUf defV] := isoUV.
split=> [||W modW sWV nzW]; first by rewrite (mx_iso_module isoUV).
  by rewrite -(eqmx_eq0 defV) -(mul0mx n f) (can_eq (mulmxK injf)).
rewrite -defV -[W](mulmxKV injf) submxMr //; set W' := W *m _.
have sW'U: (W' <= U)%MS by rewrite -[U](mulmxK injf) submxMr ?defV.
rewrite (simU W') //; last by rewrite -(can_eq (mulmxK injf)) mul0mx mulmxKV.
rewrite hom_mxmodule ?dom_hom_invmx // -[W](mulmxKV injf) submxMr //.
exact: submx_trans sW'U homUf.
Qed.

Lemma mxsimple_cyclic u U :
  mxsimple U -> u != 0 -> (u <= U)%MS -> (U :=: cyclic_mx u)%MS.
Proof.
case=> [modU _ simU] nz_u Uu; apply/eqmxP; set uG := cyclic_mx u.
have s_uG_U: (uG <= U)%MS by rewrite cyclic_mx_sub.
by rewrite simU ?cyclic_mx_eq0 ?submx_refl // cyclic_mx_module.
Qed.

(* The surjective part of Schur's lemma. *)
Lemma mx_Schur_onto m (U : 'M_(m, n)) V f :
    mxmodule U -> mxsimple V -> (U <= dom_hom_mx f)%MS ->
  (U *m f <= V)%MS -> U *m f != 0 -> (U *m f :=: V)%MS.
Proof.
move=> modU [modV _ simV] homUf sUfV nzUf.
apply/eqmxP; rewrite sUfV -(genmxE (U *m f)).
rewrite simV ?(eqmx_eq0 (genmxE _)) ?genmxE //.
by rewrite (eqmx_module (genmxE _)) hom_mxmodule.
Qed.

(* The injective part of Schur's lemma. *)
Lemma mx_Schur_inj U f :
  mxsimple U -> (U <= dom_hom_mx f)%MS -> U *m f != 0 -> (U :&: kermx f)%MS = 0.
Proof.
case=> [modU _ simU] homUf nzUf; apply/eqP; apply: contraR nzUf => nz_ker.
rewrite (sameP eqP sub_kermxP) (sameP capmx_idPl eqmxP) simU ?capmxSl //.
exact: kermx_hom_module.
Qed.

(* The injectve part of Schur's lemma, stated as isomorphism with the image. *)
Lemma mx_Schur_inj_iso U f :
  mxsimple U -> (U <= dom_hom_mx f)%MS -> U *m f != 0 -> mx_iso U (U *m f).
Proof.
move=> simU homUf nzUf; have [modU _ _] := simU.
have eqUfU: \rank (U *m f) = \rank U by apply/mxrank_injP; rewrite mx_Schur_inj.
have{eqUfU} [g invg defUf] := complete_unitmx eqUfU.
suffices homUg: (U <= dom_hom_mx g)%MS by exists g; rewrite ?defUf.
apply/hom_mxP=> x Gx; have [ux defUx] := submxP (mxmoduleP modU x Gx).
by rewrite -defUf -(hom_mxP homUf) // defUx -!(mulmxA ux) defUf.
Qed.

(* The isomorphism part of Schur's lemma. *)
Lemma mx_Schur_iso U V f :
    mxsimple U -> mxsimple V -> (U <= dom_hom_mx f)%MS ->
  (U *m f <= V)%MS -> U *m f != 0 -> mx_iso U V.
Proof.
move=> simU simV homUf sUfV nzUf; have [modU _ _] := simU.
have [g invg homUg defUg] := mx_Schur_inj_iso simU homUf nzUf.
exists g => //; apply: mx_Schur_onto; rewrite ?defUg //.
by rewrite -!submx0 defUg in nzUf *.
Qed.

(* A boolean test for module isomorphism that is only valid for simple        *)
(* modules; this is the only case that matters in practice.                   *)

Lemma nz_row_mxsimple U : mxsimple U -> nz_row U != 0.
Proof. by case=> _ nzU _; rewrite nz_row_eq0. Qed.

Definition mxsimple_iso (U V : 'M_n) :=
  [&& mxmodule V, (V :&: row_hom_mx (nz_row U))%MS != 0 & \rank V <= \rank U].

Lemma mxsimple_isoP U V :
  mxsimple U -> reflect (mx_iso U V) (mxsimple_iso U V).
Proof.
move=> simU; pose u := nz_row U.
have [Uu nz_u]: (u <= U)%MS /\ u != 0 by rewrite nz_row_sub nz_row_mxsimple.
apply: (iffP and3P) => [[modV] | isoUV]; last first.
  split; last by rewrite (mxrank_iso isoUV).
    by case: (mx_iso_simple isoUV simU).
  have [f injf homUf defV] := isoUV; apply/rowV0Pn; exists (u *m f).
    rewrite sub_capmx -defV submxMr //.
    by apply/row_hom_mxP; exists f; first apply: (submx_trans Uu).
  by rewrite -(mul0mx _ f) (can_eq (mulmxK injf)) nz_u.
case/rowV0Pn=> v; rewrite sub_capmx => /andP[Vv].
case/row_hom_mxP => f homMf def_v nz_v eqrUV.
pose uG := cyclic_mx u; pose vG := cyclic_mx v.
have def_vG: (uG *m f :=: vG)%MS by rewrite /vG -def_v; apply: hom_cyclic_mx.
have defU: (U :=: uG)%MS by apply: mxsimple_cyclic.
have mod_uG: mxmodule uG by rewrite cyclic_mx_module.
have homUf: (U <= dom_hom_mx f)%MS.
  by rewrite defU cyclic_mx_sub ?dom_hom_mx_module.
have isoUf: mx_iso U (U *m f).
  apply: mx_Schur_inj_iso => //; apply: contra nz_v; rewrite -!submx0.
  by rewrite (eqmxMr f defU) def_vG; apply: submx_trans (cyclic_mx_id v).
apply: mx_iso_trans (isoUf) (eqmx_iso _); apply/eqmxP.
have sUfV: (U *m f <= V)%MS by rewrite (eqmxMr f defU) def_vG cyclic_mx_sub.
by rewrite -mxrank_leqif_eq ?eqn_leq 1?mxrankS // -(mxrank_iso isoUf).
Qed.

Lemma mxsimple_iso_simple U V :
  mxsimple_iso U V -> mxsimple U -> mxsimple V.
Proof.
by move=> isoUV simU; apply: mx_iso_simple (simU); apply/mxsimple_isoP.
Qed.

(* For us, "semisimple" means "sum of simple modules"; this is classically,   *)
(* but not intuitionistically, equivalent to the "completely reducible"       *)
(* alternate characterization.                                                *)

Implicit Type I : finType.

Variant mxsemisimple (V : 'M_n) :=
  MxSemisimple I U (W := (\sum_(i : I) U i)%MS) of
    forall i, mxsimple (U i) & (W :=: V)%MS & mxdirect W.

(* This is a slight generalization of Aschbacher 12.5 for finite sets. *)
Lemma sum_mxsimple_direct_compl m I W (U : 'M_(m, n)) :
    let V := (\sum_(i : I) W i)%MS in
    (forall i : I, mxsimple (W i)) -> mxmodule U -> (U <= V)%MS -> 
  {J : {set I} | let S := U + \sum_(i in J) W i in S :=: V /\ mxdirect S}%MS.
Proof.
move=> V simW modU sUV; pose V_ (J : {set I}) := (\sum_(i in J) W i)%MS.
pose dxU (J : {set I}) := mxdirect (U + V_ J).
have [J maxJ]: {J | maxset dxU J}; last case/maxsetP: maxJ => dxUVJ maxJ.
  apply: ex_maxset; exists set0.
  by rewrite /dxU mxdirectE /V_ /= !big_set0 addn0 addsmx0 /=.
have modWJ: mxmodule (V_ J) by apply: sumsmx_module => i _; case: (simW i).
exists J; split=> //; apply/eqmxP; rewrite addsmx_sub sUV; apply/andP; split.
  by apply/sumsmx_subP=> i Ji; rewrite (sumsmx_sup i).
rewrite -/(V_ J); apply/sumsmx_subP=> i _.
case Ji: (i \in J).
  by apply: submx_trans (addsmxSr _ _); apply: (sumsmx_sup i).
have [modWi nzWi simWi] := simW i.
rewrite (sameP capmx_idPl eqmxP) simWi ?capmxSl ?capmx_module ?addsmx_module //.
apply: contraFT (Ji); rewrite negbK => dxWiUVJ.
rewrite -(maxJ (i |: J)) ?setU11 ?subsetUr // /dxU.
rewrite mxdirectE /= !big_setU1 ?Ji //=.
rewrite addnCA addsmxA (addsmxC U) -addsmxA -mxdirectE /=.
by rewrite mxdirect_addsE /= mxdirect_trivial -/(dxU _) dxUVJ.
Qed.

Lemma sum_mxsimple_direct_sub I W (V : 'M_n) :
    (forall i : I, mxsimple (W i)) -> (\sum_i W i :=: V)%MS ->
  {J : {set I} | let S := \sum_(i in J) W i in S :=: V /\ mxdirect S}%MS.
Proof.
move=> simW defV.
have [|J [defS dxS]] := sum_mxsimple_direct_compl simW (mxmodule0 n).
  exact: sub0mx.
exists J; split; last by rewrite mxdirectE /= adds0mx mxrank0 in dxS.
by apply: eqmx_trans defV; rewrite adds0mx_id in defS.
Qed.

Lemma mxsemisimple0 : mxsemisimple 0.
Proof.
exists [finType of 'I_0] (fun _ => 0); [by case | by rewrite big_ord0 | ].
by rewrite mxdirectE /= !big_ord0 mxrank0.
Qed.

Lemma intro_mxsemisimple (I : Type) r (P : pred I) W V :
    (\sum_(i <- r | P i) W i :=: V)%MS ->
    (forall i, P i -> W i != 0 -> mxsimple (W i)) ->
  mxsemisimple V.
Proof.
move=> defV simW; pose W_0 := [pred i | W i == 0].
have [-> | nzV] := eqVneq V 0; first exact: mxsemisimple0.
case def_r: r => [| i0 r'] => [|{r' def_r}].
  by rewrite -mxrank_eq0 -defV def_r big_nil mxrank0 in nzV.
move: defV; rewrite (bigID W_0) /= addsmxC -big_filter !(big_nth i0) !big_mkord.
rewrite addsmxC big1 ?adds0mx_id => [|i /andP[_ /eqP] //].
set tI := 'I_(_); set r_ := nth _ _ => defV.
have{simW} simWr (i : tI) : mxsimple (W (r_ i)).
  case: i => m /=; set Pr := fun i => _ => lt_m_r /=.
  suffices: (Pr (r_ m)) by case/andP; apply: simW.
  apply: all_nthP m lt_m_r; apply/all_filterP.
  by rewrite -filter_predI; apply: eq_filter => i; rewrite /= andbb.
have [J []] := sum_mxsimple_direct_sub simWr defV.
case: (set_0Vmem J) => [-> V0 | [j0 Jj0]].
  by rewrite -mxrank_eq0 -V0 big_set0 mxrank0 in nzV.
pose K := {j | j \in J}; pose k0 : K := Sub j0 Jj0.
have bij_KJ: {on J, bijective (sval : K -> _)}.
  by exists (insubd k0) => [k _ | j Jj]; rewrite ?valKd ?insubdK.
have J_K (k : K) : sval k \in J by apply: valP k.
rewrite mxdirectE /= !(reindex _ bij_KJ) !(eq_bigl _ _ J_K) -mxdirectE /= -/tI.
exact: MxSemisimple.
Qed.

Lemma mxsimple_semisimple U : mxsimple U -> mxsemisimple U.
Proof.
move=> simU; apply: (intro_mxsemisimple (_ : \sum_(i < 1) U :=: U))%MS => //.
by rewrite big_ord1.
Qed.

Lemma addsmx_semisimple U V :
  mxsemisimple U -> mxsemisimple V -> mxsemisimple (U + V)%MS.
Proof.
case=> [I W /= simW defU _] [J T /= simT defV _].
have defUV: (\sum_ij sum_rect (fun _ => 'M_n) W T ij :=: U + V)%MS.
  by rewrite big_sumType /=; apply: adds_eqmx.
by apply: intro_mxsemisimple defUV _; case=> /=.
Qed.

Lemma sumsmx_semisimple (I : finType) (P : pred I) V :
  (forall i, P i -> mxsemisimple (V i)) -> mxsemisimple (\sum_(i | P i) V i)%MS.
Proof.
move=> ssimV; elim/big_ind: _ => //; first exact: mxsemisimple0.
exact: addsmx_semisimple.
Qed.

Lemma eqmx_semisimple U V : (U :=: V)%MS -> mxsemisimple U -> mxsemisimple V.
Proof.
by move=> eqUV [I W S simW defU dxS]; exists I W => //; apply: eqmx_trans eqUV.
Qed.

Lemma hom_mxsemisimple (V f : 'M_n) :
  mxsemisimple V -> (V <= dom_hom_mx f)%MS -> mxsemisimple (V *m f).
Proof.
case=> I W /= simW defV _; rewrite -defV => /sumsmx_subP homWf.
have{defV} defVf: (\sum_i W i *m f :=: V *m f)%MS.
  by apply: eqmx_trans (eqmx_sym _) (eqmxMr f defV); apply: sumsmxMr.
apply: (intro_mxsemisimple defVf) => i _ nzWf.
by apply: mx_iso_simple (simW i); apply: mx_Schur_inj_iso; rewrite ?homWf.
Qed.

Lemma mxsemisimple_module U : mxsemisimple U -> mxmodule U.
Proof.
case=> I W /= simW defU _.
by rewrite -(eqmx_module defU) sumsmx_module // => i _; case: (simW i).
Qed.

(* Completely reducible modules, and Maeschke's Theorem. *)

Variant mxsplits (V U : 'M_n) :=
  MxSplits (W : 'M_n) of mxmodule W & (U + W :=: V)%MS & mxdirect (U + W).

Definition mx_completely_reducible V :=
  forall U, mxmodule U -> (U <= V)%MS -> mxsplits V U.

Lemma mx_reducibleS U V :
    mxmodule U -> (U <= V)%MS ->
  mx_completely_reducible V -> mx_completely_reducible U.
Proof.
move=> modU sUV redV U1 modU1 sU1U.
have [W modW defV dxU1W] := redV U1 modU1 (submx_trans sU1U sUV).
exists (W :&: U)%MS; first exact: capmx_module.
  by apply/eqmxP; rewrite !matrix_modl // capmxSr sub_capmx defV sUV /=.
by apply/mxdirect_addsP; rewrite capmxA (mxdirect_addsP dxU1W) cap0mx.
Qed.

Lemma mx_Maschke : [char F]^'.-group G -> mx_completely_reducible 1%:M.
Proof.
rewrite /pgroup charf'_nat; set nG := _%:R => nzG U => /mxmoduleP Umod _.
pose phi := nG^-1 *: (\sum_(x in G) rG x^-1 *m pinvmx U *m U *m rG x).
have phiG x: x \in G -> phi *m rG x = rG x *m phi.
  move=> Gx; rewrite -scalemxAl -scalemxAr; congr (_ *: _).
  rewrite {2}(reindex_acts 'R _ Gx) ?astabsR //= mulmx_suml mulmx_sumr.
  apply: eq_bigr => y Gy; rewrite !mulmxA -repr_mxM ?groupV ?groupM //.
  by rewrite invMg mulKVg repr_mxM ?mulmxA.
have Uphi: U *m phi = U.
  rewrite -scalemxAr mulmx_sumr (eq_bigr (fun _ => U)) => [|x Gx].
    by rewrite sumr_const -scaler_nat !scalerA  mulVf ?scale1r.
  by rewrite 3!mulmxA mulmxKpV ?repr_mxKV ?Umod ?groupV.
have tiUker: (U :&: kermx phi = 0)%MS.
  apply/eqP/rowV0P=> v; rewrite sub_capmx => /andP[/submxP[u ->] /sub_kermxP].
  by rewrite -mulmxA Uphi.
exists (kermx phi); last exact/mxdirect_addsP.
  apply/mxmoduleP=> x Gx; apply/sub_kermxP.
  by rewrite -mulmxA -phiG // mulmxA mulmx_ker mul0mx.
apply/eqmxP; rewrite submx1 sub1mx.
rewrite /row_full mxrank_disjoint_sum //= mxrank_ker.
suffices ->: (U :=: phi)%MS by rewrite subnKC ?rank_leq_row.
apply/eqmxP; rewrite -{1}Uphi submxMl scalemx_sub //.
by rewrite summx_sub // => x Gx; rewrite -mulmxA mulmx_sub ?Umod.
Qed.

Lemma mxsemisimple_reducible V : mxsemisimple V -> mx_completely_reducible V.
Proof.
case=> [I W /= simW defV _] U modU sUV; rewrite -defV in sUV.
have [J [defV' dxV]] := sum_mxsimple_direct_compl simW modU sUV.
exists (\sum_(i in J) W i)%MS.
- by apply: sumsmx_module => i _; case: (simW i).
- exact: eqmx_trans defV' defV.
by rewrite mxdirect_addsE (sameP eqP mxdirect_addsP) /= in dxV; case/and3P: dxV.
Qed.

Lemma mx_reducible_semisimple V :
  mxmodule V -> mx_completely_reducible V -> classically (mxsemisimple V).
Proof.
move=> modV redV [] // nssimV; move: {-1}_.+1 (ltnSn (\rank V)) => r leVr.
elim: r => // r IHr in V leVr modV redV nssimV.
have [V0 | nzV] := eqVneq V 0.
  by rewrite nssimV ?V0 //; apply: mxsemisimple0.
apply (mxsimple_exists modV nzV) => [[U simU sUV]]; have [modU nzU _] := simU.
have [W modW defUW dxUW] := redV U modU sUV.
have sWV: (W <= V)%MS by rewrite -defUW addsmxSr.
apply: IHr (mx_reducibleS modW sWV redV) _ => // [|ssimW].
  rewrite ltnS -defUW (mxdirectP dxUW) /= in leVr; apply: leq_trans leVr.
  by rewrite -add1n leq_add2r lt0n mxrank_eq0.
apply: nssimV (eqmx_semisimple defUW (addsmx_semisimple _ ssimW)).
exact: mxsimple_semisimple.
Qed.

Lemma mxsemisimpleS U V :
  mxmodule U -> (U <= V)%MS -> mxsemisimple V -> mxsemisimple U.
Proof.
move=> modU sUV ssimV.
have [W modW defUW dxUW]:= mxsemisimple_reducible ssimV modU sUV.
move/mxdirect_addsP: dxUW => dxUW.
have defU : (V *m proj_mx U W :=: U)%MS.
  by apply/eqmxP; rewrite proj_mx_sub -{1}[U](proj_mx_id dxUW) ?submxMr.
apply: eqmx_semisimple defU _; apply: hom_mxsemisimple ssimV _.
by rewrite -defUW proj_mx_hom.
Qed.

Lemma hom_mxsemisimple_iso I P U W f :
  let V := (\sum_(i : I |  P i) W i)%MS in
  mxsimple U -> (forall i, P i -> W i != 0 -> mxsimple (W i)) -> 
  (V <= dom_hom_mx f)%MS -> (U <= V *m f)%MS ->
  {i | P i & mx_iso (W i) U}.
Proof.
move=> V simU simW homVf sUVf; have [modU nzU _] := simU.
have ssimVf: mxsemisimple (V *m f).
  exact: hom_mxsemisimple (intro_mxsemisimple (eqmx_refl V) simW) homVf.
have [U' modU' defVf] := mxsemisimple_reducible ssimVf modU sUVf.
move/mxdirect_addsP=> dxUU'; pose p := f *m proj_mx U U'.
case: (pickP (fun i => P i && (W i *m p != 0))) => [i /andP[Pi nzWip] | no_i].
  have sWiV: (W i <= V)%MS by rewrite (sumsmx_sup i).
  have sWipU: (W i *m p <= U)%MS by rewrite mulmxA proj_mx_sub.
  exists i => //; apply: (mx_Schur_iso (simW i Pi _) simU _ sWipU nzWip).
    by apply: contraNneq nzWip => ->; rewrite mul0mx.
  apply: (submx_trans sWiV); apply/hom_mxP=> x Gx.
  by rewrite mulmxA [_ *m p]mulmxA 2?(hom_mxP _) -?defVf ?proj_mx_hom.
case/negP: nzU; rewrite -submx0 -[U](proj_mx_id dxUU') //.
rewrite (submx_trans (submxMr _ sUVf)) // -mulmxA -/p sumsmxMr.
by apply/sumsmx_subP=> i Pi; move/negbT: (no_i i); rewrite Pi negbK submx0.
Qed.

(* The component associated to a given irreducible module.                    *)

Section Components.

Fact component_mx_key : unit. Proof. by []. Qed.
Definition component_mx_expr (U : 'M[F]_n) :=
  (\sum_i cyclic_mx (row i (row_hom_mx (nz_row U))))%MS.
Definition component_mx := locked_with component_mx_key component_mx_expr.
Canonical component_mx_unfoldable := [unlockable fun component_mx].

Variable U : 'M[F]_n.
Hypothesis simU : mxsimple U.

Let u := nz_row U.
Let iso_u := row_hom_mx u.
Let nz_u : u != 0 := nz_row_mxsimple simU.
Let Uu : (u <= U)%MS := nz_row_sub U.
Let defU : (U :=: cyclic_mx u)%MS := mxsimple_cyclic simU nz_u Uu.
Local Notation compU := (component_mx U).

Lemma component_mx_module : mxmodule compU.
Proof.
by rewrite unlock sumsmx_module // => i; rewrite cyclic_mx_module.
Qed.

Lemma genmx_component : <<compU>>%MS = compU.
Proof.
by rewrite [in compU]unlock genmx_sums; apply: eq_bigr => i; rewrite genmx_id.
Qed.

Lemma component_mx_def : {I : finType & {W : I -> 'M_n |
  forall i, mx_iso U (W i) & compU = \sum_i W i}}%MS.
Proof.
pose r i := row i iso_u; pose r_nz i := r i != 0; pose I := {i | r_nz i}.
exists [finType of I]; exists (fun i => cyclic_mx (r (sval i))) => [i|].
  apply/mxsimple_isoP=> //; apply/and3P.
  split; first by rewrite cyclic_mx_module.
    apply/rowV0Pn; exists (r (sval i)); last exact: (svalP i).
    by rewrite sub_capmx cyclic_mx_id row_sub.
  have [f hom_u_f <-] := @row_hom_mxP u (r (sval i)) (row_sub _ _).
  by rewrite defU -hom_cyclic_mx ?mxrankM_maxl.
rewrite -(eq_bigr _ (fun _ _ => genmx_id _)) -genmx_sums -genmx_component.
rewrite [in compU]unlock; apply/genmxP/andP; split; last first.
  by apply/sumsmx_subP => i _; rewrite (sumsmx_sup (sval i)).
apply/sumsmx_subP => i _.
case i0: (r_nz i); first by rewrite (sumsmx_sup (Sub i i0)).
by move/negbFE: i0; rewrite -cyclic_mx_eq0 => /eqP->; apply: sub0mx.
Qed.

Lemma component_mx_semisimple : mxsemisimple compU.
Proof.
have [I [W isoUW ->]] := component_mx_def.
apply: intro_mxsemisimple (eqmx_refl _) _ => i _ _.
exact: mx_iso_simple (isoUW i) simU.
Qed.

Lemma mx_iso_component V : mx_iso U V -> (V <= compU)%MS.
Proof.
move=> isoUV; have [f injf homUf defV] := isoUV.
have simV := mx_iso_simple isoUV simU.
have hom_u_f := submx_trans Uu homUf.
have ->: (V :=: cyclic_mx (u *m f))%MS.
  apply: eqmx_trans (hom_cyclic_mx hom_u_f).
  exact: eqmx_trans (eqmx_sym defV) (eqmxMr _ defU).
have iso_uf: (u *m f <= iso_u)%MS by apply/row_hom_mxP; exists f.
rewrite genmxE; apply/row_subP=> j; rewrite row_mul mul_rV_lin1 /=.
set a := vec_mx _; apply: submx_trans (submxMr _ iso_uf) _.
apply/row_subP=> i; rewrite row_mul [in compU]unlock (sumsmx_sup i) //.
by apply/cyclic_mxP; exists a; rewrite // vec_mxK row_sub.
Qed.

Lemma component_mx_id : (U <= compU)%MS.
Proof. exact: mx_iso_component (mx_iso_refl U). Qed.

Lemma hom_component_mx_iso f V :
    mxsimple V -> (compU <= dom_hom_mx f)%MS -> (V <= compU *m f)%MS ->
  mx_iso U V.
Proof.
have [I [W isoUW ->]] := component_mx_def => simV homWf sVWf.
have [i _ _|i _ ] := hom_mxsemisimple_iso simV _ homWf sVWf.
  exact: mx_iso_simple (simU).
exact: mx_iso_trans.
Qed.

Lemma component_mx_iso V : mxsimple V -> (V <= compU)%MS -> mx_iso U V.
Proof.
move=> simV; rewrite -[compU]mulmx1.
exact: hom_component_mx_iso (scalar_mx_hom _ _).
Qed.

Lemma hom_component_mx f :
  (compU <= dom_hom_mx f)%MS -> (compU *m f <= compU)%MS.
Proof.
move=> hom_f.
have [I W /= simW defW _] := hom_mxsemisimple component_mx_semisimple hom_f.
rewrite -defW; apply/sumsmx_subP=> i _; apply: mx_iso_component.
by apply: hom_component_mx_iso hom_f _ => //; rewrite -defW (sumsmx_sup i).
Qed.

End Components.

Lemma component_mx_isoP U V :
    mxsimple U -> mxsimple V ->
  reflect (mx_iso U V) (component_mx U == component_mx V).
Proof.
move=> simU simV; apply: (iffP eqP) => isoUV.
  by apply: component_mx_iso; rewrite ?isoUV ?component_mx_id.
rewrite -(genmx_component U) -(genmx_component V); apply/genmxP.
wlog suffices: U V simU simV isoUV / (component_mx U <= component_mx V)%MS.
  by move=> IH; rewrite !IH //; apply: mx_iso_sym.
have [I [W isoWU ->]] := component_mx_def simU.
apply/sumsmx_subP => i _; apply: mx_iso_component => //.
exact: mx_iso_trans (mx_iso_sym isoUV) (isoWU i).
Qed.

Lemma component_mx_disjoint U V :
    mxsimple U -> mxsimple V -> component_mx U != component_mx V ->
  (component_mx U :&: component_mx V = 0)%MS.
Proof.
move=> simU simV neUV; apply: contraNeq neUV => ntUV.
apply: (mxsimple_exists _ ntUV) => [|[W simW]].
  by rewrite capmx_module ?component_mx_module.
rewrite sub_capmx => /andP[sWU sWV]; apply/component_mx_isoP=> //.
by apply: mx_iso_trans (_ : mx_iso U W) (mx_iso_sym _); apply: component_mx_iso.
Qed.

Section Socle.

Record socleType := EnumSocle {
  socle_base_enum : seq 'M[F]_n;
  _ : forall M, M \in socle_base_enum -> mxsimple M;
  _ : forall M, mxsimple M -> has (mxsimple_iso M) socle_base_enum
}.

Lemma socle_exists : classically socleType.
Proof.
pose V : 'M[F]_n := 0; have: mxsemisimple V by apply: mxsemisimple0.
have: n - \rank V < n.+1 by rewrite mxrank0 subn0.
elim: _.+1 V => // n' IHn' V; rewrite ltnS => le_nV_n' ssimV.
case=> // maxV; apply: (maxV); have [I /= U simU defV _] := ssimV.
exists (codom U) => [M | M simM]; first by case/mapP=> i _ ->.
suffices sMV: (M <= V)%MS.
  rewrite -defV -(mulmx1 (\sum_i _)%MS) in sMV.
  have [//| i _] := hom_mxsemisimple_iso simM _ (scalar_mx_hom _ _) sMV.
  move/mx_iso_sym=> isoM; apply/hasP.
  by exists (U i); [apply: codom_f | apply/mxsimple_isoP].
have ssimMV := addsmx_semisimple (mxsimple_semisimple simM) ssimV.
apply: contraLR isT => nsMV; apply: IHn' ssimMV _ maxV.
apply: leq_trans le_nV_n'; rewrite ltn_sub2l //.
  rewrite ltn_neqAle rank_leq_row andbT -[_ == _]sub1mx.
  by apply: contra nsMV; apply: submx_trans; apply: submx1.
rewrite (ltn_leqif (mxrank_leqif_sup _)) ?addsmxSr //.
by rewrite addsmx_sub submx_refl andbT.
Qed.

Section SocleDef.

Variable sG0 : socleType.

Definition socle_enum := map component_mx (socle_base_enum sG0).

Lemma component_socle M : mxsimple M -> component_mx M \in socle_enum.
Proof.
rewrite /socle_enum; case: sG0 => e0 /= sim_e mem_e simM.
have /hasP[M' e0M' isoMM'] := mem_e M simM; apply/mapP; exists M' => //.
by apply/eqP/component_mx_isoP; [|apply: sim_e | apply/mxsimple_isoP].
Qed.

Inductive socle_sort : predArgType := PackSocle W of W \in socle_enum.

Local Notation sG := socle_sort.
Local Notation e0 := (socle_base_enum sG0).

Definition socle_base W := let: PackSocle W _ := W in e0`_(index W socle_enum).

Coercion socle_val W : 'M[F]_n := component_mx (socle_base W).

Definition socle_mult (W : sG) := (\rank W %/ \rank (socle_base W))%N.

Lemma socle_simple W : mxsimple (socle_base W).
Proof.
case: W => M /=; rewrite /= /socle_enum /=; case: sG0 => e sim_e _ /= e_M.
by apply: sim_e; rewrite mem_nth // -(size_map component_mx) index_mem.
Qed.

Definition socle_module (W : sG) := mxsimple_module (socle_simple W).

Definition socle_repr W := submod_repr (socle_module W).

Lemma nz_socle (W : sG) : W != 0 :> 'M_n.
Proof.
have simW := socle_simple W; have [_ nzW _] := simW; apply: contra nzW.
by rewrite -!submx0; apply: submx_trans (component_mx_id simW).
Qed.

Lemma socle_mem (W : sG) : (W : 'M_n) \in socle_enum.
Proof. exact: component_socle (socle_simple _). Qed.

Lemma PackSocleK W e0W : @PackSocle W e0W = W :> 'M_n.
Proof.
rewrite /socle_val /= in e0W *; rewrite -(nth_map _ 0) ?nth_index //.
by rewrite -(size_map component_mx) index_mem.
Qed.

Canonical socle_subType := SubType _ _ _ socle_sort_rect PackSocleK.
Definition socle_eqMixin := Eval hnf in [eqMixin of sG by <:].
Canonical socle_eqType := Eval hnf in EqType sG socle_eqMixin.
Definition socle_choiceMixin := Eval hnf in [choiceMixin of sG by <:].
Canonical socle_choiceType := ChoiceType sG socle_choiceMixin.

Lemma socleP (W W' : sG) : reflect (W = W') (W == W')%MS.
Proof. by rewrite (sameP genmxP eqP) !{1}genmx_component; apply: (W =P _). Qed.

Fact socle_finType_subproof :
  cancel (fun W => SeqSub (socle_mem W)) (fun s => PackSocle (valP s)).
Proof. by move=> W /=; apply: val_inj; rewrite /= PackSocleK. Qed.

Definition socle_countMixin := CanCountMixin socle_finType_subproof.
Canonical socle_countType := CountType sG socle_countMixin.
Canonical socle_subCountType := [subCountType of sG].
Definition socle_finMixin := CanFinMixin socle_finType_subproof.
Canonical socle_finType := FinType sG socle_finMixin.
Canonical socle_subFinType := [subFinType of sG].

End SocleDef.

Coercion socle_sort : socleType >-> predArgType.

Variable sG : socleType.

Section SubSocle.

Variable P : pred sG.
Notation S := (\sum_(W : sG | P W) socle_val W)%MS.

Lemma subSocle_module : mxmodule S.
Proof. by rewrite sumsmx_module // => W _; apply: component_mx_module. Qed.

Lemma subSocle_semisimple : mxsemisimple S.
Proof.
apply: sumsmx_semisimple => W _; apply: component_mx_semisimple.
exact: socle_simple.
Qed.
Local Notation ssimS := subSocle_semisimple.

Lemma subSocle_iso M :
  mxsimple M -> (M <= S)%MS -> {W : sG | P W & mx_iso (socle_base W) M}.
Proof.
move=> simM sMS; have [modM nzM _] := simM.
have [V /= modV defMV] := mxsemisimple_reducible ssimS modM sMS.
move/mxdirect_addsP=> dxMV; pose p := proj_mx M V; pose Sp (W : sG) := W *m p.
case: (pickP [pred i | P i & Sp i != 0]) => [/= W | Sp0]; last first.
  case/negP: nzM; rewrite -submx0 -[M](proj_mx_id dxMV) //.
  rewrite (submx_trans (submxMr _ sMS)) // sumsmxMr big1 // => W P_W.
  by apply/eqP; move/negbT: (Sp0 W); rewrite /= P_W negbK.
rewrite {}/Sp /= => /andP[P_W nzSp]; exists W => //.
have homWp: (W <= dom_hom_mx p)%MS.
  apply: submx_trans (proj_mx_hom dxMV modM modV).
  by rewrite defMV (sumsmx_sup W).
have simWP := socle_simple W; apply: hom_component_mx_iso (homWp) _ => //.
by rewrite (mx_Schur_onto _ simM) ?proj_mx_sub ?component_mx_module.
Qed.

Lemma capmx_subSocle m (M : 'M_(m, n)) :
  mxmodule M -> (M :&: S :=: \sum_(W : sG | P W) (M :&: W))%MS.
Proof.
move=> modM; apply/eqmxP/andP; split; last first.
  by apply/sumsmx_subP=> W P_W; rewrite capmxS // (sumsmx_sup W).
have modMS: mxmodule (M :&: S)%MS by rewrite capmx_module ?subSocle_module.
have [J /= U simU defMS _] := mxsemisimpleS modMS (capmxSr M S) ssimS.
rewrite -defMS; apply/sumsmx_subP=> j _.
have [sUjV sUjS]: (U j <= M /\ U j <= S)%MS.
  by apply/andP; rewrite -sub_capmx -defMS (sumsmx_sup j).
have [W P_W isoWU] := subSocle_iso (simU j) sUjS.
rewrite (sumsmx_sup W) // sub_capmx sUjV mx_iso_component //.
exact: socle_simple.
Qed.

End SubSocle.

Lemma subSocle_direct P : mxdirect (\sum_(W : sG | P W) W).
Proof.
apply/mxdirect_sumsP=> W _; apply/eqP.
rewrite -submx0 capmx_subSocle ?component_mx_module //.
apply/sumsmx_subP=> W' /andP[_ neWW'].
by rewrite capmxC component_mx_disjoint //; apply: socle_simple.
Qed.

Definition Socle := (\sum_(W : sG) W)%MS.

Lemma simple_Socle M : mxsimple M -> (M <= Socle)%MS.
Proof.
move=> simM; have socM := component_socle sG simM.
by rewrite (sumsmx_sup (PackSocle socM)) // PackSocleK component_mx_id.
Qed.

Lemma semisimple_Socle U : mxsemisimple U -> (U <= Socle)%MS.
Proof.
by case=> I M /= simM <- _; apply/sumsmx_subP=> i _; apply: simple_Socle.
Qed.

Lemma reducible_Socle U :
  mxmodule U -> mx_completely_reducible U -> (U <= Socle)%MS.
Proof.
move=> modU redU; apply: (mx_reducible_semisimple modU redU).
exact: semisimple_Socle.
Qed.

Lemma genmx_Socle : <<Socle>>%MS = Socle.
Proof. by rewrite genmx_sums; apply: eq_bigr => W; rewrite genmx_component. Qed.

Lemma reducible_Socle1 : mx_completely_reducible 1%:M -> Socle = 1%:M.
Proof.
move=> redG; rewrite -genmx1 -genmx_Socle; apply/genmxP.
by rewrite submx1 reducible_Socle ?mxmodule1.
Qed.

Lemma Socle_module : mxmodule Socle. Proof. exact: subSocle_module. Qed.

Lemma Socle_semisimple : mxsemisimple Socle.
Proof. exact: subSocle_semisimple. Qed.

Lemma Socle_direct : mxdirect Socle. Proof. exact: subSocle_direct. Qed.

Lemma Socle_iso M : mxsimple M -> {W : sG | mx_iso (socle_base W) M}.
Proof.
by move=> simM; case/subSocle_iso: (simple_Socle simM) => // W _; exists W.
Qed.

End Socle.

(* Centralizer subgroup and central homomorphisms. *)
Section CentHom.

Variable f : 'M[F]_n.

Lemma row_full_dom_hom : row_full (dom_hom_mx f) = centgmx rG f.
Proof.
by rewrite -sub1mx; apply/hom_mxP/centgmxP=> cfG x /cfG; rewrite !mul1mx.
Qed.

Lemma memmx_cent_envelop : (f \in 'C(E_G))%MS = centgmx rG f.
Proof.
apply/cent_rowP/centgmxP=> [cfG x Gx | cfG i].
  by have:= cfG (enum_rank_in Gx x); rewrite rowK mxvecK enum_rankK_in.
by rewrite rowK mxvecK /= cfG ?enum_valP.
Qed.

Lemma kermx_centg_module : centgmx rG f -> mxmodule (kermx f).
Proof.
move/centgmxP=> cGf; apply/mxmoduleP=> x Gx; apply/sub_kermxP.
by rewrite -mulmxA -cGf // mulmxA mulmx_ker mul0mx.
Qed.

Lemma centgmx_hom m (U : 'M_(m, n)) : centgmx rG f -> (U <= dom_hom_mx f)%MS.
Proof. by rewrite -row_full_dom_hom -sub1mx; apply: submx_trans (submx1 _). Qed.

End CentHom.

(* (Globally) irreducible, and absolutely irreducible representations. Note   *)
(* that unlike "reducible", "absolutely irreducible" can easily be decided.   *)

Definition mx_irreducible := mxsimple 1%:M.

Lemma mx_irrP :
  mx_irreducible <-> n > 0 /\ (forall U, @mxmodule n U -> U != 0 -> row_full U).
Proof.
rewrite /mx_irreducible /mxsimple mxmodule1 -mxrank_eq0 mxrank1 -lt0n.
do [split=> [[_ -> irrG] | [-> irrG]]; split=> // U] => [modU | modU _] nzU.
  by rewrite -sub1mx (irrG U) ?submx1.
by rewrite sub1mx irrG.
Qed.

(* Schur's lemma for endomorphisms. *)
Lemma mx_Schur :
  mx_irreducible -> forall f, centgmx rG f -> f != 0 -> f \in unitmx.
Proof.
move/mx_Schur_onto=> irrG f.
rewrite -row_full_dom_hom -!row_full_unit -!sub1mx => cGf nz.
by rewrite -[f]mul1mx irrG ?submx1 ?mxmodule1 ?mul1mx.
Qed.

Definition mx_absolutely_irreducible := (n > 0) && row_full E_G.

Lemma mx_abs_irrP :
  reflect (n > 0 /\ exists a_, forall A, A = \sum_(x in G) a_ x A *: rG x)
          mx_absolutely_irreducible.
Proof.
have G_1 := group1 G; have bijG := enum_val_bij_in G_1.
set h := enum_val in bijG; have Gh : h _ \in G by apply: enum_valP.
rewrite /mx_absolutely_irreducible; case: (n > 0); last by right; case.
apply: (iffP row_fullP) => [[E' E'G] | [_ [a_ a_G]]].
  split=> //; exists (fun x B => (mxvec B *m E') 0 (enum_rank_in G_1 x)) => B.
  apply: (can_inj mxvecK); rewrite -{1}[mxvec B]mulmx1 -{}E'G mulmxA.
  move: {B E'}(_ *m E') => u; apply/rowP=> j.
  rewrite linear_sum (reindex h) //= mxE summxE.
  by apply: eq_big => [k| k _]; rewrite ?Gh // enum_valK_in mxE linearZ !mxE.
exists (\matrix_(j, i) a_ (h i) (vec_mx (row j 1%:M))).
apply/row_matrixP=> i; rewrite -[row i 1%:M]vec_mxK {}[vec_mx _]a_G.
apply/rowP=> j; rewrite linear_sum (reindex h) //= 2!mxE summxE.
by apply: eq_big => [k| k _]; [rewrite Gh | rewrite linearZ !mxE].
Qed.

Lemma mx_abs_irr_cent_scalar :
  mx_absolutely_irreducible -> forall A, centgmx rG A -> is_scalar_mx A.
Proof.
case/mx_abs_irrP=> n_gt0 [a_ a_G] A /centgmxP cGA.
have{cGA a_G} cMA B: A *m B = B *m A.
  rewrite {}[B]a_G mulmx_suml mulmx_sumr.
  by apply: eq_bigr => x Gx; rewrite -scalemxAl -scalemxAr cGA.
pose i0 := Ordinal n_gt0; apply/is_scalar_mxP; exists (A i0 i0).
apply/matrixP=> i j; move/matrixP/(_ i0 j): (esym (cMA (delta_mx i0 i))).
rewrite -[A *m _]trmxK trmx_mul trmx_delta -!(@mul_delta_mx _ n 1 n 0) -!mulmxA.
by rewrite -!rowE !mxE !big_ord1 !mxE !eqxx !mulr_natl /= andbT eq_sym.
Qed.

Lemma mx_abs_irrW : mx_absolutely_irreducible -> mx_irreducible.
Proof.
case/mx_abs_irrP=> n_gt0 [a_ a_G]; apply/mx_irrP; split=> // U Umod.
case/rowV0Pn=> u Uu; rewrite -mxrank_eq0 -lt0n row_leq_rank -sub1mx.
case/submxP: Uu => v ->{u} /row_freeP[u' vK]; apply/row_subP=> i.
rewrite rowE scalar_mxC -{}vK -2![_ *m _]mulmxA; move: {u' i}(u' *m _) => A.
rewrite mulmx_sub {v}// [A]a_G linear_sum summx_sub //= => x Gx.
by rewrite linearZ /= scalemx_sub // (mxmoduleP Umod).
Qed.

Lemma linear_mx_abs_irr : n = 1%N -> mx_absolutely_irreducible.
Proof.
move=> n1; rewrite /mx_absolutely_irreducible /row_full eqn_leq rank_leq_col.
rewrite {1 2 3}n1 /= lt0n mxrank_eq0; apply: contraTneq envelop_mx1 => ->.
by rewrite eqmx0 submx0 mxvec_eq0 -mxrank_eq0 mxrank1 n1.
Qed.

Lemma abelian_abs_irr : abelian G -> mx_absolutely_irreducible = (n == 1%N).
Proof.
move=> cGG; apply/idP/eqP=> [absG|]; last exact: linear_mx_abs_irr.
have [n_gt0 _] := andP absG.
pose M := <<delta_mx 0 (Ordinal n_gt0) : 'rV[F]_n>>%MS.
have rM: \rank M = 1%N by rewrite genmxE mxrank_delta.
suffices defM: (M == 1%:M)%MS by rewrite (eqmxP defM) mxrank1 in rM.
case: (mx_abs_irrW absG) => _ _ ->; rewrite ?submx1 -?mxrank_eq0 ?rM //.
apply/mxmoduleP=> x Gx; suffices: is_scalar_mx (rG x).
  by case/is_scalar_mxP=> a ->; rewrite mul_mx_scalar scalemx_sub.
apply: (mx_abs_irr_cent_scalar absG).
by apply/centgmxP=> y Gy; rewrite -!repr_mxM // (centsP cGG).
Qed.

End OneRepresentation.

Arguments mxmoduleP {gT G n rG m U}.
Arguments envelop_mxP {gT G n rG A}.
Arguments hom_mxP {gT G n rG m f W}.
Arguments rfix_mxP {gT G n rG m W}.
Arguments cyclic_mxP {gT G n rG u v}.
Arguments annihilator_mxP {gT G n rG u A}.
Arguments row_hom_mxP {gT G n rG u v}.
Arguments mxsimple_isoP {gT G n rG U V}.
Arguments socleP {gT G n rG sG0 W W'}.
Arguments mx_abs_irrP {gT G n rG}.

Arguments val_submod {n U m} W.
Arguments in_submod {n} U {m} W.
Arguments val_submodK {n U m} W : rename.
Arguments in_submodK {n U m} [W] sWU.
Arguments val_submod_inj {n U m} [W1 W2] : rename.

Arguments val_factmod {n U m} W.
Arguments in_factmod {n} U {m} W.
Arguments val_factmodK {n U m} W : rename.
Arguments in_factmodK {n} U {m} [W] sWU.
Arguments val_factmod_inj {n U m} [W1 W2] : rename.

Section Proper.

Variables (gT : finGroupType) (G : {group gT}) (n' : nat).
Local Notation n := n'.+1.
Variable rG : mx_representation F G n.

Lemma envelop_mx_ring : mxring (enveloping_algebra_mx rG).
Proof.
apply/andP; split; first by apply/mulsmx_subP; apply: envelop_mxM.
apply/mxring_idP; exists 1%:M; split=> *; rewrite ?mulmx1 ?mul1mx //.
  by rewrite -mxrank_eq0 mxrank1.
exact: envelop_mx1.
Qed.

End Proper.

Section JacobsonDensity.

Variables (gT : finGroupType) (G : {group gT}) (n : nat).
Variable rG : mx_representation F G n.
Hypothesis irrG : mx_irreducible rG.

Local Notation E_G := (enveloping_algebra_mx rG).
Local Notation Hom_G := 'C(E_G)%MS.

Lemma mx_Jacobson_density : ('C(Hom_G) <= E_G)%MS.
Proof.
apply/row_subP=> iB; rewrite -[row iB _]vec_mxK; move defB: (vec_mx _) => B.
have{defB} cBcE: (B \in 'C(Hom_G))%MS by rewrite -defB vec_mxK row_sub.
have rGnP: mx_repr G (fun x => lin_mx (mulmxr (rG x)) : 'A_n).
  split=> [|x y Gx Gy]; apply/row_matrixP=> i.
    by rewrite !rowE mul_rV_lin repr_mx1 /= !mulmx1 vec_mxK.
  by rewrite !rowE mulmxA !mul_rV_lin repr_mxM //= mxvecK mulmxA.
move def_rGn: (MxRepresentation rGnP) => rGn.
pose E_Gn := enveloping_algebra_mx rGn.
pose e1 : 'rV[F]_(n ^ 2) := mxvec 1%:M; pose U := cyclic_mx rGn e1.
have U_e1: (e1 <= U)%MS by rewrite cyclic_mx_id.
have modU: mxmodule rGn U by rewrite cyclic_mx_module.
pose Bn : 'M_(n ^ 2) := lin_mx (mulmxr B).
suffices U_e1Bn: (e1 *m Bn <= U)%MS.
  rewrite mul_vec_lin /= mul1mx in U_e1Bn; apply: submx_trans U_e1Bn _.
  rewrite genmxE; apply/row_subP=> i; rewrite row_mul rowK mul_vec_lin_row.
  by rewrite -def_rGn mul_vec_lin /= mul1mx (eq_row_sub i) ?rowK.
have{cBcE} cBncEn A: centgmx rGn A -> A *m Bn = Bn *m A.
  rewrite -def_rGn => cAG; apply/row_matrixP; case/mxvec_indexP=> j k /=.
  rewrite !rowE !mulmxA -mxvec_delta -(mul_delta_mx (0 : 'I_1)).
  rewrite mul_rV_lin mul_vec_lin /= -mulmxA; apply: (canLR vec_mxK).
  apply/row_matrixP=> i; set dj0 := delta_mx j 0.
  pose Aij := row i \o vec_mx \o mulmxr A \o mxvec \o mulmx dj0.
  have defAij := mul_rV_lin1 [linear of Aij]; rewrite /= {2}/Aij /= in defAij.
  rewrite -defAij row_mul -defAij -!mulmxA (cent_mxP cBcE) {k}//.
  rewrite memmx_cent_envelop; apply/centgmxP=> x Gx; apply/row_matrixP=> k.
  rewrite !row_mul !rowE !{}defAij /= -row_mul mulmxA mul_delta_mx.
  congr (row i _); rewrite -(mul_vec_lin (mulmxr_linear _ _)) -mulmxA.
  by rewrite -(centgmxP cAG) // mulmxA mx_rV_lin.
suffices redGn: mx_completely_reducible rGn 1%:M.
  have [V modV defUV] := redGn _ modU (submx1 _); move/mxdirect_addsP=> dxUV.
  rewrite -(proj_mx_id dxUV U_e1) -mulmxA {}cBncEn 1?mulmxA ?proj_mx_sub //.
  by rewrite -row_full_dom_hom -sub1mx -defUV proj_mx_hom.
pose W i : 'M[F]_(n ^ 2) := <<lin1_mx (mxvec \o mulmx (delta_mx i 0))>>%MS.
have defW: (\sum_i W i :=: 1%:M)%MS.
  apply/eqmxP; rewrite submx1; apply/row_subP; case/mxvec_indexP=> i j.
  rewrite row1 -mxvec_delta (sumsmx_sup i) // genmxE; apply/submxP.
  by exists (delta_mx 0 j); rewrite mul_rV_lin1 /= mul_delta_mx.
apply: mxsemisimple_reducible; apply: (intro_mxsemisimple defW) => i _ nzWi.
split=> // [|Vi modVi sViWi nzVi].
  apply/mxmoduleP=> x Gx; rewrite genmxE (eqmxMr _ (genmxE _)) -def_rGn.
  apply/row_subP=> j; rewrite rowE mulmxA !mul_rV_lin1 /= mxvecK -mulmxA.
  by apply/submxP; move: (_ *m rG x) => v; exists v; rewrite mul_rV_lin1.
do [rewrite !genmxE; set f := lin1_mx _] in sViWi *.
have f_free: row_free f.
  apply/row_freeP; exists (lin1_mx (row i \o vec_mx)); apply/row_matrixP=> j.
  by rewrite row1 rowE mulmxA !mul_rV_lin1 /= mxvecK rowE !mul_delta_mx.
pose V := <<Vi *m pinvmx f>>%MS; have Vidf := mulmxKpV sViWi.
suffices: (1%:M <= V)%MS by rewrite genmxE -(submxMfree _ _ f_free) mul1mx Vidf.
case: irrG => _ _ ->; rewrite ?submx1 //; last first.
  by rewrite -mxrank_eq0 genmxE -(mxrankMfree _ f_free) Vidf mxrank_eq0.
apply/mxmoduleP=> x Gx; rewrite genmxE (eqmxMr _ (genmxE _)).
rewrite -(submxMfree _ _ f_free) Vidf.
apply: submx_trans (mxmoduleP modVi x Gx); rewrite -{2}Vidf.
apply/row_subP=> j; apply: (eq_row_sub j); rewrite row_mul -def_rGn.
by rewrite !(row_mul _ _ f) !mul_rV_lin1 /= mxvecK !row_mul !mulmxA.
Qed.

Lemma cent_mx_scalar_abs_irr : \rank Hom_G <= 1 -> mx_absolutely_irreducible rG.
Proof.
rewrite leqNgt => /(has_non_scalar_mxP (scalar_mx_cent _ _)) scal_cE.
apply/andP; split; first by case/mx_irrP: irrG.
rewrite -sub1mx; apply: submx_trans mx_Jacobson_density.
apply/memmx_subP=> B _; apply/cent_mxP=> A cGA.
case scalA: (is_scalar_mx A); last by case: scal_cE; exists A; rewrite ?scalA.
by case/is_scalar_mxP: scalA => a ->; rewrite scalar_mxC.
Qed.

End JacobsonDensity.

Section ChangeGroup.

Variables (gT : finGroupType) (G H : {group gT}) (n : nat).
Variables (rG : mx_representation F G n).

Section SubGroup.

Hypothesis sHG : H \subset G.

Local Notation rH := (subg_repr rG sHG).

Lemma rfix_subg : rfix_mx rH = rfix_mx rG. Proof. by []. Qed.

Section Stabilisers.

Variables (m : nat) (U : 'M[F]_(m, n)).

Lemma rstabs_subg : rstabs rH U = H :&: rstabs rG U.
Proof. by apply/setP=> x; rewrite !inE andbA -in_setI (setIidPl sHG). Qed.

Lemma mxmodule_subg : mxmodule rG U -> mxmodule rH U.
Proof. by rewrite /mxmodule rstabs_subg subsetI subxx; apply: subset_trans. Qed.

End Stabilisers.

Lemma mxsimple_subg M : mxmodule rG M -> mxsimple rH M -> mxsimple rG M.
Proof.
by move=> modM [_ nzM minM]; split=> // U /mxmodule_subg; apply: minM.
Qed.

Lemma subg_mx_irr : mx_irreducible rH -> mx_irreducible rG.
Proof. by apply: mxsimple_subg; apply: mxmodule1. Qed.

Lemma subg_mx_abs_irr :
   mx_absolutely_irreducible rH -> mx_absolutely_irreducible rG.
Proof.
rewrite /mx_absolutely_irreducible -!sub1mx => /andP[-> /submx_trans-> //].
apply/row_subP=> i; rewrite rowK /= envelop_mx_id //.
by rewrite (subsetP sHG) ?enum_valP.
Qed.

End SubGroup.

Section SameGroup.

Hypothesis eqGH : G :==: H.

Local Notation rH := (eqg_repr rG eqGH).

Lemma rfix_eqg : rfix_mx rH = rfix_mx rG. Proof. by []. Qed.

Section Stabilisers.

Variables (m : nat) (U : 'M[F]_(m, n)).

Lemma rstabs_eqg : rstabs rH U = rstabs rG U.
Proof. by rewrite rstabs_subg -(eqP eqGH) (setIidPr _) ?rstabs_sub. Qed.

Lemma mxmodule_eqg : mxmodule rH U = mxmodule rG U.
Proof. by rewrite /mxmodule rstabs_eqg -(eqP eqGH). Qed.

End Stabilisers.

Lemma mxsimple_eqg M : mxsimple rH M <-> mxsimple rG M.
Proof.
rewrite /mxsimple mxmodule_eqg.
split=> [] [-> -> minM]; split=> // U modU;
 by apply: minM; rewrite mxmodule_eqg in modU *.
Qed.

Lemma eqg_mx_irr : mx_irreducible rH <-> mx_irreducible rG.
Proof. exact: mxsimple_eqg. Qed.

Lemma eqg_mx_abs_irr :
  mx_absolutely_irreducible rH = mx_absolutely_irreducible rG.
Proof.
by congr (_ && (_ == _)); rewrite /enveloping_algebra_mx /= -(eqP eqGH).
Qed.

End SameGroup.

End ChangeGroup.

Section Morphpre.

Variables (aT rT : finGroupType) (D : {group aT}) (f : {morphism D >-> rT}).
Variables (G : {group rT}) (n : nat) (rG : mx_representation F G n).

Local Notation rGf := (morphpre_repr f rG).

Section Stabilisers.
Variables (m : nat) (U : 'M[F]_(m, n)).

Lemma rstabs_morphpre : rstabs rGf U = f @*^-1 (rstabs rG U).
Proof. by apply/setP=> x; rewrite !inE andbA. Qed.

Lemma mxmodule_morphpre : G \subset f @* D -> mxmodule rGf U = mxmodule rG U.
Proof. by move=> sGf; rewrite /mxmodule rstabs_morphpre morphpreSK. Qed.

End Stabilisers.

Lemma rfix_morphpre (H : {set aT}) :
  H \subset D -> (rfix_mx rGf H :=: rfix_mx rG (f @* H))%MS.
Proof.
move=> sHD; apply/eqmxP/andP; split.
  by apply/rfix_mxP=> _ /morphimP[x _ Hx ->]; rewrite rfix_mx_id.
by apply/rfix_mxP=> x Hx; rewrite rfix_mx_id ?mem_morphim ?(subsetP sHD).
Qed.

Lemma morphpre_mx_irr :
  G \subset f @* D -> (mx_irreducible rGf <-> mx_irreducible rG).
Proof.
move/mxmodule_morphpre=> modG; split=> /mx_irrP[n_gt0 irrG];
 by apply/mx_irrP; split=> // U modU; apply: irrG; rewrite modG in modU *.
Qed.

Lemma morphpre_mx_abs_irr :
    G \subset f @* D ->
  mx_absolutely_irreducible rGf = mx_absolutely_irreducible rG.
Proof.
move=> sGfD; congr (_ && (_ == _)); apply/eqP; rewrite mxrank_leqif_sup //.
  apply/row_subP=> i; rewrite rowK.
  case/morphimP: (subsetP sGfD _ (enum_valP i)) => x Dx _ def_i.
  by rewrite def_i (envelop_mx_id rGf) // !inE Dx -def_i enum_valP.
apply/row_subP=> i; rewrite rowK (envelop_mx_id rG) //.
by case/morphpreP: (enum_valP i).
Qed.

End Morphpre.

Section Morphim.

Variables (aT rT : finGroupType) (G D : {group aT}) (f : {morphism D >-> rT}).
Variables (n : nat) (rGf : mx_representation F (f @* G) n).

Hypothesis sGD : G \subset D.

Let sG_f'fG : G \subset f @*^-1 (f @* G).
Proof. by rewrite -sub_morphim_pre. Qed.

Local Notation rG := (morphim_repr rGf sGD).

Section Stabilisers.
Variables (m : nat) (U : 'M[F]_(m, n)).

Lemma rstabs_morphim : rstabs rG U = G :&: f @*^-1 rstabs rGf U.
Proof. by rewrite -rstabs_morphpre -(rstabs_subg _ sG_f'fG). Qed.

Lemma mxmodule_morphim : mxmodule rG U = mxmodule rGf U.
Proof. by rewrite /mxmodule rstabs_morphim subsetI subxx -sub_morphim_pre. Qed.

End Stabilisers.

Lemma rfix_morphim (H : {set aT}) :
  H \subset D -> (rfix_mx rG H :=: rfix_mx rGf (f @* H))%MS.
Proof. exact: rfix_morphpre. Qed.

Lemma mxsimple_morphim M : mxsimple rG M <-> mxsimple rGf M.
Proof.
rewrite /mxsimple mxmodule_morphim.
split=> [] [-> -> minM]; split=> // U modU;
  by apply: minM; rewrite mxmodule_morphim in modU *.
Qed.

Lemma morphim_mx_irr : (mx_irreducible rG <-> mx_irreducible rGf).
Proof. exact: mxsimple_morphim. Qed.

Lemma morphim_mx_abs_irr : 
  mx_absolutely_irreducible rG = mx_absolutely_irreducible rGf.
Proof.
have fG_onto: f @* G \subset restrm sGD f @* G.
  by rewrite morphim_restrm setIid.
rewrite -(morphpre_mx_abs_irr _ fG_onto); congr (_ && (_ == _)).
by rewrite /enveloping_algebra_mx /= morphpre_restrm (setIidPl _).
Qed.

End Morphim.

Section Submodule.

Variables (gT : finGroupType) (G : {group gT}) (n : nat).
Variables (rG : mx_representation F G n) (U : 'M[F]_n) (Umod : mxmodule rG U).
Local Notation rU := (submod_repr Umod).
Local Notation rU' := (factmod_repr Umod).

Lemma rfix_submod (H : {set gT}) :
  H \subset G -> (rfix_mx rU H :=: in_submod U (U :&: rfix_mx rG H))%MS.
Proof.
move=> sHG; apply/eqmxP/andP; split; last first.
  apply/rfix_mxP=> x Hx; rewrite -in_submodJ ?capmxSl //.
  by rewrite (rfix_mxP H _) ?capmxSr.
rewrite -val_submodS in_submodK ?capmxSl // sub_capmx val_submodP //=.
apply/rfix_mxP=> x Hx.
by rewrite -(val_submodJ Umod) ?(subsetP sHG) ?rfix_mx_id.
Qed.

Lemma rfix_factmod (H : {set gT}) :
  H \subset G -> (in_factmod U (rfix_mx rG H) <= rfix_mx rU' H)%MS.
Proof.
move=> sHG; apply/rfix_mxP=> x Hx.
by rewrite -(in_factmodJ Umod) ?(subsetP sHG) ?rfix_mx_id.
Qed.

Lemma rstab_submod m (W : 'M_(m, \rank U)) :
  rstab rU W = rstab rG (val_submod W).
Proof.
apply/setP=> x; rewrite !inE; apply: andb_id2l => Gx.
by rewrite -(inj_eq val_submod_inj) val_submodJ.
Qed.

Lemma rstabs_submod m (W : 'M_(m, \rank U)) :
  rstabs rU W = rstabs rG (val_submod W).
Proof.
apply/setP=> x; rewrite !inE; apply: andb_id2l => Gx.
by rewrite -val_submodS val_submodJ.
Qed.

Lemma val_submod_module m (W : 'M_(m, \rank U)) :
   mxmodule rG (val_submod W) = mxmodule rU W.
Proof. by rewrite /mxmodule rstabs_submod. Qed.

Lemma in_submod_module m (V : 'M_(m, n)) :
  (V <= U)%MS -> mxmodule rU (in_submod U V) = mxmodule rG V.
Proof. by move=> sVU; rewrite -val_submod_module in_submodK. Qed.

Lemma rstab_factmod m (W : 'M_(m, n)) :
  rstab rG W \subset rstab rU' (in_factmod U W).
Proof.
by apply/subsetP=> x /setIdP[Gx /eqP cUW]; rewrite inE Gx -in_factmodJ //= cUW.
Qed.

Lemma rstabs_factmod m (W : 'M_(m, \rank (cokermx U))) :
  rstabs rU' W = rstabs rG (U + val_factmod W)%MS.
Proof.
apply/setP=> x; rewrite !inE; apply: andb_id2l => Gx.
rewrite addsmxMr addsmx_sub (submx_trans (mxmoduleP Umod x Gx)) ?addsmxSl //.
rewrite -val_factmodS val_factmodJ //= val_factmodS; apply/idP/idP=> nWx.
  rewrite (submx_trans (addsmxSr U _)) // -(in_factmodsK (addsmxSl U _)) //.
  by rewrite addsmxS // val_factmodS in_factmod_addsK.
rewrite in_factmodE (submx_trans (submxMr _ nWx)) // -in_factmodE.
by rewrite in_factmod_addsK val_factmodK.
Qed.

Lemma val_factmod_module m (W : 'M_(m, \rank (cokermx U))) :
  mxmodule rG (U + val_factmod W)%MS = mxmodule rU' W.
Proof. by rewrite /mxmodule rstabs_factmod. Qed.

Lemma in_factmod_module m (V : 'M_(m, n)) :
  mxmodule rU' (in_factmod U V) = mxmodule rG (U + V)%MS.
Proof.
rewrite -(eqmx_module _ (in_factmodsK (addsmxSl U V))).
by rewrite val_factmod_module (eqmx_module _ (in_factmod_addsK _ _)).
Qed.

Lemma rker_submod : rker rU = rstab rG U.
Proof. by rewrite /rker rstab_submod; apply: eqmx_rstab (val_submod1 U). Qed.

Lemma rstab_norm : G \subset 'N(rstab rG U).
Proof. by rewrite -rker_submod rker_norm. Qed.

Lemma rstab_normal : rstab rG U <| G.
Proof. by rewrite -rker_submod rker_normal. Qed.

Lemma submod_mx_faithful : mx_faithful rU -> mx_faithful rG.
Proof. by apply: subset_trans; rewrite rker_submod rstabS ?submx1. Qed.

Lemma rker_factmod : rker rG \subset rker rU'.
Proof.
apply/subsetP=> x /rkerP[Gx cVx].
by rewrite inE Gx /= /factmod_mx cVx mul1mx mulmx1 val_factmodK.
Qed.

Lemma factmod_mx_faithful : mx_faithful rU' -> mx_faithful rG.
Proof. exact: subset_trans rker_factmod. Qed.

Lemma submod_mx_irr : mx_irreducible rU <-> mxsimple rG U.
Proof.
split=> [] [_ nzU simU].
  rewrite -mxrank_eq0 mxrank1 mxrank_eq0 in nzU; split=> // V modV sVU nzV.
  rewrite -(in_submodK sVU) -val_submod1 val_submodS.
  rewrite -(genmxE (in_submod U V)) simU ?genmxE ?submx1 //=.
    by rewrite (eqmx_module _ (genmxE _)) in_submod_module.
  rewrite -submx0 genmxE -val_submodS in_submodK //.
  by rewrite linear0 eqmx0 submx0.
apply/mx_irrP; rewrite lt0n mxrank_eq0; split=> // V modV.
rewrite -(inj_eq val_submod_inj) linear0 -(eqmx_eq0 (genmxE _)) => nzV.
rewrite -sub1mx -val_submodS val_submod1 -(genmxE (val_submod V)).
rewrite simU ?genmxE ?val_submodP //=.
by rewrite (eqmx_module _ (genmxE _)) val_submod_module.
Qed.

End Submodule.

Section Conjugate.

Variables (gT : finGroupType) (G : {group gT}) (n : nat).
Variables (rG : mx_representation F G n) (B : 'M[F]_n).

Hypothesis uB : B \in unitmx.

Local Notation rGB := (rconj_repr rG uB).

Lemma rfix_conj (H : {set gT}) :
   (rfix_mx rGB H :=: B *m rfix_mx rG H *m invmx B)%MS.
Proof.
apply/eqmxP/andP; split.
  rewrite -mulmxA (eqmxMfull (_ *m _)) ?row_full_unit //.
  rewrite -[rfix_mx rGB H](mulmxK uB) submxMr //; apply/rfix_mxP=> x Hx.
  apply: (canRL (mulmxKV uB)); rewrite -(rconj_mxJ _ uB) mulmxK //.
  by rewrite rfix_mx_id.
apply/rfix_mxP=> x Gx; rewrite -3!mulmxA; congr (_ *m _).
by rewrite !mulmxA mulmxKV // rfix_mx_id.
Qed.

Lemma rstabs_conj m (U : 'M_(m, n)) : rstabs rGB U = rstabs rG (U *m B).
Proof.
apply/setP=> x; rewrite !inE rconj_mxE !mulmxA.
by rewrite -{2}[U](mulmxK uB) submxMfree // row_free_unit unitmx_inv.
Qed.

Lemma mxmodule_conj m (U : 'M_(m, n)) : mxmodule rGB U = mxmodule rG (U *m B).
Proof. by rewrite /mxmodule rstabs_conj. Qed.

Lemma conj_mx_irr : mx_irreducible rGB <-> mx_irreducible rG.
Proof.
have Bfree: row_free B by rewrite row_free_unit.
split => /mx_irrP[n_gt0 irrG]; apply/mx_irrP; split=> // U.
  rewrite -[U](mulmxKV uB) -mxmodule_conj -mxrank_eq0 /row_full mxrankMfree //.
  by rewrite mxrank_eq0; apply: irrG.
rewrite -mxrank_eq0 /row_full -(mxrankMfree _ Bfree) mxmodule_conj mxrank_eq0.
exact: irrG.
Qed.

End Conjugate.

Section Quotient.

Variables (gT : finGroupType) (G : {group gT}) (n : nat).
Variables (rG : mx_representation F G n) (H : {group gT}).
Hypotheses (krH : H \subset rker rG) (nHG : G \subset 'N(H)).
Let nHGs := subsetP nHG.

Local Notation rGH := (quo_repr krH nHG).

Local Notation E_ r := (enveloping_algebra_mx r).
Lemma quo_mx_quotient : (E_ rGH :=: E_ rG)%MS.
Proof.
apply/eqmxP/andP; split; apply/row_subP=> i.
  rewrite rowK; case/morphimP: (enum_valP i) => x _ Gx ->{i}.
  rewrite quo_repr_coset // (eq_row_sub (enum_rank_in Gx x)) // rowK.
  by rewrite enum_rankK_in.
rewrite rowK -(quo_mx_coset krH nHG) ?enum_valP //; set Hx := coset H _.
have GHx: Hx \in (G / H)%g by rewrite mem_quotient ?enum_valP.
by rewrite (eq_row_sub (enum_rank_in GHx Hx)) // rowK enum_rankK_in.
Qed.

Lemma rfix_quo (K : {group gT}) :
  K \subset G -> (rfix_mx rGH (K / H)%g :=: rfix_mx rG K)%MS.
Proof.
move=> sKG; apply/eqmxP/andP; (split; apply/rfix_mxP) => [x Kx | Hx].
  have Gx := subsetP sKG x Kx; rewrite -(quo_mx_coset krH nHG) // rfix_mx_id //.
  by rewrite mem_morphim ?(subsetP nHG).
case/morphimP=> x _ Kx ->; have Gx := subsetP sKG x Kx.
by rewrite quo_repr_coset ?rfix_mx_id.
Qed.

Lemma rstabs_quo m (U : 'M_(m, n)) : rstabs rGH U = (rstabs rG U / H)%g.
Proof.
apply/setP=> Hx; rewrite !inE; apply/andP/idP=> [[]|] /morphimP[x Nx Gx ->{Hx}].
  by rewrite quo_repr_coset // => nUx; rewrite mem_morphim // inE Gx.
by case/setIdP: Gx => Gx nUx; rewrite quo_repr_coset ?mem_morphim.
Qed.

Lemma mxmodule_quo m (U : 'M_(m, n)) : mxmodule rGH U = mxmodule rG U.
Proof.
rewrite /mxmodule rstabs_quo quotientSGK // ?(subset_trans krH) //.
apply/subsetP=> x; rewrite !inE mul1mx => /andP[-> /eqP->].
by rewrite /= mulmx1.
Qed.

Lemma quo_mx_irr : mx_irreducible rGH <-> mx_irreducible rG.
Proof.
split; case/mx_irrP=> n_gt0 irrG; apply/mx_irrP; split=> // U modU;
  by apply: irrG; rewrite mxmodule_quo in modU *.
Qed.

End Quotient.

Section SplittingField.

Implicit Type gT : finGroupType.

Definition group_splitting_field gT (G : {group gT}) :=
  forall n (rG : mx_representation F G n),
     mx_irreducible rG -> mx_absolutely_irreducible rG.

Definition group_closure_field gT :=
  forall G : {group gT}, group_splitting_field G.

Lemma quotient_splitting_field gT (G : {group gT}) (H : {set gT}) :
  G \subset 'N(H) -> group_splitting_field G -> group_splitting_field (G / H).
Proof.
move=> nHG splitG n rGH irrGH.
by rewrite -(morphim_mx_abs_irr _ nHG) splitG //; apply/morphim_mx_irr.
Qed.

Lemma coset_splitting_field gT (H : {set gT}) :
  group_closure_field gT -> group_closure_field (coset_groupType H).
Proof.
move=> split_gT Gbar; have ->: Gbar = (coset H @*^-1 Gbar / H)%G.
  by apply: val_inj; rewrite /= /quotient morphpreK ?sub_im_coset.
by apply: quotient_splitting_field; [apply: subsetIl | apply: split_gT].
Qed.

End SplittingField.

Section Abelian.

Variables (gT : finGroupType) (G : {group gT}).

Lemma mx_faithful_irr_center_cyclic n (rG : mx_representation F G n) :
  mx_faithful rG -> mx_irreducible rG -> cyclic 'Z(G).
Proof.
case: n rG => [|n] rG injG irrG; first by case/mx_irrP: irrG.
move/trivgP: injG => KrG1; pose rZ := subg_repr rG (center_sub _).
apply: (div_ring_mul_group_cyclic (repr_mx1 rZ)) (repr_mxM rZ) _ _; last first.
  exact: center_abelian.
move=> x; rewrite -[[set _]]KrG1 !inE mul1mx -subr_eq0 andbC; set U := _ - _.
do 2![case/andP]=> Gx cGx; rewrite Gx /=; apply: (mx_Schur irrG).
apply/centgmxP=> y Gy; rewrite mulmxBl mulmxBr mulmx1 mul1mx.
by rewrite -!repr_mxM // (centP cGx).
Qed.

Lemma mx_faithful_irr_abelian_cyclic n (rG : mx_representation F G n) :
  mx_faithful rG -> mx_irreducible rG -> abelian G -> cyclic G.
Proof.
move=> injG irrG cGG; rewrite -(setIidPl cGG).
exact: mx_faithful_irr_center_cyclic injG irrG.
Qed.

Hypothesis splitG : group_splitting_field G.

Lemma mx_irr_abelian_linear n (rG : mx_representation F G n) :
  mx_irreducible rG -> abelian G -> n = 1%N.
Proof.
by move=> irrG cGG; apply/eqP; rewrite -(abelian_abs_irr rG) ?splitG.
Qed.

Lemma mxsimple_abelian_linear n (rG : mx_representation F G n) M :
  abelian G -> mxsimple rG M -> \rank M = 1%N.
Proof.
move=> cGG simM; have [modM _ _] := simM.
by move/(submod_mx_irr modM)/mx_irr_abelian_linear: simM => ->.
Qed.

Lemma linear_mxsimple n (rG : mx_representation F G n) (M : 'M_n) :
  mxmodule rG M -> \rank M = 1%N -> mxsimple rG M.
Proof.
move=> modM rM1; apply/(submod_mx_irr modM).
by apply: mx_abs_irrW; rewrite linear_mx_abs_irr.
Qed.

End Abelian.

Section AbelianQuotient.

Variables (gT : finGroupType) (G : {group gT}).
Variables (n : nat) (rG : mx_representation F G n).

Lemma center_kquo_cyclic : mx_irreducible rG -> cyclic 'Z(G / rker rG)%g.
Proof.
move=> irrG; apply: mx_faithful_irr_center_cyclic (kquo_mx_faithful rG) _.
exact/quo_mx_irr.
Qed.

Lemma der1_sub_rker :
    group_splitting_field G -> mx_irreducible rG ->
  (G^`(1) \subset rker rG)%g = (n == 1)%N.
Proof.
move=> splitG irrG; apply/idP/idP; last by move/eqP; apply: rker_linear.
move/sub_der1_abelian; move/(abelian_abs_irr (kquo_repr rG))=> <-.
by apply: (quotient_splitting_field (rker_norm _) splitG); apply/quo_mx_irr.
Qed.

End AbelianQuotient.

Section Similarity.

Variables (gT : finGroupType) (G : {group gT}).
Local Notation reprG := (mx_representation F G).

Variant mx_rsim n1 (rG1 : reprG n1) n2 (rG2 : reprG n2) : Prop :=
  MxReprSim B of n1 = n2 & row_free B
              & forall x, x \in G -> rG1 x *m B = B *m rG2 x.

Lemma mxrank_rsim n1 n2 (rG1 : reprG n1) (rG2 : reprG n2) :
  mx_rsim rG1 rG2 -> n1 = n2.
Proof. by case. Qed.

Lemma mx_rsim_refl n (rG : reprG n) : mx_rsim rG rG.
Proof.
exists 1%:M => // [|x _]; first by rewrite row_free_unit unitmx1.
by rewrite mulmx1 mul1mx.
Qed.

Lemma mx_rsim_sym n1 n2 (rG1 : reprG n1) (rG2 : reprG n2) :
  mx_rsim rG1 rG2 ->  mx_rsim rG2 rG1.
Proof.
case=> B def_n1; rewrite def_n1 in rG1 B *.
rewrite row_free_unit => injB homB; exists (invmx B) => // [|x Gx].
  by rewrite row_free_unit unitmx_inv.
by apply: canRL (mulKmx injB) _; rewrite mulmxA -homB ?mulmxK.
Qed.

Lemma mx_rsim_trans n1 n2 n3
                    (rG1 : reprG n1) (rG2 : reprG n2) (rG3 : reprG n3) :
  mx_rsim rG1 rG2 -> mx_rsim rG2 rG3 -> mx_rsim rG1 rG3.
Proof.
case=> [B1 defn1 freeB1 homB1] [B2 defn2 freeB2 homB2].
exists (B1 *m B2); rewrite /row_free ?mxrankMfree 1?defn1 // => x Gx.
by rewrite mulmxA homB1 // -!mulmxA homB2.
Qed.

Lemma mx_rsim_def n1 n2 (rG1 : reprG n1) (rG2 : reprG n2) :
    mx_rsim rG1 rG2 -> 
  exists B, exists2 B', B' *m B = 1%:M &
    forall x, x \in G -> rG1 x = B *m rG2 x *m B'.
Proof.
case=> B def_n1; rewrite def_n1 in rG1 B *; rewrite row_free_unit => injB homB.
by exists B, (invmx B) => [|x Gx]; rewrite ?mulVmx // -homB // mulmxK.
Qed.

Lemma mx_rsim_iso n (rG : reprG n) (U V : 'M_n)
                  (modU : mxmodule rG U) (modV : mxmodule rG V) :
  mx_rsim (submod_repr modU) (submod_repr modV) <-> mx_iso rG U V.
Proof.
split=> [[B eqrUV injB homB] | [f injf homf defV]].
  have: \rank (U *m val_submod (in_submod U 1%:M *m B)) = \rank U.
    do 2!rewrite mulmxA mxrankMfree ?row_base_free //.
    by rewrite -(eqmxMr _ (val_submod1 U)) -in_submodE val_submodK mxrank1.
  case/complete_unitmx => f injf defUf; exists f => //.
    apply/hom_mxP=> x Gx; rewrite -defUf -2!mulmxA -(val_submodJ modV) //.
    rewrite -(mulmxA _ B) -homB // val_submodE 3!(mulmxA U) (mulmxA _ _ B).
    rewrite -in_submodE -in_submodJ //.
    have [u ->] := submxP (mxmoduleP modU x Gx).
    by rewrite in_submodE -mulmxA -defUf !mulmxA mulmx1.
  apply/eqmxP; rewrite -mxrank_leqif_eq.
    by rewrite mxrankMfree ?eqrUV ?row_free_unit.
  by rewrite -defUf mulmxA val_submodP.
have eqrUV: \rank U = \rank V by rewrite -defV mxrankMfree ?row_free_unit.
exists (in_submod V (val_submod 1%:M *m f)) => // [|x Gx].
  rewrite /row_free {6}eqrUV -[_ == _]sub1mx -val_submodS.
  rewrite in_submodK; last by rewrite -defV submxMr ?val_submodP.
  by rewrite val_submod1 -defV submxMr ?val_submod1.
rewrite -in_submodJ; last by rewrite -defV submxMr ?val_submodP.
rewrite -(hom_mxP (submx_trans (val_submodP _) homf)) //.
by rewrite -(val_submodJ modU) // mul1mx 2!(mulmxA ((submod_repr _) x)) -val_submodE.
Qed.

Lemma mx_rsim_irr n1 n2 (rG1 : reprG n1) (rG2 : reprG n2) :
  mx_rsim rG1 rG2 -> mx_irreducible rG1 -> mx_irreducible rG2.
Proof.
case/mx_rsim_sym=> f def_n2; rewrite {n2}def_n2 in f rG2 * => injf homf.
case/mx_irrP=> n1_gt0 minG; apply/mx_irrP; split=> // U modU nzU.
rewrite /row_full -(mxrankMfree _ injf) -genmxE.
apply: minG; last by rewrite -mxrank_eq0 genmxE mxrankMfree // mxrank_eq0.
rewrite (eqmx_module _ (genmxE _)); apply/mxmoduleP=> x Gx.
by rewrite -mulmxA -homf // mulmxA submxMr // (mxmoduleP modU).
Qed.

Lemma mx_rsim_abs_irr n1 n2 (rG1 : reprG n1) (rG2 : reprG n2) :
    mx_rsim rG1 rG2 ->
  mx_absolutely_irreducible rG1 = mx_absolutely_irreducible rG2.
Proof.
case=> f def_n2; rewrite -{n2}def_n2 in f rG2 *.
rewrite row_free_unit => injf homf; congr (_ && (_ == _)).
pose Eg (g : 'M[F]_n1) := lin_mx (mulmxr (invmx g) \o mulmx g).
have free_Ef: row_free (Eg f).
  apply/row_freeP; exists (Eg (invmx f)); apply/row_matrixP=> i.
  rewrite rowE row1 mulmxA mul_rV_lin mx_rV_lin /=.
  by rewrite invmxK !{1}mulmxA mulmxKV // -mulmxA mulKmx // vec_mxK.
symmetry; rewrite -(mxrankMfree _ free_Ef); congr (\rank _).
apply/row_matrixP=> i; rewrite row_mul !rowK mul_vec_lin /=.
by rewrite -homf ?enum_valP // mulmxK.
Qed.

Lemma rker_mx_rsim n1 n2 (rG1 : reprG n1) (rG2 : reprG n2) :
  mx_rsim rG1 rG2 -> rker rG1 = rker rG2.
Proof.
case=> f def_n2; rewrite -{n2}def_n2 in f rG2 *.
rewrite row_free_unit => injf homf.
apply/setP=> x; rewrite !inE !mul1mx; apply: andb_id2l => Gx.
by rewrite -(can_eq (mulmxK injf)) homf // -scalar_mxC (can_eq (mulKmx injf)).
Qed.

Lemma mx_rsim_faithful n1 n2 (rG1 : reprG n1) (rG2 : reprG n2) :
  mx_rsim rG1 rG2 -> mx_faithful rG1 = mx_faithful rG2.
Proof. by move=> simG12; rewrite /mx_faithful (rker_mx_rsim simG12). Qed.

Lemma mx_rsim_factmod n (rG : reprG n) U V
                     (modU : mxmodule rG U) (modV : mxmodule rG V) :
    (U + V :=: 1%:M)%MS -> mxdirect (U + V) ->
  mx_rsim (factmod_repr modV) (submod_repr modU).
Proof.
move=> addUV dxUV.
have eqUV: \rank U = \rank (cokermx V).
  by rewrite mxrank_coker -{3}(mxrank1 F n) -addUV (mxdirectP dxUV) addnK.
have{dxUV} dxUV: (U :&: V = 0)%MS by apply/mxdirect_addsP.
exists (in_submod U (val_factmod 1%:M *m proj_mx U V)) => // [|x Gx].
  rewrite /row_free -{6}eqUV -[_ == _]sub1mx -val_submodS val_submod1.
  rewrite in_submodK ?proj_mx_sub // -{1}[U](proj_mx_id dxUV) //.
  rewrite -{1}(add_sub_fact_mod V U) mulmxDl proj_mx_0 ?val_submodP // add0r.
  by rewrite submxMr // val_factmodS submx1.
rewrite -in_submodJ ?proj_mx_sub // -(hom_mxP _) //; last first.
  by apply: submx_trans (submx1 _) _; rewrite -addUV proj_mx_hom.
rewrite mulmxA; congr (_ *m _); rewrite mulmxA -val_factmodE; apply/eqP.
rewrite eq_sym -subr_eq0 -mulmxBl proj_mx_0 //.
by rewrite -[_ *m rG x](add_sub_fact_mod V) addrK val_submodP.
Qed.

Lemma mxtrace_rsim n1 n2 (rG1 : reprG n1) (rG2 : reprG n2) :
  mx_rsim rG1 rG2 -> {in G, forall x, \tr (rG1 x) = \tr (rG2 x)}.
Proof.
case/mx_rsim_def=> B [B' B'B def_rG1] x Gx.
by rewrite def_rG1 // mxtrace_mulC mulmxA B'B mul1mx.
Qed.

Lemma mx_rsim_scalar n1 n2 (rG1 : reprG n1) (rG2 : reprG n2) x c :
   x \in G -> mx_rsim rG1 rG2 -> rG1 x = c%:M -> rG2 x = c%:M.
Proof.
move=> Gx /mx_rsim_sym[B _ Bfree rG2_B] rG1x.
by apply: (row_free_inj Bfree); rewrite rG2_B // rG1x scalar_mxC.
Qed.

End Similarity.

Section Socle.

Variables (gT : finGroupType) (G : {group gT}).
Variables (n : nat) (rG : mx_representation F G n) (sG : socleType rG).

Lemma socle_irr (W : sG) : mx_irreducible (socle_repr W).
Proof. by apply/submod_mx_irr; apply: socle_simple. Qed.

Lemma socle_rsimP (W1 W2 : sG) :
  reflect (mx_rsim (socle_repr W1) (socle_repr W2)) (W1 == W2).
Proof.
have [simW1 simW2] := (socle_simple W1, socle_simple W2).
by apply: (iffP (component_mx_isoP simW1 simW2)); move/mx_rsim_iso; apply.
Qed.

Local Notation mG U := (mxmodule rG U).
Local Notation sr modV := (submod_repr modV).

Lemma mx_rsim_in_submod U V (modU : mG U) (modV : mG V) :
  let U' := <<in_submod V U>>%MS in
    (U <= V)%MS ->
  exists modU' : mxmodule (sr modV) U', mx_rsim (sr modU) (sr modU').
Proof.
move=> U' sUV; have modU': mxmodule (sr modV) U'.
  by rewrite (eqmx_module _ (genmxE _)) in_submod_module.
have rankU': \rank U = \rank U' by rewrite genmxE mxrank_in_submod.
pose v1 := val_submod 1%:M; pose U1 := v1 _ U.
have sU1V: (U1 <= V)%MS by rewrite val_submod1.
have sU1U': (in_submod V U1 <= U')%MS by rewrite genmxE submxMr ?val_submod1.
exists modU', (in_submod U' (in_submod V U1)) => // [|x Gx].
  apply/row_freeP; exists (v1 _ _ *m v1 _ _ *m in_submod U 1%:M).
  by rewrite 2!mulmxA -in_submodE -!val_submodE !in_submodK ?val_submodK.
rewrite -!in_submodJ // -(val_submodJ modU) // mul1mx.
by rewrite 2!{1}in_submodE mulmxA (mulmxA _ U1) -val_submodE -!in_submodE.
Qed.

Lemma rsim_submod1 U (modU : mG U) : (U :=: 1%:M)%MS -> mx_rsim (sr modU) rG.
Proof.
move=> U1; exists (val_submod 1%:M) => [||x Gx]; first by rewrite U1 mxrank1.
  by rewrite /row_free val_submod1.
by rewrite -(val_submodJ modU) // mul1mx -val_submodE.
Qed.

Lemma mxtrace_submod1 U (modU : mG U) :
  (U :=: 1%:M)%MS -> {in G, forall x, \tr (sr modU x) = \tr (rG x)}.
Proof. by move=> defU; apply: mxtrace_rsim (rsim_submod1 modU defU). Qed.

Lemma mxtrace_dadd_mod U V W (modU : mG U) (modV : mG V) (modW : mG W) :
    (U + V :=: W)%MS -> mxdirect (U + V) ->
  {in G, forall x, \tr (sr modU x) + \tr (sr modV x) = \tr (sr modW x)}.
Proof.
move=> defW dxW x Gx; have [sUW sVW]: (U <= W)%MS /\ (V <= W)%MS.
  by apply/andP; rewrite -addsmx_sub defW.
pose U' := <<in_submod W U>>%MS; pose V' := <<in_submod W V>>%MS.
have addUV': (U' + V' :=: 1%:M)%MS.
  apply/eqmxP; rewrite submx1 /= (adds_eqmx (genmxE _) (genmxE _)).
  by rewrite -addsmxMr -val_submodS val_submod1 in_submodK ?defW.
have dxUV': mxdirect (U' + V').
  apply/eqnP; rewrite /= addUV' mxrank1 !genmxE !mxrank_in_submod //.
  by rewrite -(mxdirectP dxW) /= defW.
have [modU' simU] := mx_rsim_in_submod modU modW sUW.
have [modV' simV] := mx_rsim_in_submod modV modW sVW.
rewrite (mxtrace_rsim simU) // (mxtrace_rsim simV) //.
rewrite -(mxtrace_sub_fact_mod modV') addrC; congr (_ + _).
by rewrite (mxtrace_rsim (mx_rsim_factmod modU' modV' addUV' dxUV')).
Qed.

Lemma mxtrace_dsum_mod (I : finType) (P : pred I) U W
                       (modU : forall i, mG (U i)) (modW : mG W) :
    let S := (\sum_(i | P i) U i)%MS in (S :=: W)%MS -> mxdirect S -> 
  {in G, forall x, \sum_(i | P i) \tr (sr (modU i) x) = \tr (sr modW x)}.
Proof.
move=> /= sumS dxS x Gx.
elim: {P}_.+1 {-2}P (ltnSn #|P|) => // m IHm P lePm in W modW sumS dxS *.
have [j /= Pj | P0] := pickP P; last first.
  case: sumS (_ x); rewrite !big_pred0 // mxrank0 => <- _ rWx.
  by rewrite [rWx]flatmx0 linear0.
rewrite ltnS (cardD1x Pj) in lePm.
rewrite mxdirectE /= !(bigD1 j Pj) -mxdirectE mxdirect_addsE /= in dxS sumS *.
have [_ dxW' dxW] := and3P dxS; rewrite (sameP eqP mxdirect_addsP) in dxW.
rewrite (IHm _ _ _ (sumsmx_module _ (fun i _ => modU i)) (eqmx_refl _)) //.
exact: mxtrace_dadd_mod.
Qed.

Lemma mxtrace_component U (simU : mxsimple rG U) :
   let V := component_mx rG U in
   let modV := component_mx_module rG U in let modU := mxsimple_module simU in
  {in G, forall x, \tr (sr modV x) = \tr (sr modU x) *+ (\rank V %/ \rank U)}.
Proof.
move=> V modV modU x Gx.
have [I W S simW defV dxV] := component_mx_semisimple simU.
rewrite -(mxtrace_dsum_mod (fun i => mxsimple_module (simW i)) modV defV) //.
have rankU_gt0: \rank U > 0 by rewrite lt0n mxrank_eq0; case simU.
have isoW i: mx_iso rG U (W i).
  by apply: component_mx_iso; rewrite ?simU // -defV (sumsmx_sup i).
have ->: (\rank V %/ \rank U)%N = #|I|.
  symmetry; rewrite -(mulnK #|I| rankU_gt0); congr (_ %/ _)%N.
  rewrite -defV (mxdirectP dxV) /= -sum_nat_const.
  by apply: eq_bigr => i _; apply: mxrank_iso.
rewrite -sumr_const; apply: eq_bigr => i _; symmetry.
by apply: mxtrace_rsim Gx; apply/mx_rsim_iso; apply: isoW.
Qed.

Lemma mxtrace_Socle : let modS := Socle_module sG in
  {in G, forall x,
    \tr (sr modS x) = \sum_(W : sG) \tr (socle_repr W x) *+ socle_mult W}.
Proof.
move=> /= x Gx /=; pose modW (W : sG) := component_mx_module rG (socle_base W).
rewrite -(mxtrace_dsum_mod modW _ (eqmx_refl _) (Socle_direct sG)) //.
by apply: eq_bigr => W _; rewrite (mxtrace_component (socle_simple W)).
Qed.

End Socle.

Section Clifford.

Variables (gT : finGroupType) (G H : {group gT}).
Hypothesis nsHG : H <| G.
Variables (n : nat) (rG : mx_representation F G n).
Let sHG := normal_sub nsHG.
Let nHG := normal_norm nsHG.
Let rH := subg_repr rG sHG.

Lemma Clifford_simple M x : mxsimple rH M -> x \in G -> mxsimple rH (M *m rG x).
Proof.
have modmG m U y: y \in G -> (mxmodule rH) m U -> mxmodule rH (U *m rG y).
  move=> Gy modU; apply/mxmoduleP=> h Hh; have Gh := subsetP sHG h Hh.
  rewrite -mulmxA -repr_mxM // conjgCV repr_mxM ?groupJ ?groupV // mulmxA.
  by rewrite submxMr ?(mxmoduleP modU) // -mem_conjg (normsP nHG).
have nzmG m y (U : 'M_(m, n)): y \in G -> (U *m rG y == 0) = (U == 0).
  by move=> Gy; rewrite -{1}(mul0mx m (rG y)) (can_eq (repr_mxK rG Gy)).
case=> [modM nzM simM] Gx; have Gx' := groupVr Gx.
split=> [||U modU sUMx nzU]; rewrite ?modmG ?nzmG //.
rewrite -(repr_mxKV rG Gx U) submxMr //.
by rewrite (simM (U *m _)) ?modmG ?nzmG // -(repr_mxK rG Gx M) submxMr.
Qed.

Lemma Clifford_hom x m (U : 'M_(m, n)) :
  x \in 'C_G(H) -> (U <= dom_hom_mx rH (rG x))%MS.
Proof.
case/setIP=> Gx cHx; apply/rV_subP=> v _{U}.
apply/hom_mxP=> h Hh; have Gh := subsetP sHG h Hh.
by rewrite -!mulmxA /= -!repr_mxM // (centP cHx).
Qed.

Lemma Clifford_iso x U : x \in 'C_G(H) -> mx_iso rH U (U *m rG x).
Proof.
move=> cHx; have [Gx _] := setIP cHx.
by exists (rG x); rewrite ?repr_mx_unit ?Clifford_hom.
Qed.

Lemma Clifford_iso2 x U V :
  mx_iso rH U V -> x \in G -> mx_iso rH (U *m rG x) (V *m rG x).
Proof.
case=> [f injf homUf defV] Gx; have Gx' := groupVr Gx.
pose fx := rG (x^-1)%g *m f *m rG x; exists fx; last 1 first.
- by rewrite !mulmxA repr_mxK //; apply: eqmxMr.
- by rewrite !unitmx_mul andbC !repr_mx_unit.
apply/hom_mxP=> h Hh; have Gh := subsetP sHG h Hh.
rewrite -(mulmxA U) -repr_mxM // conjgCV repr_mxM ?groupJ // !mulmxA.
rewrite !repr_mxK // (hom_mxP homUf) -?mem_conjg ?(normsP nHG) //=.
by rewrite !repr_mxM ?invgK ?groupM // !mulmxA repr_mxKV.
Qed.

Lemma Clifford_componentJ M x :
    mxsimple rH M -> x \in G ->
  (component_mx rH (M *m rG x) :=: component_mx rH M *m rG x)%MS.
Proof.
set simH := mxsimple rH; set cH := component_mx rH.
have actG: {in G, forall y M, simH M -> cH M *m rG y <= cH (M *m rG y)}%MS.
  move=> {M} y Gy /= M simM; have [I [U isoU def_cHM]] := component_mx_def simM.
  rewrite /cH def_cHM sumsmxMr; apply/sumsmx_subP=> i _.
  by apply: mx_iso_component; [apply: Clifford_simple | apply: Clifford_iso2].
move=> simM Gx; apply/eqmxP; rewrite actG // -/cH.
rewrite -{1}[cH _](repr_mxKV rG Gx) submxMr // -{2}[M](repr_mxK rG Gx).
by rewrite actG ?groupV //; apply: Clifford_simple.
Qed.

Hypothesis irrG : mx_irreducible rG.

Lemma Clifford_basis M : mxsimple rH M ->
  {X : {set gT} | X \subset G &
    let S := \sum_(x in X) M *m rG x in S :=: 1%:M /\ mxdirect S}%MS.
Proof.
move=> simM. have simMG (g : [subg G]) : mxsimple rH (M *m rG (val g)).
  by case: g => x Gx; apply: Clifford_simple.
have [|XG [defX1 dxX1]] := sum_mxsimple_direct_sub simMG (_ : _ :=: 1%:M)%MS.
  apply/eqmxP; case irrG => _ _ ->; rewrite ?submx1 //; last first.
    rewrite -submx0; apply/sumsmx_subP; move/(_ 1%g (erefl _)); apply: negP.
    by rewrite submx0 repr_mx1 mulmx1; case simM.
  apply/mxmoduleP=> x Gx; rewrite sumsmxMr; apply/sumsmx_subP=> [[y Gy]] /= _.
  by rewrite (sumsmx_sup (subg G (y * x))) // subgK ?groupM // -mulmxA repr_mxM.
exists (val @: XG); first by apply/subsetP=> ?; case/imsetP=> [[x Gx]] _ ->.
have bij_val: {on val @: XG, bijective (@sgval _ G)}.
  exists (subg G) => [g _ | x]; first exact: sgvalK.
  by case/imsetP=> [[x' Gx]] _ ->; rewrite subgK.
have defXG g: (val g \in val @: XG) = (g \in XG).
  by apply/imsetP/idP=> [[h XGh] | XGg]; [move/val_inj-> | exists g].
by rewrite /= mxdirectE /= !(reindex _ bij_val) !(eq_bigl _ _ defXG).
Qed.

Variable sH : socleType rH.

Definition Clifford_act (W : sH) x :=
  let Gx := subgP (subg G x) in
  PackSocle (component_socle sH (Clifford_simple (socle_simple W) Gx)).

Let valWact W x : (Clifford_act W x :=: W *m rG (sgval (subg G x)))%MS.
Proof.
rewrite PackSocleK; apply: Clifford_componentJ (subgP _).
exact: socle_simple.
Qed.

Fact Clifford_is_action : is_action G Clifford_act.
Proof.
split=> [x W W' eqWW' | W x y Gx Gy].
  pose Gx := subgP (subg G x); apply/socleP; apply/eqmxP.
  rewrite -(repr_mxK rG Gx W) -(repr_mxK rG Gx W'); apply: eqmxMr.
  apply: eqmx_trans (eqmx_sym _) (valWact _ _).
  by rewrite -eqWW'; apply: valWact.
apply/socleP; rewrite !{1}valWact 2!{1}(eqmxMr _ (valWact _ _)).
by rewrite !subgK ?groupM ?repr_mxM ?mulmxA ?andbb.
Qed.

Definition Clifford_action := Action Clifford_is_action.

Local Notation "'Cl" := Clifford_action (at level 8) : action_scope.

Lemma val_Clifford_act W x : x \in G -> ('Cl%act W x :=: W *m rG x)%MS.
Proof. by move=> Gx; apply: eqmx_trans (valWact _ _) _; rewrite subgK. Qed.

Lemma Clifford_atrans : [transitive G, on [set: sH] | 'Cl].
Proof.
have [_ nz1 _] := irrG.
apply: mxsimple_exists (mxmodule1 rH) nz1 _ _ => [[M simM _]].
pose W1 := PackSocle (component_socle sH simM).
have [X sXG [def1 _]] := Clifford_basis simM; move/subsetP: sXG => sXG.
apply/imsetP; exists W1; first by rewrite inE.
symmetry; apply/setP=> W; rewrite inE; have simW := socle_simple W.
have:= submx1 (socle_base W); rewrite -def1 -[(\sum_(x in X) _)%MS]mulmx1.
case/(hom_mxsemisimple_iso simW) => [x Xx _ | | x Xx isoMxW].
- by apply: Clifford_simple; rewrite ?sXG.
- exact: scalar_mx_hom.
have Gx := sXG x Xx; apply/imsetP; exists x => //; apply/socleP/eqmxP/eqmx_sym.
apply: eqmx_trans (val_Clifford_act _ Gx) _; rewrite PackSocleK.
apply: eqmx_trans (eqmx_sym (Clifford_componentJ simM Gx)) _.
apply/eqmxP; rewrite (sameP genmxP eqP) !{1}genmx_component.
by apply/component_mx_isoP=> //; apply: Clifford_simple.
Qed.

Lemma Clifford_Socle1 : Socle sH = 1%:M.
Proof.
case/imsetP: Clifford_atrans => W _ _; have simW := socle_simple W.
have [X sXG [def1 _]] := Clifford_basis simW.
rewrite reducible_Socle1 //; apply: mxsemisimple_reducible.
apply: intro_mxsemisimple def1 _ => x /(subsetP sXG) Gx _.
exact: Clifford_simple.
Qed.

Lemma Clifford_rank_components (W : sH) : (#|sH| * \rank W)%N = n.
Proof.
rewrite -{9}(mxrank1 F n) -Clifford_Socle1.
rewrite (mxdirectP (Socle_direct sH)) /= -sum_nat_const.
apply: eq_bigr => W1 _; have [W0 _ W0G] := imsetP Clifford_atrans.
have{W0G} W0G W': W' \in orbit 'Cl G W0 by rewrite -W0G inE.
have [/orbitP[x Gx <-] /orbitP[y Gy <-]] := (W0G W, W0G W1).
by rewrite !{1}val_Clifford_act // !mxrankMfree // !repr_mx_free.
Qed.

Theorem Clifford_component_basis M : mxsimple rH M ->
  {t : nat & {x_ : sH -> 'I_t -> gT |
    forall W, let sW := (\sum_j M *m rG (x_ W j))%MS in
      [/\ forall j, x_ W j \in G, (sW :=: W)%MS & mxdirect sW]}}.
Proof.
move=> simM; pose t := (n %/ #|sH| %/ \rank M)%N; exists t.
have [X /subsetP sXG [defX1 dxX1]] := Clifford_basis simM.
pose sMv (W : sH) x := (M *m rG x <= W)%MS; pose Xv := [pred x in X | sMv _ x].
have sXvG W: {subset Xv W <= G} by move=> x /andP[/sXG].
have defW W: (\sum_(x in Xv W) M *m rG x :=: W)%MS.
  apply/eqmxP; rewrite -(geq_leqif (mxrank_leqif_eq _)); last first.
    by apply/sumsmx_subP=> x /andP[].
  rewrite -(leq_add2r (\sum_(W' | W' != W) \rank W')) -((bigD1 W) predT) //=.
  rewrite -(mxdirectP (Socle_direct sH)) /= -/(Socle _) Clifford_Socle1 -defX1.
  apply: leq_trans (mxrankS _) (mxrank_sum_leqif _).1 => /=.
  rewrite (bigID (sMv W))%MS addsmxS //=.
  apply/sumsmx_subP=> x /andP[Xx notW_Mx]; have Gx := sXG x Xx.
  have simMx := Clifford_simple simM Gx.
  pose Wx := PackSocle (component_socle sH simMx).
  have sMxWx: (M *m rG x <= Wx)%MS by rewrite PackSocleK component_mx_id.
  by rewrite (sumsmx_sup Wx) //; apply: contra notW_Mx => /eqP <-.
have dxXv W: mxdirect (\sum_(x in Xv W) M *m rG x).
  move: dxX1; rewrite !mxdirectE /= !(bigID (sMv W) (mem X)) /=.
  by rewrite -mxdirectE mxdirect_addsE /= => /andP[].
have def_t W: #|Xv W| = t.
  rewrite /t -{1}(Clifford_rank_components W) mulKn 1?(cardD1 W) //.
  rewrite -defW (mxdirectP (dxXv W)) /= (eq_bigr (fun _ => \rank M)) => [|x].
    rewrite sum_nat_const mulnK //; last by rewrite lt0n mxrank_eq0; case simM.
  by move/sXvG=> Gx; rewrite mxrankMfree // row_free_unit repr_mx_unit.
exists (fun W i => enum_val (cast_ord (esym (def_t W)) i)) => W.
case: {def_t}t / (def_t W) => sW.
case: (pickP (Xv W)) => [x0 XvWx0 | XvW0]; last first.
  by case/negP: (nz_socle W); rewrite -submx0 -defW big_pred0.
have{x0 XvWx0} reXv := reindex _ (enum_val_bij_in XvWx0).
have def_sW: (sW :=: W)%MS.
  apply: eqmx_trans (defW W); apply/eqmxP; apply/genmxP; congr <<_>>%MS.
  rewrite reXv /=; apply: eq_big => [j | j _]; first by have:= enum_valP j.
  by rewrite cast_ord_id.
split=> // [j|]; first by rewrite (sXvG W) ?enum_valP.
apply/mxdirectP; rewrite def_sW -(defW W) /= (mxdirectP (dxXv W)) /= reXv /=.
by apply: eq_big => [j | j _]; [move: (enum_valP j) | rewrite cast_ord_id].
Qed.

Lemma Clifford_astab : H <*> 'C_G(H) \subset 'C([set: sH] | 'Cl).
Proof.
rewrite join_subG !subsetI sHG subsetIl /=; apply/andP; split.
  apply/subsetP=> h Hh; have Gh := subsetP sHG h Hh; rewrite inE.
  apply/subsetP=> W _; have simW := socle_simple W; have [modW _ _] := simW.
  have simWh: mxsimple rH (socle_base W *m rG h) by apply: Clifford_simple.
  rewrite inE -val_eqE /= PackSocleK eq_sym.
  apply/component_mx_isoP; rewrite ?subgK //; apply: component_mx_iso => //.
  by apply: submx_trans (component_mx_id simW); move/mxmoduleP: modW => ->.
apply/subsetP=> z cHz; have [Gz _] := setIP cHz; rewrite inE.
apply/subsetP=> W _; have simW := socle_simple W; have [modW _ _] := simW.
have simWz: mxsimple rH (socle_base W *m rG z) by apply: Clifford_simple.
rewrite inE -val_eqE /= PackSocleK eq_sym.
by apply/component_mx_isoP; rewrite ?subgK //; apply: Clifford_iso.
Qed.

Lemma Clifford_astab1 (W : sH) : 'C[W | 'Cl] = rstabs rG W.
Proof.
apply/setP=> x; rewrite !inE; apply: andb_id2l => Gx.
rewrite sub1set inE (sameP eqP socleP) !val_Clifford_act //.
rewrite andb_idr // => sWxW; rewrite -mxrank_leqif_sup //.
by rewrite mxrankMfree ?repr_mx_free.
Qed.

Lemma Clifford_rstabs_simple (W : sH) :
  mxsimple (subg_repr rG (rstabs_sub rG W)) W.
Proof.
split => [||U modU sUW nzU]; last 2 [exact: nz_socle].
  by rewrite /mxmodule rstabs_subg setIid.
have modUH: mxmodule rH U.
  apply/mxmoduleP=> h Hh; rewrite (mxmoduleP modU) //.
  rewrite /= -Clifford_astab1 !(inE, sub1set) (subsetP sHG) //.
  rewrite (astab_act (subsetP Clifford_astab h _)) ?inE //=.
  by rewrite mem_gen // inE Hh.
apply: (mxsimple_exists modUH nzU) => [[M simM sMU]].
have [t [x_ /(_ W)[Gx_ defW _]]] := Clifford_component_basis simM.
rewrite -defW; apply/sumsmx_subP=> j _; set x := x_ W j.
have{Gx_} Gx: x \in G by rewrite Gx_.
apply: submx_trans (submxMr _ sMU) _; apply: (mxmoduleP modU).
rewrite inE -val_Clifford_act Gx //; set Wx := 'Cl%act W x.
have [-> //= | neWxW] := eqVneq Wx W.
case: (simM) => _ /negP[]; rewrite -submx0.
rewrite (canF_eq (actKin 'Cl Gx)) in neWxW.
rewrite -(component_mx_disjoint _ _ neWxW); try exact: socle_simple.
rewrite sub_capmx {1}(submx_trans sMU sUW) val_Clifford_act ?groupV //.
by rewrite -(eqmxMr _ defW) sumsmxMr (sumsmx_sup j) ?repr_mxK.
Qed.

End Clifford.

Section JordanHolder.

Variables (gT : finGroupType) (G : {group gT}).
Variables (n : nat) (rG : mx_representation F G n).
Local Notation modG := ((mxmodule rG) n).

Lemma section_module (U V : 'M_n) (modU : modG U) (modV : modG V) :
  mxmodule (factmod_repr modU) <<in_factmod U V>>%MS.
Proof.
by rewrite (eqmx_module _ (genmxE _)) in_factmod_module addsmx_module.
Qed.

Definition section_repr U V (modU : modG U) (modV : modG V) :=
  submod_repr (section_module modU modV).

Lemma mx_factmod_sub U modU :
  mx_rsim (@section_repr U _ modU (mxmodule1 rG)) (factmod_repr modU).
Proof.
exists (val_submod 1%:M) => [||x Gx].
- apply: (@addIn (\rank U)); rewrite genmxE mxrank_in_factmod mxrank_coker.
  by rewrite (addsmx_idPr (submx1 U)) mxrank1 subnK ?rank_leq_row.
- by rewrite /row_free val_submod1.
by rewrite -[_ x]mul1mx -val_submodE val_submodJ.
Qed.

Definition max_submod (U V : 'M_n) :=
  (U < V)%MS /\ (forall W, ~ [/\ modG W, U < W & W < V])%MS.

Lemma max_submodP U V (modU : modG U) (modV : modG V) :
  (U <= V)%MS -> (max_submod U V <-> mx_irreducible (section_repr modU modV)).
Proof.
move=> sUV; split=> [[ltUV maxU] | ].
  apply/mx_irrP; split=> [|WU modWU nzWU].
    by rewrite genmxE lt0n mxrank_eq0 in_factmod_eq0; case/andP: ltUV.
  rewrite -sub1mx -val_submodS val_submod1 genmxE.
  pose W := (U + val_factmod (val_submod WU))%MS.
  suffices sVW: (V <= W)%MS.
    rewrite {2}in_factmodE (submx_trans (submxMr _ sVW)) //.
    rewrite addsmxMr -!in_factmodE val_factmodK.
    by rewrite ((in_factmod U U =P 0) _) ?adds0mx ?in_factmod_eq0.
  move/and3P: {maxU}(maxU W); apply: contraR; rewrite /ltmx addsmxSl => -> /=.
  move: modWU; rewrite /mxmodule rstabs_submod rstabs_factmod => -> /=.
  rewrite addsmx_sub submx_refl -in_factmod_eq0 val_factmodK.
  move: nzWU; rewrite -[_ == 0](inj_eq val_submod_inj) linear0 => ->.
  rewrite -(in_factmodsK sUV) addsmxS // val_factmodS.
  by rewrite -(genmxE (in_factmod U V)) val_submodP.
case/mx_irrP; rewrite lt0n {1}genmxE mxrank_eq0 in_factmod_eq0 => ltUV maxV.
split=> // [|W [modW /andP[sUW ltUW] /andP[sWV /negP[]]]]; first exact/andP.
rewrite -(in_factmodsK sUV) -(in_factmodsK sUW) addsmxS // val_factmodS.
rewrite -genmxE -val_submod1; set VU := <<_>>%MS.
have sW_VU: (in_factmod U W <= VU)%MS.
  by rewrite genmxE -val_factmodS !submxMr.
rewrite -(in_submodK sW_VU) val_submodS -(genmxE (in_submod _ _)).
rewrite sub1mx maxV //.
  rewrite (eqmx_module _ (genmxE _)) in_submod_module ?genmxE ?submxMr //.
  by rewrite in_factmod_module addsmx_module.
rewrite -submx0 [(_ <= 0)%MS]genmxE -val_submodS linear0 in_submodK //.
by rewrite eqmx0 submx0 in_factmod_eq0.
Qed.

Lemma max_submod_eqmx U1 U2 V1 V2 :
  (U1 :=: U2)%MS -> (V1 :=: V2)%MS -> max_submod U1 V1 -> max_submod U2 V2.
Proof.
move=> eqU12 eqV12 [ltUV1 maxU1].
by split=> [|W]; rewrite -(lt_eqmx eqU12) -(lt_eqmx eqV12).
Qed.

Definition mx_subseries := all modG.

Definition mx_composition_series V :=
  mx_subseries V /\ (forall i, i < size V -> max_submod (0 :: V)`_i V`_i).
Local Notation mx_series := mx_composition_series.

Fact mx_subseries_module V i : mx_subseries V -> mxmodule rG V`_i.
Proof.
move=> modV; have [|leVi] := ltnP i (size V); first exact: all_nthP.
by rewrite nth_default ?mxmodule0.
Qed.

Fact mx_subseries_module' V i : mx_subseries V -> mxmodule rG (0 :: V)`_i.
Proof. by move=> modV; rewrite mx_subseries_module //= mxmodule0. Qed.

Definition subseries_repr V i (modV : all modG V) :=
  section_repr (mx_subseries_module' i modV) (mx_subseries_module i modV).

Definition series_repr V i (compV : mx_composition_series V) :=
  subseries_repr i (proj1 compV).

Lemma mx_series_lt V : mx_composition_series V -> path ltmx 0 V.
Proof. by case=> _ compV; apply/(pathP 0)=> i /compV[]. Qed.

Lemma max_size_mx_series (V : seq 'M[F]_n) :
   path ltmx 0 V -> size V <= \rank (last 0 V).
Proof.
rewrite -[size V]addn0 -(mxrank0 F n n); elim: V 0 => //= V1 V IHV V0.
rewrite ltmxErank -andbA => /and3P[_ ltV01 ltV].
by apply: leq_trans (IHV _ ltV); rewrite addSnnS leq_add2l.
Qed.

Lemma mx_series_repr_irr V i (compV : mx_composition_series V) :
  i < size V -> mx_irreducible (series_repr i compV).
Proof.
case: compV => modV compV /compV maxVi; apply/max_submodP => //.
by apply: ltmxW; case: maxVi.
Qed.

Lemma mx_series_rcons U V :
  mx_series (rcons U V) <-> [/\ mx_series U, modG V & max_submod (last 0 U) V].
Proof.
rewrite /mx_series /mx_subseries all_rcons size_rcons -rcons_cons.
split=> [ [/andP[modU modV] maxU] | [[modU maxU] modV maxV]].
  split=> //; last first.
    by have:= maxU _ (leqnn _); rewrite !nth_rcons leqnn ltnn eqxx -last_nth.
  by split=> // i ltiU; have:= maxU i (ltnW ltiU); rewrite !nth_rcons leqW ltiU.
rewrite modV; split=> // i; rewrite !nth_rcons ltnS leq_eqVlt.
case: eqP => [-> _ | /= _ ltiU]; first by rewrite ltnn ?eqxx -last_nth.
by rewrite ltiU; apply: maxU.
Qed.

Theorem mx_Schreier U :
    mx_subseries U -> path ltmx 0 U ->
  classically (exists V, [/\ mx_series V, last 0 V :=: 1%:M & subseq U V])%MS.
Proof.
move: U => U0; set U := {1 2}U0; have: subseq U0 U := subseq_refl U.
pose n' := n.+1; have: n < size U + n' by rewrite leq_addl.
elim: n' U => [|n' IH_U] U ltUn' sU0U modU incU [] // noV.
  rewrite addn0 ltnNge in ltUn'; case/negP: ltUn'.
  by rewrite (leq_trans (max_size_mx_series incU)) ?rank_leq_row.
apply: (noV); exists U; split => //; first split=> // i lt_iU; last first.
  apply/eqmxP; apply: contraT => neU1.
  apply: {IH_U}(IH_U (rcons U 1%:M)) noV.
  - by rewrite size_rcons addSnnS.
  - by rewrite (subseq_trans sU0U) ?subseq_rcons.
  - by rewrite /mx_subseries all_rcons mxmodule1.
  by rewrite rcons_path ltmxEneq neU1 submx1 !andbT.
set U'i := _`_i; set Ui := _`_i; have defU := cat_take_drop i U.
have defU'i: U'i = last 0 (take i U).
  rewrite (last_nth 0) /U'i -{1}defU -cat_cons nth_cat /=.
  by rewrite size_take lt_iU leqnn.
move: incU; rewrite -defU cat_path (drop_nth 0) //= -/Ui -defU'i.
set U' := take i U; set U'' := drop _ U; case/and3P=> incU' ltUi incU''.
split=> // W [modW ltUW ltWV]; case: notF.
apply: {IH_U}(IH_U (U' ++ W :: Ui :: U'')) noV; last 2 first.
- by rewrite /mx_subseries -drop_nth // all_cat /= modW -all_cat defU.
- by rewrite cat_path /= -defU'i; apply/and4P.
- by rewrite -drop_nth // size_cat /= addnS -size_cat defU addSnnS.
by rewrite (subseq_trans sU0U) // -defU cat_subseq // -drop_nth ?subseq_cons.
Qed.

Lemma mx_second_rsim U V (modU : modG U) (modV : modG V) :
  let modI := capmx_module modU modV in let modA := addsmx_module modU modV in
  mx_rsim (section_repr modI modU) (section_repr modV modA).
Proof.
move=> modI modA; set nI := {1}(\rank _).
have sIU := capmxSl U V; have sVA := addsmxSr U V.
pose valI := val_factmod (val_submod (1%:M : 'M_nI)).
have UvalI: (valI <= U)%MS.
  rewrite -(addsmx_idPr sIU) (submx_trans _ (proj_factmodS _ _)) //.
  by rewrite submxMr // val_submod1 genmxE.
exists (valI *m in_factmod _ 1%:M *m in_submod _ 1%:M) => [||x Gx].
- apply: (@addIn (\rank (U :&: V) + \rank V)%N); rewrite genmxE addnA addnCA.
  rewrite /nI genmxE !{1}mxrank_in_factmod 2?(addsmx_idPr _) //.
  by rewrite -mxrank_sum_cap addnC.
- rewrite -kermx_eq0; apply/rowV0P=> u; rewrite (sameP sub_kermxP eqP).
  rewrite mulmxA -in_submodE mulmxA -in_factmodE -(inj_eq val_submod_inj).
  rewrite linear0 in_submodK ?in_factmod_eq0 => [Vvu|]; last first.
    by rewrite genmxE addsmxC in_factmod_addsK submxMr // mulmx_sub.
  apply: val_submod_inj; apply/eqP; rewrite linear0 -[val_submod u]val_factmodK.
  rewrite val_submodE val_factmodE -mulmxA -val_factmodE -/valI.
  by rewrite in_factmod_eq0 sub_capmx mulmx_sub.
symmetry; rewrite -{1}in_submodE -{1}in_submodJ; last first.
   by rewrite genmxE addsmxC in_factmod_addsK -in_factmodE submxMr.
rewrite -{1}in_factmodE -{1}in_factmodJ // mulmxA in_submodE; congr (_ *m _).
apply/eqP; rewrite mulmxA -in_factmodE -subr_eq0 -linearB in_factmod_eq0.
apply: submx_trans (capmxSr U V); rewrite -in_factmod_eq0 linearB /=.
rewrite subr_eq0 {1}(in_factmodJ modI) // val_factmodK eq_sym.
rewrite /valI val_factmodE mulmxA -val_factmodE val_factmodK.
by rewrite -[submod_mx _ _]mul1mx -val_submodE val_submodJ.
Qed.

Lemma section_eqmx_add U1 U2 V1 V2 modU1 modU2 modV1 modV2 :
    (U1 :=: U2)%MS -> (U1 + V1 :=: U2 + V2)%MS ->
  mx_rsim (@section_repr U1 V1 modU1 modV1) (@section_repr U2 V2 modU2 modV2).
Proof.
move=> eqU12 eqV12; set n1 := {1}(\rank _).
pose v1 := val_factmod (val_submod (1%:M : 'M_n1)).
have sv12: (v1 <= U2 + V2)%MS.
  rewrite -eqV12 (submx_trans _ (proj_factmodS _ _)) //.
  by rewrite submxMr // val_submod1 genmxE.
exists (v1 *m in_factmod _ 1%:M *m in_submod _ 1%:M) => [||x Gx].
- apply: (@addIn (\rank U1)); rewrite {2}eqU12 /n1 !{1}genmxE.
  by rewrite !{1}mxrank_in_factmod eqV12.
- rewrite -kermx_eq0; apply/rowV0P=> u; rewrite (sameP sub_kermxP eqP) mulmxA.
  rewrite -in_submodE mulmxA -in_factmodE -(inj_eq val_submod_inj) linear0.
  rewrite in_submodK ?in_factmod_eq0 -?eqU12 => [U1uv1|]; last first.
    by rewrite genmxE -(in_factmod_addsK U2 V2) submxMr // mulmx_sub.
  apply: val_submod_inj; apply/eqP; rewrite linear0 -[val_submod _]val_factmodK.
  by rewrite in_factmod_eq0 val_factmodE val_submodE -mulmxA -val_factmodE.
symmetry; rewrite -{1}in_submodE -{1}in_factmodE -{1}in_submodJ; last first.
  by rewrite genmxE -(in_factmod_addsK U2 V2) submxMr.
rewrite -{1}in_factmodJ // mulmxA in_submodE; congr (_ *m _); apply/eqP.
rewrite mulmxA -in_factmodE -subr_eq0 -linearB in_factmod_eq0 -eqU12.
rewrite -in_factmod_eq0 linearB /= subr_eq0 {1}(in_factmodJ modU1) //.
rewrite val_factmodK /v1 val_factmodE eq_sym mulmxA -val_factmodE val_factmodK.
by rewrite -[_ *m _]mul1mx mulmxA -val_submodE val_submodJ.
Qed.

Lemma section_eqmx U1 U2 V1 V2 modU1 modU2 modV1 modV2
                   (eqU : (U1 :=: U2)%MS) (eqV : (V1 :=: V2)%MS) : 
  mx_rsim (@section_repr U1 V1 modU1 modV1) (@section_repr U2 V2 modU2 modV2).
Proof. by apply: section_eqmx_add => //; apply: adds_eqmx. Qed.

Lemma mx_butterfly U V W modU modV modW :
    ~~ (U == V)%MS -> max_submod U W -> max_submod V W ->
  let modUV := capmx_module modU modV in 
     max_submod (U :&: V)%MS U
  /\ mx_rsim (@section_repr V W modV modW) (@section_repr _ U modUV modU).
Proof.
move=> neUV maxU maxV modUV; have{neUV maxU} defW: (U + V :=: W)%MS.
  wlog{neUV modUV} ltUV: U V modU modV maxU maxV / ~~ (V <= U)%MS.
    by case/nandP: neUV => ?; first rewrite addsmxC; apply.
  apply/eqmxP/idPn=> neUVW; case: maxU => ltUW; case/(_ (U + V)%MS).
  rewrite addsmx_module // ltmxE ltmxEneq neUVW addsmxSl !addsmx_sub.
  by have [ltVW _] := maxV; rewrite submx_refl andbT ltUV !ltmxW.
have sUV_U := capmxSl U V; have sVW: (V <= W)%MS by rewrite -defW addsmxSr.
set goal := mx_rsim _ _; suffices{maxV} simUV: goal.
  split=> //; apply/(max_submodP modUV modU sUV_U).
  by apply: mx_rsim_irr simUV _; apply/max_submodP.
apply: {goal}mx_rsim_sym.
by apply: mx_rsim_trans (mx_second_rsim modU modV) _; apply: section_eqmx.
Qed.

Lemma mx_JordanHolder_exists U V :
    mx_composition_series U -> modG V -> max_submod V (last 0 U) ->
  {W : seq 'M_n | mx_composition_series W & last 0 W = V}.
Proof.
elim/last_ind: U V => [|U Um IHU] V compU modV; first by case; rewrite ltmx0.
rewrite last_rcons => maxV; case/mx_series_rcons: compU => compU modUm maxUm.
case eqUV: (last 0 U == V)%MS.
  case/lastP: U eqUV compU {maxUm IHU} => [|U' Um'].
    by rewrite andbC; move/eqmx0P->; exists [::].
  rewrite last_rcons; move/eqmxP=> eqU'V; case/mx_series_rcons=> compU _ maxUm'.
  exists (rcons U' V); last by rewrite last_rcons.
  by apply/mx_series_rcons; split => //; apply: max_submod_eqmx maxUm'.
set Um' := last 0 U in maxUm eqUV; have [modU _] := compU.
have modUm': modG Um' by rewrite /Um' (last_nth 0) mx_subseries_module'.
have [|||W compW lastW] := IHU (V :&: Um')%MS; rewrite ?capmx_module //.
  by case: (mx_butterfly modUm' modV modUm); rewrite ?eqUV // {1}capmxC.
exists (rcons W V); last by rewrite last_rcons.
apply/mx_series_rcons; split; rewrite // lastW.
by case: (mx_butterfly modV modUm' modUm); rewrite // andbC eqUV.
Qed.

Let rsim_rcons U V compU compUV i : i < size U ->
  mx_rsim (@series_repr U i compU) (@series_repr (rcons U V) i compUV).
Proof.
by move=> ltiU; apply: section_eqmx; rewrite -?rcons_cons nth_rcons ?leqW ?ltiU.
Qed.

Let last_mod U (compU : mx_series U) : modG (last 0 U).
Proof.
by case: compU => modU _; rewrite (last_nth 0) (mx_subseries_module' _ modU).
Qed.

Let rsim_last U V modUm modV compUV :
  mx_rsim (@section_repr (last 0 U) V modUm modV)
          (@series_repr (rcons U V) (size U) compUV).
Proof.
apply: section_eqmx; last by rewrite nth_rcons ltnn eqxx.
by rewrite -rcons_cons nth_rcons leqnn -last_nth.
Qed.
Local Notation rsimT := mx_rsim_trans.
Local Notation rsimC := mx_rsim_sym.

Lemma mx_JordanHolder U V compU compV :
  let m := size U in (last 0 U :=: last 0 V)%MS -> 
  m = size V  /\ (exists p : 'S_m, forall i : 'I_m,
     mx_rsim (@series_repr U i compU) (@series_repr V (p i) compV)).
Proof.
elim: {U}(size U) {-2}U V (eqxx (size U)) compU compV => /= [|r IHr] U V.
  move/nilP->; case/lastP: V => [|V Vm] /= ? compVm; rewrite ?last_rcons => Vm0.
    by split=> //; exists 1%g; case.
  by case/mx_series_rcons: (compVm) => _ _ []; rewrite -(lt_eqmx Vm0) ltmx0.
case/lastP: U => // [U Um]; rewrite size_rcons eqSS => szUr compUm.
case/mx_series_rcons: (compUm); set Um' := last 0 U => compU modUm maxUm.
case/lastP: V => [|V Vm] compVm; rewrite ?last_rcons ?size_rcons /= => eqUVm.
  by case/mx_series_rcons: (compUm) => _ _ []; rewrite (lt_eqmx eqUVm) ltmx0.
case/mx_series_rcons: (compVm); set Vm' := last 0 V => compV modVm maxVm.
have [modUm' modVm']: modG Um' * modG Vm' := (last_mod compU, last_mod compV).
pose i_m := @ord_max (size U).
have [eqUVm' | neqUVm'] := altP (@eqmxP _ _ _ _ Um' Vm').
  have [szV [p sim_p]] := IHr U V szUr compU compV eqUVm'.
  split; first by rewrite szV.
  exists (lift_perm i_m i_m p) => i; case: (unliftP i_m i) => [j|] ->{i}.
    apply: rsimT (rsimC _) (rsimT (sim_p j) _).
      by rewrite lift_max; apply: rsim_rcons.
    by rewrite lift_perm_lift lift_max; apply: rsim_rcons; rewrite -szV.
  have simUVm := section_eqmx modUm' modVm' modUm modVm eqUVm' eqUVm.
  apply: rsimT (rsimC _) (rsimT simUVm _); first exact: rsim_last.
  by rewrite lift_perm_id /= szV; apply: rsim_last.
have maxVUm: max_submod Vm' Um by apply: max_submod_eqmx (eqmx_sym _) maxVm.
have:= mx_butterfly modUm' modVm' modUm neqUVm' maxUm maxVUm.
move: (capmx_module _ _); set Wm := (Um' :&: Vm')%MS => modWm [maxWUm simWVm].
have:= mx_butterfly modVm' modUm' modUm _ maxVUm maxUm.
move: (capmx_module _ _); rewrite andbC capmxC -/Wm => modWmV [// | maxWVm].
rewrite {modWmV}(bool_irrelevance modWmV modWm) => simWUm.
have [W compW lastW] := mx_JordanHolder_exists compU modWm maxWUm.
have compWU: mx_series (rcons W Um') by apply/mx_series_rcons; rewrite lastW.
have compWV: mx_series (rcons W Vm') by apply/mx_series_rcons; rewrite lastW.
have [|szW [pU pUW]] := IHr U _ szUr compU compWU; first by rewrite last_rcons.
rewrite size_rcons in szW; have ltWU: size W < size U by rewrite -szW.
have{IHr} := IHr _ V _ compWV compV; rewrite last_rcons size_rcons -szW.
case=> {r szUr}// szV [pV pWV]; split; first by rewrite szV.
pose j_m := Ordinal ltWU; pose i_m' := lift i_m j_m.
exists (lift_perm i_m i_m pU * tperm i_m i_m' * lift_perm i_m i_m pV)%g => i.
rewrite !permM; case: (unliftP i_m i) => [j {simWUm}|] ->{i}; last first.
  rewrite lift_perm_id tpermL lift_perm_lift lift_max {simWVm}.
  apply: rsimT (rsimT (pWV j_m) _); last by apply: rsim_rcons; rewrite -szV.
  apply: rsimT (rsimC _) {simWUm}(rsimT simWUm _); first exact: rsim_last.
  by rewrite -lastW in modWm *; apply: rsim_last.
apply: rsimT (rsimC _) {pUW}(rsimT (pUW j) _).
  by rewrite lift_max; apply: rsim_rcons.
rewrite lift_perm_lift; case: (unliftP j_m (pU j)) => [k|] ->{j pU}.
  rewrite tpermD ?(inj_eq lift_inj) ?neq_lift //.
  rewrite lift_perm_lift !lift_max; set j := lift j_m k.
  have ltjW: j < size W by have:= ltn_ord k; rewrite -(lift_max k) /= {1 3}szW.
  apply: rsimT (rsimT (pWV j) _); last by apply: rsim_rcons; rewrite -szV.
  by apply: rsimT (rsimC _) (rsim_rcons compW _ _); first apply: rsim_rcons.
apply: rsimT {simWVm}(rsimC (rsimT simWVm _)) _.
  by rewrite -lastW in modWm *; apply: rsim_last.
rewrite tpermR lift_perm_id /= szV.
by apply: rsimT (rsim_last modVm' modVm _); apply: section_eqmx.
Qed.

Lemma mx_JordanHolder_max U (m := size U) V compU modV :
    (last 0 U :=: 1%:M)%MS -> mx_irreducible (@factmod_repr _ G n rG V modV) ->
  exists i : 'I_m, mx_rsim (factmod_repr modV) (@series_repr U i compU).
Proof.
rewrite {}/m; set Um := last 0 U => Um1 irrV.
have modUm: modG Um := last_mod compU; have simV := rsimC (mx_factmod_sub modV).
have maxV: max_submod V Um.
  move/max_submodP: (mx_rsim_irr simV irrV) => /(_ (submx1 _)).
  by apply: max_submod_eqmx; last apply: eqmx_sym.
have [W compW lastW] := mx_JordanHolder_exists compU modV maxV.
have compWU: mx_series (rcons W Um) by apply/mx_series_rcons; rewrite lastW.
have:= mx_JordanHolder compU compWU; rewrite last_rcons size_rcons.
case=> // szW [p pUW]; have ltWU: size W < size U by rewrite szW.
pose i := Ordinal ltWU; exists ((p^-1)%g i).
apply: rsimT simV (rsimT _ (rsimC (pUW _))); rewrite permKV.
apply: rsimT (rsimC _) (rsim_last (last_mod compW) modUm _).
by apply: section_eqmx; rewrite ?lastW.
Qed.

End JordanHolder.

Bind Scope irrType_scope with socle_sort.

Section Regular.

Variables (gT : finGroupType) (G : {group gT}).
Local Notation nG := #|pred_of_set (gval G)|.

Local Notation rF := (GRing.Field.comUnitRingType F) (only parsing).
Local Notation aG := (regular_repr rF G).
Local Notation R_G := (group_ring rF G).

Lemma gring_free : row_free R_G.
Proof.
apply/row_freeP; exists (lin1_mx (row (gring_index G 1) \o vec_mx)).
apply/row_matrixP=> i; rewrite row_mul rowK mul_rV_lin1 /= mxvecK rowK row1.
by rewrite gring_indexK // mul1g gring_valK.
Qed.

Lemma gring_op_id A : (A \in R_G)%MS -> gring_op aG A = A.
Proof.
case/envelop_mxP=> a ->{A}; rewrite linear_sum.
by apply: eq_bigr => x Gx; rewrite linearZ /= gring_opG.
Qed.

Lemma gring_rowK A : (A \in R_G)%MS -> gring_mx aG (gring_row A) = A.
Proof. exact: gring_op_id. Qed.

Lemma mem_gring_mx m a (M : 'M_(m, nG)) :
  (gring_mx aG a \in M *m R_G)%MS = (a <= M)%MS.
Proof. by rewrite vec_mxK submxMfree ?gring_free. Qed.

Lemma mem_sub_gring m A (M : 'M_(m, nG)) :
  (A \in M *m R_G)%MS = (A \in R_G)%MS && (gring_row A <= M)%MS.
Proof.
rewrite -(andb_idl (memmx_subP (submxMl _ _) A)); apply: andb_id2l => R_A.
by rewrite -mem_gring_mx gring_rowK.
Qed.

Section GringMx.

Variables (n : nat) (rG : mx_representation F G n).

Lemma gring_mxP a : (gring_mx rG a \in enveloping_algebra_mx rG)%MS.
Proof. by rewrite vec_mxK submxMl. Qed.

Lemma gring_opM A B :
  (B \in R_G)%MS -> gring_op rG (A *m B) = gring_op rG A *m gring_op rG B.
Proof. by move=> R_B; rewrite -gring_opJ gring_rowK. Qed.

Hypothesis irrG : mx_irreducible rG.

Lemma rsim_regular_factmod :
  {U : 'M_nG & {modU : mxmodule aG U & mx_rsim rG (factmod_repr modU)}}.
Proof.
pose v : 'rV[F]_n := nz_row 1%:M.
pose fU := lin1_mx (mulmx v \o gring_mx rG); pose U := kermx fU.
have modU: mxmodule aG U.
  apply/mxmoduleP => x Gx; apply/sub_kermxP/row_matrixP=> i.
  rewrite 2!row_mul row0; move: (row i U) (sub_kermxP (row_sub i U)) => u.
  by rewrite !mul_rV_lin1 /= gring_mxJ // mulmxA => ->; rewrite mul0mx.
have def_n: \rank (cokermx U) = n.
  apply/eqP; rewrite mxrank_coker mxrank_ker subKn ?rank_leq_row // -genmxE.
  rewrite -[_ == _]sub1mx; have [_ _ ->] := irrG; rewrite ?submx1 //.
    rewrite (eqmx_module _ (genmxE _)); apply/mxmoduleP=> x Gx.
    apply/row_subP=> i; apply: eq_row_sub (gring_index G (enum_val i * x)) _.
    rewrite !rowE mulmxA !mul_rV_lin1 /= -mulmxA -gring_mxJ //.
    by rewrite -rowE rowK.
  rewrite (eqmx_eq0 (genmxE _)); apply/rowV0Pn.
  exists v; last exact: (nz_row_mxsimple irrG).
  apply/submxP; exists (gring_row (aG 1%g)); rewrite mul_rV_lin1 /=.
  by rewrite -gring_opE gring_opG // repr_mx1 mulmx1.
exists U; exists modU; apply: mx_rsim_sym.
exists (val_factmod 1%:M *m fU) => // [|x Gx].
  rewrite /row_free eqn_leq rank_leq_row /= -subn_eq0 -mxrank_ker mxrank_eq0.
  apply/rowV0P=> u /sub_kermxP; rewrite mulmxA => /sub_kermxP.
  by rewrite -/U -in_factmod_eq0 mulmxA mulmx1 val_factmodK => /eqP.
rewrite mulmxA -val_factmodE (canRL (addKr _) (add_sub_fact_mod U _)).
rewrite mulmxDl mulNmx (sub_kermxP (val_submodP _)) oppr0 add0r.
apply/row_matrixP=> i; move: (val_factmod _) => zz.
by rewrite !row_mul !mul_rV_lin1 /= gring_mxJ // mulmxA.
Qed.

Lemma rsim_regular_series U (compU : mx_composition_series aG U) :
    (last 0 U :=: 1%:M)%MS ->
  exists i : 'I_(size U), mx_rsim rG (series_repr i compU).
Proof.
move=> lastU; have [V [modV simGV]] := rsim_regular_factmod.
have irrV := mx_rsim_irr simGV irrG.
have [i simVU] := mx_JordanHolder_max compU lastU irrV.
by exists i; apply: mx_rsim_trans simGV simVU.
Qed.

Hypothesis F'G : [char F]^'.-group G.

Lemma rsim_regular_submod :
  {U : 'M_nG & {modU : mxmodule aG U & mx_rsim rG (submod_repr modU)}}.
Proof.
have [V [modV eqG'V]] := rsim_regular_factmod.
have [U modU defVU dxVU] := mx_Maschke F'G modV (submx1 V).
exists U; exists modU; apply: mx_rsim_trans eqG'V _.
by apply: mx_rsim_factmod; rewrite ?mxdirectE /= addsmxC // addnC.
Qed.

End GringMx.

Definition gset_mx (A : {set gT}) := \sum_(x in A) aG x.

Local Notation tG := #|pred_of_set (classes (gval G))|.

Definition classg_base := \matrix_(k < tG) mxvec (gset_mx (enum_val k)).

Let groupCl : {in G, forall x, {subset x ^: G <= G}}.
Proof. by move=> x Gx; apply: subsetP; apply: class_subG. Qed.

Lemma classg_base_free : row_free classg_base.
Proof.
rewrite -kermx_eq0; apply/rowV0P=> v /sub_kermxP; rewrite mulmx_sum_row => v0.
apply/rowP=> k; rewrite mxE.
have [x Gx def_k] := imsetP (enum_valP k).
transitivity (@gring_proj F _ G x (vec_mx 0) 0 0); last first.
  by rewrite !linear0 !mxE.
rewrite -{}v0 !linear_sum (bigD1 k) //= !linearZ /= rowK mxvecK def_k.
rewrite linear_sum (bigD1 x) ?class_refl //= gring_projE // eqxx.
rewrite !big1 ?addr0 ?mxE ?mulr1 // => [k' | y /andP[xGy ne_yx]]; first 1 last.
  by rewrite gring_projE ?(groupCl Gx xGy) // eq_sym (negPf ne_yx).
rewrite rowK !linearZ /= mxvecK -(inj_eq enum_val_inj) def_k eq_sym.
have [z Gz ->] := imsetP (enum_valP k').
move/eqP=> not_Gxz; rewrite linear_sum big1 ?scaler0 //= => y zGy.
rewrite gring_projE ?(groupCl Gz zGy) //.
by case: eqP zGy => // <- /class_eqP.
Qed.

Lemma classg_base_center : (classg_base :=: 'Z(R_G))%MS.
Proof.
apply/eqmxP/andP; split.
  apply/row_subP=> k; rewrite rowK /gset_mx sub_capmx {1}linear_sum.
  have [x Gx ->{k}] := imsetP (enum_valP k); have sxGG := groupCl Gx.
  rewrite summx_sub => [|y xGy]; last by rewrite envelop_mx_id ?sxGG.
  rewrite memmx_cent_envelop; apply/centgmxP=> y Gy.
  rewrite {2}(reindex_acts 'J _ Gy) ?astabsJ ?class_norm //=.
  rewrite mulmx_suml mulmx_sumr; apply: eq_bigr => z; move/sxGG=> Gz.
  by rewrite -!repr_mxM ?groupJ -?conjgC.
apply/memmx_subP=> A; rewrite sub_capmx memmx_cent_envelop.
case/andP=> /envelop_mxP[a ->{A}] cGa.
rewrite (partition_big_imset (class^~ G)) -/(classes G) /=.
rewrite linear_sum summx_sub //= => xG GxG; have [x Gx def_xG] := imsetP GxG.
apply: submx_trans (scalemx_sub (a x) (submx_refl _)).
rewrite (eq_row_sub (enum_rank_in GxG xG)) // linearZ /= rowK enum_rankK_in //.
rewrite !linear_sum {xG GxG}def_xG; apply: eq_big  => [y | xy] /=.
  apply/idP/andP=> [| [_ xGy]]; last by rewrite -(eqP xGy) class_refl.
  by case/imsetP=> z Gz ->; rewrite groupJ // classGidl.
case/imsetP=> y Gy ->{xy}; rewrite linearZ; congr (_ *: _).
move/(canRL (repr_mxK aG Gy)): (centgmxP cGa y Gy); have Gy' := groupVr Gy.
move/(congr1 (gring_proj x)); rewrite -mulmxA mulmx_suml !linear_sum.
rewrite (bigD1 x Gx) big1 => [|z /andP[Gz]]; rewrite !linearZ /=; last first.
  by rewrite eq_sym gring_projE // => /negPf->; rewrite scaler0.
rewrite gring_projE // eqxx scalemx1 (bigD1 (x ^ y)%g) ?groupJ //=.
rewrite big1 => [|z /andP[Gz]]; rewrite -scalemxAl !linearZ /=.
  rewrite !addr0 -!repr_mxM ?groupM // mulgA mulKVg mulgK => /rowP/(_ 0).
  by rewrite gring_projE // eqxx scalemx1 !mxE.
rewrite eq_sym -(can_eq (conjgKV y)) conjgK conjgE invgK.
by rewrite -!repr_mxM ?gring_projE ?groupM // => /negPf->; rewrite scaler0.
Qed.

Lemma regular_module_ideal m (M : 'M_(m, nG)) :
  mxmodule aG M = right_mx_ideal R_G (M *m R_G).
Proof.
apply/idP/idP=> modM.
  apply/mulsmx_subP=> A B; rewrite !mem_sub_gring => /andP[R_A M_A] R_B.
  by rewrite envelop_mxM // gring_row_mul (mxmodule_envelop modM).
apply/mxmoduleP=> x Gx; apply/row_subP=> i; rewrite row_mul -mem_gring_mx.
rewrite gring_mxJ // (mulsmx_subP modM) ?envelop_mx_id //.
by rewrite mem_gring_mx row_sub.
Qed.

Definition irrType := socleType aG.
Identity Coercion type_of_irrType : irrType >-> socleType.

Variable sG : irrType.

Definition irr_degree (i : sG) := \rank (socle_base i).
Local Notation "'n_ i" := (irr_degree i) : group_ring_scope.
Local Open Scope group_ring_scope.

Lemma irr_degreeE i : 'n_i = \rank (socle_base i). Proof. by []. Qed.
Lemma irr_degree_gt0 i : 'n_i > 0.
Proof. by rewrite lt0n mxrank_eq0; case: (socle_simple i). Qed.

Definition irr_repr i : mx_representation F G 'n_i := socle_repr i.
Lemma irr_reprE i x : irr_repr i x = submod_mx (socle_module i) x.
Proof. by []. Qed.

Lemma rfix_regular : (rfix_mx aG G :=: gring_row (gset_mx G))%MS.
Proof.
apply/eqmxP/andP; split; last first.
  apply/rfix_mxP => x Gx; rewrite -gring_row_mul; congr gring_row.
  rewrite {2}/gset_mx (reindex_astabs 'R x) ?astabsR //= mulmx_suml.
  by apply: eq_bigr => y Gy; rewrite repr_mxM.
apply/rV_subP=> v /rfix_mxP cGv.
have /envelop_mxP[a def_v]: (gring_mx aG v \in R_G)%MS.
  by rewrite vec_mxK submxMl.
suffices ->: v = a 1%g *: gring_row (gset_mx G) by rewrite scalemx_sub.
rewrite -linearZ  scaler_sumr -[v]gring_mxK def_v; congr (gring_row _).
apply: eq_bigr => x Gx; congr (_ *: _).
move/rowP/(_ 0): (congr1 (gring_proj x \o gring_mx aG) (cGv x Gx)).
rewrite /= gring_mxJ // def_v mulmx_suml !linear_sum (bigD1 1%g) //=.
rewrite repr_mx1 -scalemxAl mul1mx linearZ /= gring_projE // eqxx scalemx1.
rewrite big1 ?addr0 ?mxE /= => [ | y /andP[Gy nt_y]]; last first.
  rewrite -scalemxAl linearZ -repr_mxM //= gring_projE ?groupM //.
  by rewrite eq_sym eq_mulgV1 mulgK (negPf nt_y) scaler0.
rewrite (bigD1 x) //= linearZ /= gring_projE // eqxx scalemx1.
rewrite big1 ?addr0 ?mxE // => y /andP[Gy ne_yx].
by rewrite linearZ /= gring_projE // eq_sym (negPf ne_yx) scaler0.
Qed.

Lemma principal_comp_subproof : mxsimple aG (rfix_mx aG G).
Proof.
apply: linear_mxsimple; first exact: rfix_mx_module.
apply/eqP; rewrite rfix_regular eqn_leq rank_leq_row lt0n mxrank_eq0.
apply/eqP => /(congr1 (gring_proj 1 \o gring_mx aG)); apply/eqP.
rewrite /= -[gring_mx _ _]/(gring_op _ _) !linear0 !linear_sum (bigD1 1%g) //=.
rewrite gring_opG ?gring_projE // eqxx big1 ?addr0 ?oner_eq0 // => x.
by case/andP=> Gx nt_x; rewrite gring_opG // gring_projE // eq_sym (negPf nt_x).
Qed.

Fact principal_comp_key : unit. Proof. by []. Qed.
Definition principal_comp_def :=
  PackSocle (component_socle sG principal_comp_subproof).
Definition principal_comp := locked_with principal_comp_key principal_comp_def.
Local Notation "1" := principal_comp : irrType_scope.

Lemma irr1_rfix : (1%irr :=: rfix_mx aG G)%MS.
Proof.
rewrite [1%irr]unlock PackSocleK; apply/eqmxP.
rewrite (component_mx_id principal_comp_subproof) andbT.
have [I [W isoW ->]] := component_mx_def principal_comp_subproof.
apply/sumsmx_subP=> i _; have [f _ hom_f <-]:= isoW i.
by apply/rfix_mxP=> x Gx; rewrite -(hom_mxP hom_f) // (rfix_mxP G _).
Qed.

Lemma rank_irr1 : \rank 1%irr = 1%N.
Proof.
apply/eqP; rewrite eqn_leq lt0n mxrank_eq0 nz_socle andbT.
by rewrite irr1_rfix rfix_regular rank_leq_row.
Qed.

Lemma degree_irr1 : 'n_1 = 1%N.
Proof.
apply/eqP; rewrite eqn_leq irr_degree_gt0 -rank_irr1.
by rewrite mxrankS ?component_mx_id //; apply: socle_simple.
Qed.

Definition Wedderburn_subring (i : sG) := <<i *m R_G>>%MS.

Local Notation "''R_' i" := (Wedderburn_subring i) : group_ring_scope.

Let sums_R : (\sum_i 'R_i :=: Socle sG *m R_G)%MS.
Proof.
apply/eqmxP; set R_S := (_ <= _)%MS.
have sRS: R_S by apply/sumsmx_subP=> i; rewrite genmxE submxMr ?(sumsmx_sup i).
rewrite sRS -(mulmxKpV sRS) mulmxA submxMr //; apply/sumsmx_subP=> i _.
rewrite -(submxMfree _ _ gring_free) -(mulmxA _ _ R_G) mulmxKpV //.
by rewrite (sumsmx_sup i) ?genmxE.
Qed.

Lemma Wedderburn_ideal i : mx_ideal R_G 'R_i.
Proof.
apply/andP; split; last first.
  rewrite /right_mx_ideal genmxE (muls_eqmx (genmxE _) (eqmx_refl _)).
  by rewrite -[(_ <= _)%MS]regular_module_ideal component_mx_module.
apply/mulsmx_subP=> A B R_A; rewrite !genmxE !mem_sub_gring => /andP[R_B SiB].
rewrite envelop_mxM {R_A}// gring_row_mul -{R_B}(gring_rowK R_B).
pose f := mulmx (gring_row A) \o gring_mx aG.
rewrite -[_ *m _](mul_rV_lin1 [linear of f]).
suffices: (i *m lin1_mx f <= i)%MS by apply: submx_trans; rewrite submxMr.
apply: hom_component_mx; first exact: socle_simple.
apply/rV_subP=> v _; apply/hom_mxP=> x Gx.
by rewrite !mul_rV_lin1 /f /= gring_mxJ ?mulmxA.
Qed.

Lemma Wedderburn_direct : mxdirect (\sum_i 'R_i)%MS.
Proof.
apply/mxdirectP; rewrite /= sums_R mxrankMfree ?gring_free //.
rewrite (mxdirectP (Socle_direct sG)); apply: eq_bigr=> i _ /=.
by rewrite genmxE mxrankMfree ?gring_free.
Qed.

Lemma Wedderburn_disjoint i j : i != j -> ('R_i :&: 'R_j)%MS = 0.
Proof.
move=> ne_ij; apply/eqP; rewrite -submx0 capmxC.
by rewrite -(mxdirect_sumsP Wedderburn_direct j) // capmxS // (sumsmx_sup i).
Qed.

Lemma Wedderburn_annihilate i j : i != j -> ('R_i * 'R_j)%MS = 0.
Proof.
move=> ne_ij; apply/eqP; rewrite -submx0 -(Wedderburn_disjoint ne_ij).
rewrite sub_capmx; apply/andP; split.
  case/andP: (Wedderburn_ideal i) => _; apply: submx_trans.
  by rewrite mulsmxS // genmxE submxMl.
case/andP: (Wedderburn_ideal j) => idlRj _; apply: submx_trans idlRj.
by rewrite mulsmxS // genmxE submxMl.
Qed.

Lemma Wedderburn_mulmx0 i j A B :
  i != j -> (A \in 'R_i)%MS -> (B \in 'R_j)%MS -> A *m B = 0.
Proof.
move=> ne_ij RiA RjB; apply: memmx0.
by rewrite -(Wedderburn_annihilate ne_ij) mem_mulsmx.
Qed.

Hypothesis F'G : [char F]^'.-group G.

Lemma irr_mx_sum : (\sum_(i : sG) i = 1%:M)%MS.
Proof. by apply: reducible_Socle1; apply: mx_Maschke. Qed.
 
Lemma Wedderburn_sum : (\sum_i 'R_i :=: R_G)%MS.
Proof. by apply: eqmx_trans sums_R _; rewrite /Socle irr_mx_sum mul1mx. Qed.

Definition Wedderburn_id i :=
  vec_mx (mxvec 1%:M *m proj_mx 'R_i (\sum_(j | j != i) 'R_j)%MS).

Local Notation "''e_' i" := (Wedderburn_id i) : group_ring_scope.

Lemma Wedderburn_sum_id : \sum_i 'e_i = 1%:M.
Proof.
rewrite -linear_sum; apply: canLR mxvecK _.
have: (1%:M \in R_G)%MS := envelop_mx1 aG.
rewrite -Wedderburn_sum; case/(sub_dsumsmx Wedderburn_direct) => e Re -> _.
apply: eq_bigr => i _; have dxR := mxdirect_sumsP Wedderburn_direct i (erefl _).
rewrite (bigD1 i) // mulmxDl proj_mx_id ?Re // proj_mx_0 ?addr0 //=.
by rewrite summx_sub // => j ne_ji; rewrite (sumsmx_sup j) ?Re.
Qed.

Lemma Wedderburn_id_mem i : ('e_i \in 'R_i)%MS.
Proof. by rewrite vec_mxK proj_mx_sub. Qed.

Lemma Wedderburn_is_id i : mxring_id 'R_i 'e_i.
Proof.
have ideRi A: (A \in 'R_i)%MS -> 'e_i *m A = A.
  move=> RiA; rewrite -{2}[A]mul1mx -Wedderburn_sum_id mulmx_suml.
  rewrite (bigD1 i) //= big1 ?addr0 // => j ne_ji.
  by rewrite (Wedderburn_mulmx0 ne_ji) ?Wedderburn_id_mem.
  split=> // [||A RiA]; first 2 [exact: Wedderburn_id_mem].
  apply: contraNneq (nz_socle i) => e0.
  apply/rowV0P=> v; rewrite -mem_gring_mx -(genmxE (i *m _)) => /ideRi.
  by rewrite e0 mul0mx => /(canLR gring_mxK); rewrite linear0.
rewrite -{2}[A]mulmx1 -Wedderburn_sum_id mulmx_sumr (bigD1 i) //=.
rewrite big1 ?addr0 // => j; rewrite eq_sym => ne_ij.
by rewrite (Wedderburn_mulmx0 ne_ij) ?Wedderburn_id_mem.
Qed.

Lemma Wedderburn_closed i : ('R_i * 'R_i = 'R_i)%MS.
Proof.
rewrite -{3}['R_i]genmx_id -/'R_i -genmx_muls; apply/genmxP.
have [idlRi idrRi] := andP (Wedderburn_ideal i).
apply/andP; split.
  by apply: submx_trans idrRi; rewrite mulsmxS // genmxE submxMl.
have [_ Ri_e ideRi _] := Wedderburn_is_id i.
by apply/memmx_subP=> A RiA; rewrite -[A]ideRi ?mem_mulsmx.
Qed.

Lemma Wedderburn_is_ring i : mxring 'R_i.
Proof.
rewrite /mxring /left_mx_ideal Wedderburn_closed submx_refl.
by apply/mxring_idP; exists 'e_i; apply: Wedderburn_is_id.
Qed.

Lemma Wedderburn_min_ideal m i (E : 'A_(m, nG)) :
  E != 0 -> (E <= 'R_i)%MS -> mx_ideal R_G E -> (E :=: 'R_i)%MS.
Proof.
move=> nzE sE_Ri /andP[idlE idrE]; apply/eqmxP; rewrite sE_Ri.
pose M := E *m pinvmx R_G; have defE: E = M *m R_G.
  by rewrite mulmxKpV // (submx_trans sE_Ri) // genmxE submxMl.
have modM: mxmodule aG M by rewrite regular_module_ideal -defE.
have simSi := socle_simple i; set Si := socle_base i in simSi.
have [I [W isoW defW]]:= component_mx_def simSi.
rewrite /'R_i /socle_val /= defW genmxE defE submxMr //.
apply/sumsmx_subP=> j _.
have simW := mx_iso_simple (isoW j) simSi; have [modW _ minW] := simW.
have [{minW}dxWE | nzWE] := eqVneq (W j :&: M)%MS 0; last first.
  by rewrite (sameP capmx_idPl eqmxP) minW ?capmxSl ?capmx_module.
have [_ Rei ideRi _] := Wedderburn_is_id i.
have:= nzE; rewrite -submx0 => /memmx_subP[A E_A].
rewrite -(ideRi _ (memmx_subP sE_Ri _ E_A)).
have:= E_A; rewrite defE mem_sub_gring => /andP[R_A M_A].
have:= Rei; rewrite genmxE mem_sub_gring => /andP[Re].
rewrite -{2}(gring_rowK Re) /socle_val defW => /sub_sumsmxP[e ->].
rewrite !(linear_sum, mulmx_suml) summx_sub //= => k _.
rewrite -(gring_rowK R_A) -gring_mxA -mulmxA gring_rowK //.
rewrite ((W k *m _ =P 0) _) ?linear0 ?sub0mx //.
have [f _ homWf defWk] := mx_iso_trans (mx_iso_sym (isoW j)) (isoW k).
rewrite -submx0 -{k defWk}(eqmxMr _ defWk) -(hom_envelop_mxC homWf) //.
rewrite -(mul0mx _ f) submxMr {f homWf}// -dxWE sub_capmx.
rewrite (mxmodule_envelop modW) //=; apply/row_subP=> k.
rewrite row_mul -mem_gring_mx -(gring_rowK R_A) gring_mxA gring_rowK //.
by rewrite -defE (memmx_subP idlE) // mem_mulsmx ?gring_mxP.
Qed.

Section IrrComponent.

(* The component of the socle of the regular module that is associated to an *)
(* irreducible representation.                                               *)

Variables (n : nat) (rG : mx_representation F G n).
Local Notation E_G := (enveloping_algebra_mx rG).

Let not_rsim_op0 (iG j : sG) A :
    mx_rsim rG (socle_repr iG) -> iG != j -> (A \in 'R_j)%MS ->
  gring_op rG A = 0.
Proof.
case/mx_rsim_def=> f [f' _ hom_f] ne_iG_j RjA.
transitivity (f *m in_submod _ (val_submod 1%:M *m A) *m f').
  have{RjA}: (A \in R_G)%MS by rewrite -Wedderburn_sum (sumsmx_sup j).
  case/envelop_mxP=> a ->{A}; rewrite !(linear_sum, mulmx_suml).
  by apply: eq_bigr => x Gx; rewrite !linearZ /= -scalemxAl -hom_f ?gring_opG.
rewrite (_ : _ *m A = 0) ?(linear0, mul0mx) //.
apply/row_matrixP=> i; rewrite row_mul row0 -[row _ _]gring_mxK -gring_row_mul.
rewrite (Wedderburn_mulmx0 ne_iG_j) ?linear0 // genmxE mem_gring_mx.
by rewrite (row_subP _) // val_submod1 component_mx_id //; apply: socle_simple.
Qed.

Definition irr_comp := odflt 1%irr [pick i | gring_op rG 'e_i != 0].
Local Notation iG := irr_comp.

Hypothesis irrG : mx_irreducible rG.

Lemma rsim_irr_comp : mx_rsim rG (irr_repr iG).
Proof.
have [M [modM rsimM]] := rsim_regular_submod irrG F'G.
have simM: mxsimple aG M.
  case/mx_irrP: irrG => n_gt0 minG.
  have [f def_n injf homf] := mx_rsim_sym rsimM.
  apply/(submod_mx_irr modM)/mx_irrP.
  split=> [|U modU nzU]; first by rewrite def_n.
  rewrite /row_full -(mxrankMfree _ injf) -genmxE {4}def_n.
  apply: minG; last by rewrite -mxrank_eq0 genmxE mxrankMfree // mxrank_eq0.
  rewrite (eqmx_module _ (genmxE _)); apply/mxmoduleP=> x Gx.
  by rewrite -mulmxA -homf // mulmxA submxMr // (mxmoduleP modU).
pose i := PackSocle (component_socle sG simM).
have{modM rsimM} rsimM: mx_rsim rG (socle_repr i).
  apply: mx_rsim_trans rsimM (mx_rsim_sym _); apply/mx_rsim_iso.
  apply: (component_mx_iso (socle_simple _)) => //.
  by rewrite [component_mx _ _]PackSocleK component_mx_id.
have [<- // | ne_i_iG] := eqVneq i iG.
suffices {i M simM ne_i_iG rsimM}: gring_op rG 'e_iG != 0.
  by rewrite (not_rsim_op0 rsimM ne_i_iG) ?Wedderburn_id_mem ?eqxx.
rewrite /iG; case: pickP => //= G0.
suffices: rG 1%g == 0.
  by case/idPn; rewrite -mxrank_eq0 repr_mx1 mxrank1 -lt0n; case/mx_irrP: irrG.
rewrite -gring_opG // repr_mx1 -Wedderburn_sum_id linear_sum big1 // => j _.
by move/eqP: (G0 j).
Qed.

Lemma irr_comp'_op0 j A : j != iG -> (A \in 'R_j)%MS -> gring_op rG A = 0.
Proof. by rewrite eq_sym; apply: not_rsim_op0 rsim_irr_comp. Qed.

Lemma irr_comp_envelop : ('R_iG *m lin_mx (gring_op rG) :=: E_G)%MS.
Proof.
apply/eqmxP/andP; split; apply/row_subP=> i.
  by rewrite row_mul mul_rV_lin gring_mxP.
rewrite rowK /= -gring_opG ?enum_valP // -mul_vec_lin -gring_opG ?enum_valP //.
rewrite vec_mxK /= -mulmxA mulmx_sub {i}//= -(eqmxMr _ Wedderburn_sum).
rewrite (bigD1 iG) //= addsmxMr addsmxC [_ *m _](sub_kermxP _) ?adds0mx //=.
apply/sumsmx_subP => j ne_j_iG; apply/memmx_subP=> A RjA; apply/sub_kermxP.
by rewrite mul_vec_lin /= (irr_comp'_op0 ne_j_iG RjA) linear0.
Qed.

Lemma ker_irr_comp_op : ('R_iG :&: kermx (lin_mx (gring_op rG)))%MS = 0.
Proof.
apply/eqP; rewrite -submx0; apply/memmx_subP=> A.
rewrite sub_capmx /= submx0 mxvec_eq0 => /andP[R_A].
rewrite (sameP sub_kermxP eqP) mul_vec_lin mxvec_eq0 /= => opA0.
have [_ Re ideR _] := Wedderburn_is_id iG; rewrite -[A]ideR {ideR}//.
move: Re; rewrite genmxE mem_sub_gring /socle_val => /andP[Re].
rewrite -{2}(gring_rowK Re) -submx0.
pose simMi := socle_simple iG; have [J [M isoM ->]] := component_mx_def simMi.
case/sub_sumsmxP=> e ->; rewrite linear_sum mulmx_suml summx_sub // => j _.
rewrite -(in_submodK (submxMl _ (M j))); move: (in_submod _ _) => v.
have modMj: mxmodule aG (M j) by apply: mx_iso_module (isoM j) _; case: simMi.
have rsimMj: mx_rsim rG (submod_repr modMj).
  by apply: mx_rsim_trans rsim_irr_comp _; apply/mx_rsim_iso.
have [f [f' _ hom_f]] := mx_rsim_def (mx_rsim_sym rsimMj); rewrite submx0.
have <-: (gring_mx aG (val_submod (v *m (f *m gring_op rG A *m f')))) = 0.
  by rewrite (eqP opA0) !(mul0mx, linear0).
have: (A \in R_G)%MS by rewrite -Wedderburn_sum (sumsmx_sup iG).
case/envelop_mxP=> a ->; rewrite !(linear_sum, mulmx_suml) /=; apply/eqP.
apply: eq_bigr=> x Gx; rewrite !linearZ -scalemxAl !linearZ /=.
by rewrite gring_opG // -hom_f // val_submodJ // gring_mxJ.
Qed.

Lemma regular_op_inj :
  {in [pred A | (A \in 'R_iG)%MS] &, injective (gring_op rG)}.
Proof.
move=> A B RnA RnB /= eqAB; apply/eqP; rewrite -subr_eq0 -mxvec_eq0 -submx0.
rewrite -ker_irr_comp_op sub_capmx (sameP sub_kermxP eqP) mul_vec_lin.
by rewrite 2!linearB /= eqAB subrr linear0 addmx_sub ?eqmx_opp /=.
Qed.

Lemma rank_irr_comp : \rank 'R_iG = \rank E_G.
Proof.
symmetry; rewrite -{1}irr_comp_envelop; apply/mxrank_injP.
by rewrite ker_irr_comp_op.
Qed.

End IrrComponent.

Lemma irr_comp_rsim n1 n2 rG1 rG2 :
  @mx_rsim _ G n1 rG1 n2 rG2 -> irr_comp rG1 = irr_comp rG2.
Proof.
case=> f eq_n12; rewrite -eq_n12 in rG2 f * => inj_f hom_f.
congr (odflt _ _); apply: eq_pick => i; rewrite -!mxrank_eq0.
rewrite -(mxrankMfree _ inj_f); symmetry; rewrite -(eqmxMfull _ inj_f).
have /envelop_mxP[e ->{i}]: ('e_i \in R_G)%MS.
  by rewrite -Wedderburn_sum (sumsmx_sup i) ?Wedderburn_id_mem.
congr (\rank _ != _); rewrite !(mulmx_suml, linear_sum); apply: eq_bigr => x Gx.
by rewrite !linearZ -scalemxAl /= !gring_opG ?hom_f.
Qed.

Lemma irr_reprK i : irr_comp (irr_repr i) = i.
Proof.
apply/eqP; apply/component_mx_isoP; try exact: socle_simple.
by move/mx_rsim_iso: (rsim_irr_comp (socle_irr i)); apply: mx_iso_sym.
Qed.

Lemma irr_repr'_op0 i j A :
  j != i -> (A \in 'R_j)%MS -> gring_op (irr_repr i) A = 0.
Proof.
by move=> neq_ij /irr_comp'_op0-> //; [apply: socle_irr | rewrite irr_reprK].
Qed.

Lemma op_Wedderburn_id i : gring_op (irr_repr i) 'e_i = 1%:M.
Proof.
rewrite -(gring_op1 (irr_repr i)) -Wedderburn_sum_id.
rewrite linear_sum (bigD1 i) //= addrC big1 ?add0r // => j neq_ji.
exact: irr_repr'_op0 (Wedderburn_id_mem j).
Qed.

Lemma irr_comp_id (M : 'M_nG) (modM : mxmodule aG M) (iM : sG) :
  mxsimple aG M -> (M <= iM)%MS -> irr_comp (submod_repr modM) = iM.
Proof.
move=> simM sMiM; rewrite -[iM]irr_reprK.
apply/esym/irr_comp_rsim/mx_rsim_iso/component_mx_iso => //.
exact: socle_simple.
Qed.

Lemma irr1_repr x : x \in G -> irr_repr 1 x = 1%:M.
Proof.
move=> Gx; suffices: x \in rker (irr_repr 1) by case/rkerP.
apply: subsetP x Gx; rewrite rker_submod rfix_mx_rstabC // -irr1_rfix.
by apply: component_mx_id; apply: socle_simple.
Qed.

Hypothesis splitG : group_splitting_field G.

Lemma rank_Wedderburn_subring i : \rank 'R_i = ('n_i ^ 2)%N.
Proof.
apply/eqP; rewrite -{1}[i]irr_reprK; have irrSi := socle_irr i.
by case/andP: (splitG irrSi) => _; rewrite rank_irr_comp.
Qed.

Lemma sum_irr_degree : (\sum_i 'n_i ^ 2 = nG)%N.
Proof.
apply: etrans (eqnP gring_free).
rewrite -Wedderburn_sum (mxdirectP Wedderburn_direct) /=.
by apply: eq_bigr => i _; rewrite rank_Wedderburn_subring.
Qed.

Lemma irr_mx_mult i : socle_mult i = 'n_i.
Proof.
rewrite /socle_mult -(mxrankMfree _ gring_free) -genmxE.
by rewrite rank_Wedderburn_subring mulKn ?irr_degree_gt0.
Qed.

Lemma mxtrace_regular :
  {in G, forall x, \tr (aG x) = \sum_i \tr (socle_repr i x) *+ 'n_i}.
Proof.
move=> x Gx; have soc1: (Socle sG :=: 1%:M)%MS by rewrite -irr_mx_sum.
rewrite -(mxtrace_submod1 (Socle_module sG) soc1) // mxtrace_Socle //.
by apply: eq_bigr => i _; rewrite irr_mx_mult.
Qed.

Definition linear_irr := [set i | 'n_i == 1%N].

Lemma irr_degree_abelian : abelian G -> forall i, 'n_i = 1%N.
Proof. by move=> cGG i; apply: mxsimple_abelian_linear (socle_simple i). Qed.

Lemma linear_irr_comp i : 'n_i = 1%N -> (i :=: socle_base i)%MS.
Proof.
move=> ni1; apply/eqmxP; rewrite andbC -mxrank_leqif_eq -/'n_i.
  by rewrite -(mxrankMfree _ gring_free) -genmxE rank_Wedderburn_subring ni1.
exact: component_mx_id (socle_simple i).
Qed.

Lemma Wedderburn_subring_center i : ('Z('R_i) :=: mxvec 'e_i)%MS.
Proof.
have [nz_e Re ideR idRe] := Wedderburn_is_id i.
have Ze: (mxvec 'e_i <= 'Z('R_i))%MS.
  rewrite sub_capmx [(_ <= _)%MS]Re.
  by apply/cent_mxP=> A R_A; rewrite ideR // idRe.
pose irrG := socle_irr i; set rG := socle_repr i in irrG.
pose E_G := enveloping_algebra_mx rG; have absG := splitG irrG.
apply/eqmxP; rewrite andbC -(geq_leqif (mxrank_leqif_eq Ze)).
have ->: \rank (mxvec 'e_i) = (0 + 1)%N.
  by apply/eqP; rewrite eqn_leq rank_leq_row lt0n mxrank_eq0 mxvec_eq0.
rewrite -(mxrank_mul_ker _ (lin_mx (gring_op rG))) addnC leq_add //.
  rewrite leqn0 mxrank_eq0 -submx0 -(ker_irr_comp_op irrG) capmxS //.
  by rewrite irr_reprK capmxSl.
apply: leq_trans (mxrankS _) (rank_leq_row (mxvec 1%:M)).
apply/memmx_subP=> Ar; case/submxP=> a ->{Ar}.
rewrite mulmxA mul_rV_lin /=; set A := vec_mx _.
rewrite memmx1 (mx_abs_irr_cent_scalar absG) // -memmx_cent_envelop.
apply/cent_mxP=> Br; rewrite -(irr_comp_envelop irrG) irr_reprK.
case/submxP=> b /(canRL mxvecK) ->{Br}; rewrite mulmxA mx_rV_lin /=.
set B := vec_mx _; have RiB: (B \in 'R_i)%MS by rewrite vec_mxK submxMl.
have sRiR: ('R_i <= R_G)%MS by rewrite -Wedderburn_sum (sumsmx_sup i).
have: (A \in 'Z('R_i))%MS by rewrite vec_mxK submxMl.
rewrite sub_capmx => /andP[RiA /cent_mxP cRiA].
by rewrite -!gring_opM ?(memmx_subP sRiR) 1?cRiA.
Qed.

Lemma Wedderburn_center :
  ('Z(R_G) :=: \matrix_(i < #|sG|) mxvec 'e_(enum_val i))%MS.
Proof.
have:= mxdirect_sums_center Wedderburn_sum Wedderburn_direct Wedderburn_ideal.
move/eqmx_trans; apply; apply/eqmxP/andP; split.
  apply/sumsmx_subP=> i _; rewrite Wedderburn_subring_center.
  by apply: (eq_row_sub (enum_rank i)); rewrite rowK enum_rankK.
apply/row_subP=> i; rewrite rowK -Wedderburn_subring_center.
by rewrite (sumsmx_sup (enum_val i)).
Qed.

Lemma card_irr : #|sG| = tG.
Proof.
rewrite -(eqnP classg_base_free) classg_base_center.
have:= mxdirect_sums_center Wedderburn_sum Wedderburn_direct Wedderburn_ideal.
move->; rewrite (mxdirectP _) /=; last first.
  apply/mxdirect_sumsP=> i _; apply/eqP; rewrite -submx0.
  rewrite -{2}(mxdirect_sumsP Wedderburn_direct i) // capmxS ?capmxSl //=.
  by apply/sumsmx_subP=> j neji; rewrite (sumsmx_sup j) ?capmxSl.
rewrite -sum1_card; apply: eq_bigr => i _; apply/eqP.
rewrite Wedderburn_subring_center eqn_leq rank_leq_row lt0n mxrank_eq0.
by rewrite andbT mxvec_eq0; case: (Wedderburn_is_id i).
Qed.

Section CenterMode.

Variable i : sG.

Let i0 := Ordinal (irr_degree_gt0 i).

Definition irr_mode x := irr_repr i x i0 i0.

Lemma irr_mode1 : irr_mode 1 = 1.
Proof. by rewrite /irr_mode repr_mx1 mxE eqxx. Qed.

Lemma irr_center_scalar : {in 'Z(G), forall x, irr_repr i x = (irr_mode x)%:M}.
Proof.
rewrite /irr_mode => x /setIP[Gx cGx].
suffices [a ->]: exists a, irr_repr i x = a%:M by rewrite mxE eqxx.
apply/is_scalar_mxP; apply: (mx_abs_irr_cent_scalar (splitG (socle_irr i))).
by apply/centgmxP=> y Gy; rewrite -!{1}repr_mxM 1?(centP cGx).
Qed.

Lemma irr_modeM : {in 'Z(G) &, {morph irr_mode : x y / (x * y)%g >-> x * y}}.
Proof.
move=> x y Zx Zy; rewrite {1}/irr_mode repr_mxM ?(subsetP (center_sub G)) //.
by rewrite !irr_center_scalar // -scalar_mxM mxE eqxx.
Qed.

Lemma irr_modeX n : {in 'Z(G), {morph irr_mode : x / (x ^+ n)%g >-> x ^+ n}}.
Proof.
elim: n => [|n IHn] x Zx; first exact: irr_mode1.
by rewrite expgS irr_modeM ?groupX // exprS IHn.
Qed.

Lemma irr_mode_unit : {in 'Z(G), forall x, irr_mode x \is a GRing.unit}.
Proof.
move=> x Zx /=; have:= unitr1 F.
by rewrite -irr_mode1 -(mulVg x) irr_modeM ?groupV // unitrM; case/andP=> _.
Qed.

Lemma irr_mode_neq0 : {in 'Z(G), forall x, irr_mode x != 0}.
Proof. by move=> x /irr_mode_unit; rewrite unitfE. Qed.

Lemma irr_modeV : {in 'Z(G), {morph irr_mode : x / (x^-1)%g >-> x^-1}}.
Proof.
move=> x Zx /=; rewrite -[_^-1]mul1r; apply: canRL (mulrK (irr_mode_unit Zx)) _.
by rewrite -irr_modeM ?groupV // mulVg irr_mode1.
Qed.

End CenterMode.

Lemma irr1_mode x : x \in G -> irr_mode 1 x = 1.
Proof. by move=> Gx; rewrite /irr_mode irr1_repr ?mxE. Qed.

End Regular.

Local Notation "[ 1 sG ]" := (principal_comp sG) : irrType_scope.

Section LinearIrr.

Variables (gT : finGroupType) (G : {group gT}).

Lemma card_linear_irr (sG : irrType G) :
    [char F]^'.-group G -> group_splitting_field G ->
  #|linear_irr sG| = #|G : G^`(1)|%g.
Proof.
move=> F'G splitG; apply/eqP.
wlog sGq: / irrType (G / G^`(1))%G by apply: socle_exists.
have [_ nG'G] := andP (der_normal 1 G); apply/eqP; rewrite -card_quotient //.
have cGqGq: abelian (G / G^`(1))%g by apply: sub_der1_abelian.
have F'Gq: [char F]^'.-group (G / G^`(1))%g by apply: morphim_pgroup.
have splitGq: group_splitting_field (G / G^`(1))%G.
  exact: quotient_splitting_field.
rewrite -(sum_irr_degree sGq) // -sum1_card.
pose rG (j : sGq) := morphim_repr (socle_repr j) nG'G.
have irrG j: mx_irreducible (rG j) by apply/morphim_mx_irr; apply: socle_irr.
rewrite (reindex (fun j => irr_comp sG (rG j))) /=.
  apply: eq_big => [j | j _]; last by rewrite irr_degree_abelian.
  have [_ lin_j _ _] := rsim_irr_comp sG F'G (irrG j).
  by rewrite inE -lin_j -irr_degreeE irr_degree_abelian.
pose sGlin := {i | i \in linear_irr sG}.
have sG'k (i : sGlin) : G^`(1)%g \subset rker (irr_repr (val i)).
  by case: i => i /=; rewrite !inE => lin; rewrite rker_linear //=; apply/eqP.
pose h' u := irr_comp sGq (quo_repr (sG'k u) nG'G).
have irrGq u: mx_irreducible (quo_repr (sG'k u) nG'G).
  by apply/quo_mx_irr; apply: socle_irr.
exists (fun i => oapp h' [1 sGq]%irr (insub i)) => [j | i] lin_i.
  rewrite (insubT (mem _) lin_i) /=; apply/esym/eqP/socle_rsimP.
  apply: mx_rsim_trans (rsim_irr_comp sGq F'Gq (irrGq _)).
  have [g lin_g inj_g hom_g] := rsim_irr_comp sG F'G (irrG j).
  exists g => [||G'x]; last 1 [case/morphimP=> x _ Gx ->] || by [].
  by rewrite quo_repr_coset ?hom_g.
rewrite (insubT (mem _) lin_i) /=; apply/esym/eqP/socle_rsimP.
set u := exist _ _ _; apply: mx_rsim_trans (rsim_irr_comp sG F'G (irrG _)).
have [g lin_g inj_g hom_g] := rsim_irr_comp sGq F'Gq (irrGq u).
exists g => [||x Gx]; last 1 [have:= hom_g (coset _ x)] || by [].
by rewrite quo_repr_coset; first by apply; rewrite mem_quotient.
Qed.

Lemma primitive_root_splitting_abelian (z : F) :
  #|G|.-primitive_root z -> abelian G -> group_splitting_field G.
Proof.
move=> ozG cGG [|n] rG irrG; first by case/mx_irrP: irrG.
case: (pickP [pred x in G | ~~ is_scalar_mx (rG x)]) => [x | scalG].
  case/andP=> Gx nscal_rGx; have: horner_mx (rG x) ('X^#|G| - 1) == 0.
    rewrite rmorphB rmorphX /= horner_mx_C horner_mx_X.
    rewrite -repr_mxX ?inE // ((_ ^+ _ =P 1)%g _) ?repr_mx1 ?subrr //.
    by rewrite -order_dvdn order_dvdG.
  case/idPn; rewrite -mxrank_eq0 -(factor_Xn_sub_1 ozG).
  elim: #|G| => [|i IHi]; first by rewrite big_nil horner_mx_C mxrank1.
  rewrite big_nat_recr //= rmorphM mxrankMfree {IHi}//.
  rewrite row_free_unit rmorphB /= horner_mx_X horner_mx_C.
  rewrite (mx_Schur irrG) ?subr_eq0 //; last first.
    by apply: contraNneq nscal_rGx => ->; apply: scalar_mx_is_scalar.
  rewrite -memmx_cent_envelop linearB.
  rewrite addmx_sub ?eqmx_opp ?scalar_mx_cent //= memmx_cent_envelop.
  by apply/centgmxP=> j Zh_j; rewrite -!repr_mxM // (centsP cGG).
pose M := <<delta_mx 0 0 : 'rV[F]_n.+1>>%MS.
have linM: \rank M = 1%N by rewrite genmxE mxrank_delta.
have modM: mxmodule rG M.
  apply/mxmoduleP=> x Gx; move/idPn: (scalG x); rewrite /= Gx negbK.
  by case/is_scalar_mxP=> ? ->; rewrite scalar_mxC submxMl.
apply: linear_mx_abs_irr; apply/eqP; rewrite eq_sym -linM.
by case/mx_irrP: irrG => _; apply; rewrite // -mxrank_eq0 linM.
Qed.

Lemma cycle_repr_structure x (sG : irrType G) :
    G :=: <[x]> -> [char F]^'.-group G -> group_splitting_field G ->
  exists2 w : F, #|G|.-primitive_root w &
  exists iphi : 'I_#|G| -> sG,
  [/\ bijective iphi,
      #|sG| = #|G|,
      forall i, irr_mode (iphi i) x = w ^+ i
    & forall i, irr_repr (iphi i) x = (w ^+ i)%:M].
Proof.
move=> defG; rewrite {defG}(group_inj defG) -/#[x] in sG * => F'X splitF.
have Xx := cycle_id x; have cXX := cycle_abelian x.
have card_sG: #|sG| = #[x].
  by rewrite card_irr //; apply/eqP; rewrite -card_classes_abelian.
have linX := irr_degree_abelian splitF cXX (_ : sG).
pose r (W : sG) := irr_mode W x.
have scalX W: irr_repr W x = (r W)%:M.
  by apply: irr_center_scalar; rewrite ?(center_idP _).
have inj_r: injective r.
  move=> V W eqVW; rewrite -(irr_reprK F'X V) -(irr_reprK F'X W).
  move: (irr_repr V) (irr_repr W) (scalX V) (scalX W).
  rewrite !linX {}eqVW => rV rW <- rWx; apply: irr_comp_rsim => //.
  exists 1%:M; rewrite ?row_free_unit ?unitmx1 // => xk; case/cycleP=> k ->{xk}.
  by rewrite mulmx1 mul1mx !repr_mxX // rWx.
have rx1 W: r W ^+ #[x] = 1.
  by rewrite -irr_modeX ?(center_idP _) // expg_order irr_mode1.
have /hasP[w _ prim_w]: has #[x].-primitive_root (map r (enum sG)).
  rewrite has_prim_root 1?map_inj_uniq ?enum_uniq //; first 1 last.
    by rewrite size_map -cardE card_sG.
  by apply/allP=> _ /mapP[W _ ->]; rewrite unity_rootE rx1.
have iphi'P := prim_rootP prim_w (rx1 _); pose iphi' := sval (iphi'P _).
have def_r W: r W = w ^+ iphi' W by apply: svalP (iphi'P W).
have inj_iphi': injective iphi'.
  by move=> i j eq_ij; apply: inj_r; rewrite !def_r eq_ij.
have iphiP: codom iphi' =i 'I_#[x].
  by apply/subset_cardP; rewrite ?subset_predT // card_ord card_image.
pose iphi i := iinv (iphiP i); exists w => //; exists iphi.
have iphiK: cancel iphi iphi' by move=> i; apply: f_iinv.
have r_iphi i: r (iphi i) = w ^+ i by rewrite def_r iphiK.
split=> // [|i]; last by rewrite scalX r_iphi.
by exists iphi' => // W; rewrite /iphi iinv_f.
Qed.

Lemma splitting_cyclic_primitive_root :
    cyclic G -> [char F]^'.-group G -> group_splitting_field G ->
  classically {z : F | #|G|.-primitive_root z}.
Proof.
case/cyclicP=> x defG F'G splitF; case=> // IH.
wlog sG: / irrType G by apply: socle_exists.
have [w prim_w _] := cycle_repr_structure sG defG F'G splitF.
by apply: IH; exists w.
Qed.

End LinearIrr.

End FieldRepr.

Arguments rfix_mx {F gT G%g n%N} rG H%g.
Arguments gset_mx F {gT} G%g A%g.
Arguments classg_base F {gT} G%g _%g : extra scopes.
Arguments irrType F {gT} G%g.

Arguments mxmoduleP {F gT G n rG m U}.
Arguments envelop_mxP {F gT G n rG A}.
Arguments hom_mxP {F gT G n rG m f W}.
Arguments mx_Maschke [F gT G n] rG _ [U].
Arguments rfix_mxP {F gT G n rG m W}.
Arguments cyclic_mxP {F gT G n rG u v}.
Arguments annihilator_mxP {F gT G n rG u A}.
Arguments row_hom_mxP {F gT G n rG u v}.
Arguments mxsimple_isoP {F gT G n rG U V}.
Arguments socle_exists [F gT G n].
Arguments socleP {F gT G n rG sG0 W W'}.
Arguments mx_abs_irrP {F gT G n rG}.
Arguments socle_rsimP {F gT G n rG sG W1 W2}.

Arguments val_submod {F n U m} W.
Arguments in_submod {F n} U {m} W.
Arguments val_submodK {F n U m} W : rename.
Arguments in_submodK {F n U m} [W] sWU.
Arguments val_submod_inj {F n U m} [W1 W2] : rename.

Arguments val_factmod {F n U m} W.
Arguments in_factmod {F n} U {m} W.
Arguments val_factmodK {F n U m} W : rename.
Arguments in_factmodK {F n} U {m} [W] sWU.
Arguments val_factmod_inj {F n U m} [W1 W2] : rename.

Notation "'Cl" := (Clifford_action _) : action_scope.

Arguments gring_row {R gT G} A.
Arguments gring_rowK {F gT G} [A] RG_A.

Bind Scope irrType_scope with socle_sort.
Notation "[ 1 sG ]" := (principal_comp sG) : irrType_scope.
Arguments irr_degree {F gT G%G sG} i%irr.
Arguments irr_repr {F gT G%G sG} i%irr _%g : extra scopes.
Arguments irr_mode {F gT G%G sG} i%irr z%g : rename.
Notation "''n_' i" := (irr_degree i) : group_ring_scope.
Notation "''R_' i" := (Wedderburn_subring i) : group_ring_scope.
Notation "''e_' i" := (Wedderburn_id i) : group_ring_scope.

Section DecideRed.

Import MatrixFormula.
Local Notation term := GRing.term.
Local Notation True := GRing.True.
Local Notation And := GRing.And (only parsing).
Local Notation morphAnd f := ((big_morph f) true andb).
Local Notation eval := GRing.eval.
Local Notation holds := GRing.holds.
Local Notation qf_form := GRing.qf_form.
Local Notation qf_eval := GRing.qf_eval.

Section Definitions.

Variables (F : fieldType) (gT : finGroupType) (G : {group gT}) (n : nat).
Variable rG : mx_representation F G n.

Definition mxmodule_form (U : 'M[term F]_n) :=
  \big[And/True]_(x in G) submx_form (mulmx_term U (mx_term (rG x))) U.

Lemma mxmodule_form_qf U : qf_form (mxmodule_form U).
Proof.
by rewrite (morphAnd (@qf_form _)) ?big1 //= => x _; rewrite submx_form_qf.
Qed.

Lemma eval_mxmodule U e :
  qf_eval e (mxmodule_form U) = mxmodule rG (eval_mx e U).
Proof.
rewrite (morphAnd (qf_eval e)) //= big_andE /=.
apply/forallP/mxmoduleP=> Umod x; move/implyP: (Umod x);
  by rewrite eval_submx eval_mulmx eval_mx_term.
Qed.

Definition mxnonsimple_form (U : 'M[term F]_n) :=
  let V := vec_mx (row_var F (n * n) 0) in
  let nzV := (~ mxrank_form 0 V)%T in
  let properVU := (submx_form V U /\ ~ submx_form U V)%T in
  (Exists_row_form (n * n) 0 (mxmodule_form V /\ nzV /\ properVU))%T.

End Definitions.

Variables (F : decFieldType) (gT : finGroupType) (G : {group gT}) (n : nat).
Variable rG : mx_representation F G n.

Definition mxnonsimple_sat U :=
  GRing.sat (@row_env _ (n * n) [::]) (mxnonsimple_form rG (mx_term U)).

Lemma mxnonsimpleP U :
  U != 0 -> reflect (mxnonsimple rG U) (mxnonsimple_sat U).
Proof.
rewrite /mxnonsimple_sat {1}/mxnonsimple_form; set Vt := vec_mx _ => /= nzU.
pose nsim V := [&& mxmodule rG V, (V <= U)%MS, V != 0 & \rank V < \rank U].
set nsimUt := (_ /\ _)%T; have: qf_form nsimUt.
  by rewrite /= mxmodule_form_qf !mxrank_form_qf !submx_form_qf.
move/GRing.qf_evalP; set qev := @GRing.qf_eval _ => qevP.
have qev_nsim u: qev (row_env [:: u]) nsimUt = nsim n (vec_mx u).
  rewrite /nsim -mxrank_eq0 /qev /= eval_mxmodule eval_mxrank.
  rewrite !eval_submx eval_mx_term eval_vec_mx eval_row_var /=.
  do 2!bool_congr; apply: andb_id2l => sUV.
  by rewrite ltn_neqAle andbC !mxrank_leqif_sup.
have n2gt0: n ^ 2 > 0.
  by move: nzU; rewrite muln_gt0 -mxrank_eq0; case: posnP (U) => // ->.
apply: (iffP satP) => [|[V nsimV]].
  by case/Exists_rowP=> // v; move/qevP; rewrite qev_nsim; exists (vec_mx v).
apply/Exists_rowP=> //; exists (mxvec V); apply/qevP.
by rewrite qev_nsim mxvecK.
Qed.

Lemma dec_mxsimple_exists (U : 'M_n) :
  mxmodule rG U -> U != 0 -> {V | mxsimple rG V & V <= U}%MS.
Proof.
elim: {U}_.+1 {-2}U (ltnSn (\rank U)) => // m IHm U leUm modU nzU.
have [nsimU | simU] := mxnonsimpleP nzU; last first.
  by exists U; first apply/mxsimpleP.
move: (xchooseP nsimU); move: (xchoose _) => W /and4P[modW sWU nzW ltWU].
case: (IHm W) => // [|V simV sVW]; first exact: leq_trans ltWU _.
by exists V; last apply: submx_trans sVW sWU.
Qed.

Lemma dec_mx_reducible_semisimple U :
  mxmodule rG U -> mx_completely_reducible rG U -> mxsemisimple rG U.
Proof.
elim: {U}_.+1 {-2}U (ltnSn (\rank U)) => // m IHm U leUm modU redU.
have [U0 | nzU] := eqVneq U 0.
  have{U0} U0: (\sum_(i < 0) 0 :=: U)%MS by rewrite big_ord0 U0.
  by apply: (intro_mxsemisimple U0); case.
have [V simV sVU] := dec_mxsimple_exists modU nzU; have [modV nzV _] := simV.
have [W modW defVW dxVW] := redU V modV sVU.
have [||I W_ /= simW defW _] := IHm W _ modW.
- rewrite ltnS in leUm; apply: leq_trans leUm.
  by rewrite -defVW (mxdirectP dxVW) /= -add1n leq_add2r lt0n mxrank_eq0.
- by apply: mx_reducibleS redU; rewrite // -defVW addsmxSr.
suffices defU: (\sum_i oapp W_ V i :=: U)%MS.
  by apply: (intro_mxsemisimple defU) => [] [|i] //=.
apply: eqmx_trans defVW; rewrite (bigD1 None) //=; apply/eqmxP.
have [i0 _ | I0] := pickP I.
  by rewrite (reindex some) ?addsmxS ?defW //; exists (odflt i0) => //; case.
rewrite big_pred0 //; last by case=> // /I0.
by rewrite !addsmxS ?sub0mx // -defW big_pred0.
Qed.

Lemma DecSocleType : socleType rG.
Proof.
have [n0 | n_gt0] := posnP n.
  by exists [::] => // M [_]; rewrite -mxrank_eq0 -leqn0 -n0 rank_leq_row.
have n2_gt0: n ^ 2 > 0 by rewrite muln_gt0 n_gt0.
pose span Ms := (\sum_(M <- Ms) component_mx rG M)%MS.
have: {in [::], forall M, mxsimple rG M} by [].
elim: _.+1 {-2}nil (ltnSn (n - \rank (span nil))) => // m IHm Ms Ms_ge_n simMs.
rewrite ltnS in Ms_ge_n; pose V := span Ms; pose Vt := mx_term V.
pose Ut i := vec_mx (row_var F (n * n) i); pose Zt := mx_term (0 : 'M[F]_n).
pose exU i f := Exists_row_form (n * n) i (~ submx_form (Ut i) Zt /\ f (Ut i)).
pose meetUVf U := exU 1%N (fun W => submx_form W Vt /\ submx_form W U)%T.
pose mx_sat := GRing.sat (@row_env F (n * n) [::]).
have ev_sub0 := GRing.qf_evalP _ (submx_form_qf _ Zt).
have ev_mod := GRing.qf_evalP _ (mxmodule_form_qf rG _).
pose ev := (eval_mxmodule, eval_submx, eval_vec_mx, eval_row_var, eval_mx_term).
case haveU: (mx_sat (exU 0%N (fun U => mxmodule_form rG U /\ ~ meetUVf _ U)%T)).
  have [U modU]: {U : 'M_n | mxmodule rG U & (U != 0) && ((U :&: V)%MS == 0)}.
    apply: sig2W; case/Exists_rowP: (satP haveU) => //= u [nzU [modU tiUV]].
    exists (vec_mx u); first by move/ev_mod: modU; rewrite !ev.
    set W := (_ :&: V)%MS; move/ev_sub0: nzU; rewrite !ev -!submx0 => -> /=.
    apply/idPn=> nzW; case: tiUV; apply/Exists_rowP=> //; exists (mxvec W).
    apply/GRing.qf_evalP; rewrite /= ?submx_form_qf // !ev mxvecK nzW /=.
    by rewrite andbC -sub_capmx.
  case/andP=> nzU tiUV; have [M simM sMU] := dec_mxsimple_exists modU nzU.
  apply: (IHm (M :: Ms)) => [|M']; last first.
    by case/predU1P=> [-> //|]; apply: simMs.
  have [_ nzM _] := simM.
  suffices ltVMV: \rank V < \rank (span (M :: Ms)).
    rewrite (leq_trans _ Ms_ge_n) // ltn_sub2l ?(leq_trans ltVMV) //.
    exact: rank_leq_row.
  rewrite /span big_cons (ltn_leqif (mxrank_leqif_sup (addsmxSr _ _))).
  apply: contra nzM; rewrite addsmx_sub -submx0 -(eqP tiUV) sub_capmx sMU.
  by case/andP=> sMV _; rewrite (submx_trans _ sMV) ?component_mx_id.
exists Ms => // M simM; have [modM nzM minM] := simM.
have sMV: (M <= V)%MS.
  apply: contraFT haveU => not_sMV; apply/satP/Exists_rowP=> //.
  exists (mxvec M); split; first by apply/ev_sub0; rewrite !ev mxvecK submx0.
  split; first by apply/ev_mod; rewrite !ev mxvecK.
  apply/Exists_rowP=> // [[w]].
  apply/GRing.qf_evalP; rewrite /= ?submx_form_qf // !ev /= mxvecK submx0.
  rewrite -nz_row_eq0 -(cyclic_mx_eq0 rG); set W := cyclic_mx _ _.
  apply: contra not_sMV => /and3P[nzW Vw Mw].
  have{Vw Mw} [sWV sWM]: (W <= V /\ W <= M)%MS.
    rewrite !cyclic_mx_sub ?(submx_trans (nz_row_sub _)) //.
    by rewrite sumsmx_module // => M' _; apply: component_mx_module.
  by rewrite (submx_trans _ sWV) // minM ?cyclic_mx_module.
wlog sG: / socleType rG by apply: socle_exists.
have sVS: (V <= \sum_(W : sG | has (fun Mi => Mi <= W) Ms) W)%MS.
  rewrite [V](big_nth 0) big_mkord; apply/sumsmx_subP=> i _.
  set Mi := Ms`_i; have MsMi: Mi \in Ms by apply: mem_nth.
  have simMi := simMs _ MsMi; have S_Mi := component_socle sG simMi.
  rewrite (sumsmx_sup (PackSocle S_Mi)) ?PackSocleK //.
  by apply/hasP; exists Mi; rewrite ?component_mx_id.
have [W MsW isoWM] := subSocle_iso simM (submx_trans sMV sVS).
have [Mi MsMi sMiW] := hasP MsW; apply/hasP; exists Mi => //.
have [simMi simW] := (simMs _ MsMi, socle_simple W); apply/mxsimple_isoP=> //.
exact: mx_iso_trans (mx_iso_sym isoWM) (component_mx_iso simW simMi sMiW).
Qed.

End DecideRed.

Prenex Implicits mxmodule_form mxnonsimple_form mxnonsimple_sat.

(* Change of representation field (by tensoring) *)
Section ChangeOfField.
  
Variables (aF rF : fieldType) (f : {rmorphism aF -> rF}).
Local Notation "A ^f" := (map_mx (GRing.RMorphism.apply f) A) : ring_scope.
Variables (gT : finGroupType) (G : {group gT}).

Section OneRepresentation.

Variables (n : nat) (rG : mx_representation aF G n).
Local Notation rGf := (map_repr f rG).

Lemma map_rfix_mx H : (rfix_mx rG H)^f = rfix_mx rGf H.
Proof.
rewrite map_kermx //; congr (kermx _); apply: map_lin1_mx => //= v.
rewrite map_mxvec map_mxM; congr (mxvec (_ *m _)); last first.
  by apply: map_lin1_mx => //= u; rewrite map_mxM map_vec_mx.
apply/row_matrixP=> i.
by rewrite -map_row !rowK map_mxvec map_mx_sub map_mx1.
Qed.

Lemma rcent_map A : rcent rGf A^f = rcent rG A.
Proof.
by apply/setP=> x; rewrite !inE -!map_mxM inj_eq //; apply: map_mx_inj.
Qed.

Lemma rstab_map m (U : 'M_(m, n)) : rstab rGf U^f = rstab rG U.
Proof.
by apply/setP=> x; rewrite !inE -!map_mxM inj_eq //; apply: map_mx_inj.
Qed.

Lemma rstabs_map m (U : 'M_(m, n)) : rstabs rGf U^f = rstabs rG U.
Proof. by apply/setP=> x; rewrite !inE -!map_mxM ?map_submx. Qed.

Lemma centgmx_map A : centgmx rGf A^f = centgmx rG A.
Proof. by rewrite /centgmx rcent_map. Qed.

Lemma mxmodule_map m (U : 'M_(m, n)) : mxmodule rGf U^f = mxmodule rG U.
Proof. by rewrite /mxmodule rstabs_map. Qed.

Lemma mxsimple_map (U : 'M_n) : mxsimple rGf U^f -> mxsimple rG U.
Proof.
case; rewrite map_mx_eq0 // mxmodule_map // => modU nzU minU.
split=> // V modV sVU nzV; rewrite -(map_submx f).
by rewrite (minU V^f) //= ?mxmodule_map ?map_mx_eq0 // map_submx.
Qed.

Lemma mx_irr_map : mx_irreducible rGf -> mx_irreducible rG.
Proof. by move=> irrGf; apply: mxsimple_map; rewrite map_mx1. Qed.

Lemma rker_map : rker rGf = rker rG.
Proof. by rewrite /rker -rstab_map map_mx1. Qed.

Lemma map_mx_faithful : mx_faithful rGf = mx_faithful rG.
Proof. by rewrite /mx_faithful rker_map. Qed.

Lemma map_mx_abs_irr :
  mx_absolutely_irreducible rGf = mx_absolutely_irreducible rG.
Proof.
by rewrite /mx_absolutely_irreducible -map_enveloping_algebra_mx row_full_map.
Qed.

End OneRepresentation.

Lemma mx_rsim_map n1 n2 rG1 rG2 :
  @mx_rsim _ _ G n1 rG1 n2 rG2 -> mx_rsim (map_repr f rG1) (map_repr f rG2).
Proof.
case=> g eqn12 inj_g hom_g.
by exists g^f => // [|x Gx]; rewrite ?row_free_map // -!map_mxM ?hom_g.
Qed.

Lemma map_section_repr n (rG : mx_representation aF G n) rGf U V
                       (modU : mxmodule rG U) (modV : mxmodule rG V)
                       (modUf : mxmodule rGf U^f) (modVf : mxmodule rGf V^f) :
    map_repr f rG =1 rGf ->
  mx_rsim (map_repr f (section_repr modU modV)) (section_repr modUf modVf).
Proof.
move=> def_rGf; set VU := <<_>>%MS.
pose valUV := val_factmod (val_submod (1%:M : 'M[aF]_(\rank VU))).
have sUV_Uf: (valUV^f <= U^f + V^f)%MS.
  rewrite -map_addsmx map_submx; apply: submx_trans (proj_factmodS _ _).
  by rewrite val_factmodS val_submod1 genmxE.
exists (in_submod _ (in_factmod U^f valUV^f)) => [||x Gx].
- rewrite !genmxE -(mxrank_map f) map_mxM map_col_base.
  by case: (\rank (cokermx U)) / (mxrank_map _ _); rewrite map_cokermx.
- rewrite -kermx_eq0 -submx0; apply/rV_subP=> u.
  rewrite (sameP sub_kermxP eqP) submx0 -val_submod_eq0.
  rewrite val_submodE -mulmxA -val_submodE in_submodK; last first.
    by rewrite genmxE -(in_factmod_addsK _ V^f) submxMr.
  rewrite in_factmodE mulmxA -in_factmodE in_factmod_eq0.
  move/(submxMr (in_factmod U 1%:M *m in_submod VU 1%:M)^f).
  rewrite -mulmxA -!map_mxM //; do 2!rewrite mulmxA -in_factmodE -in_submodE.
  rewrite val_factmodK val_submodK map_mx1 mulmx1.
  have ->: in_factmod U U = 0 by apply/eqP; rewrite in_factmod_eq0.
  by rewrite linear0 map_mx0 eqmx0 submx0.
rewrite {1}in_submodE mulmxA -in_submodE -in_submodJ; last first.
  by rewrite genmxE -(in_factmod_addsK _ V^f) submxMr.
congr (in_submod _ _); rewrite -in_factmodJ // in_factmodE mulmxA -in_factmodE.
apply/eqP; rewrite -subr_eq0 -def_rGf -!map_mxM -linearB in_factmod_eq0.
rewrite -map_mx_sub map_submx -in_factmod_eq0 linearB.
rewrite /= (in_factmodJ modU) // val_factmodK.
rewrite [valUV]val_factmodE mulmxA -val_factmodE val_factmodK.
rewrite -val_submodE in_submodK ?subrr //.
by rewrite mxmodule_trans ?section_module // val_submod1.
Qed.

Lemma map_regular_subseries U i (modU : mx_subseries (regular_repr aF G) U)
   (modUf : mx_subseries (regular_repr rF G) [seq M^f | M <- U]) :
  mx_rsim (map_repr f (subseries_repr i modU)) (subseries_repr i modUf).
Proof.
set mf := map _ in modUf *; rewrite /subseries_repr.
do 2!move: (mx_subseries_module' _ _) (mx_subseries_module _ _).
have mf_i V: nth 0^f (mf V) i = (V`_i)^f.
  case: (ltnP i (size V)) => [ltiV | leVi]; first exact: nth_map.
  by rewrite !nth_default ?size_map.
rewrite -(map_mx0 f) mf_i (mf_i (0 :: U)) => modUi'f modUif modUi' modUi.
by apply: map_section_repr; apply: map_regular_repr.
Qed.

Lemma extend_group_splitting_field :
  group_splitting_field aF G -> group_splitting_field rF G.
Proof.
move=> splitG n rG irrG.
have modU0: all ((mxmodule (regular_repr aF G)) #|G|) [::] by [].
apply: (mx_Schreier modU0 _) => // [[U [compU lastU _]]]; have [modU _]:= compU.
pose Uf := map (map_mx f) U.
have{lastU} lastUf: (last 0 Uf :=: 1%:M)%MS.
  by rewrite -(map_mx0 f) -(map_mx1 f) last_map; apply/map_eqmx.
have modUf: mx_subseries (regular_repr rF G) Uf.
  rewrite /mx_subseries all_map; apply: etrans modU; apply: eq_all => Ui /=.
  rewrite -mxmodule_map; apply: eq_subset_r => x.
  by rewrite !inE map_regular_repr.
have absUf i: i < size U -> mx_absolutely_irreducible (subseries_repr i modUf).
  move=> lt_i_U; rewrite -(mx_rsim_abs_irr (map_regular_subseries i modU _)).
  rewrite map_mx_abs_irr; apply: splitG.
  by apply: mx_rsim_irr (mx_series_repr_irr compU lt_i_U); apply: section_eqmx.
have compUf: mx_composition_series (regular_repr rF G) Uf.
  split=> // i; rewrite size_map => ltiU.
  move/max_submodP: (mx_abs_irrW (absUf i ltiU)); apply.
  rewrite -{2}(map_mx0 f) -map_cons !(nth_map 0) ?leqW //.
  by rewrite map_submx // ltmxW // (pathP _ (mx_series_lt compU)).
have [[i ltiU] simUi] := rsim_regular_series irrG compUf lastUf.
have{simUi} simUi: mx_rsim rG (subseries_repr i modUf).
  by apply: mx_rsim_trans simUi _; apply: section_eqmx.
by rewrite (mx_rsim_abs_irr simUi) absUf; rewrite size_map in ltiU.
Qed.

End ChangeOfField.

(* Construction of a splitting field FA of an irreducible representation, for *)
(* a matrix A in the centraliser of the representation. FA is the row-vector  *)
(* space of the matrix algebra generated by A with basis 1, A, ..., A ^+ d.-1 *)
(* or, equivalently, the polynomials in {poly F} taken mod the (irreducible)  *)
(* minimal polynomial pA of A (of degree d).                                  *)
(* The details of the construction of FA are encapsulated in a submodule.     *)
Module Import MatrixGenField.

(* The type definition must come before the main section so that the Bind     *)
(* Scope directive applies to all lemmas and definition discharged at the     *)
(* of the section.                                                            *)
Record gen_of {F : fieldType} {gT : finGroupType} {G : {group gT}} {n' : nat}
              {rG : mx_representation F G n'.+1} {A : 'M[F]_n'.+1}
              (irrG : mx_irreducible rG) (cGA : centgmx rG A) :=
   Gen {rVval : 'rV[F]_(degree_mxminpoly A)}.

Local Arguments rVval {F gT G%G n'%N rG A%R irrG cGA} x%R : rename.
Bind Scope ring_scope with gen_of.
 
Section GenField.

Variables (F : fieldType) (gT : finGroupType) (G : {group gT}) (n' : nat).
Local Notation n := n'.+1.
Variables (rG : mx_representation F G n) (A : 'M[F]_n).

Local Notation d := (degree_mxminpoly A).
Local Notation Ad := (powers_mx A d).
Local Notation pA := (mxminpoly A).
Let d_gt0 := mxminpoly_nonconstant A.
Local Notation irr := mx_irreducible.

Hypotheses (irrG : irr rG) (cGA : centgmx rG A).

Notation FA := (gen_of irrG cGA).
Let inFA := Gen irrG cGA.

Canonical gen_subType := Eval hnf in [newType for rVval : FA -> 'rV_d].
Definition gen_eqMixin := Eval hnf in [eqMixin of FA by <:].
Canonical gen_eqType := Eval hnf in EqType FA gen_eqMixin.
Definition gen_choiceMixin := [choiceMixin of FA by <:].
Canonical gen_choiceType := Eval hnf in ChoiceType FA gen_choiceMixin.

Definition gen0 := inFA 0.
Definition genN (x : FA) := inFA (- val x).
Definition genD (x y : FA) := inFA (val x + val y).

Lemma gen_addA : associative genD.
Proof. by move=> x y z; apply: val_inj; rewrite /= addrA. Qed.

Lemma gen_addC : commutative genD.
Proof. by move=> x y; apply: val_inj; rewrite /= addrC. Qed.

Lemma gen_add0r : left_id gen0 genD.
Proof. by move=> x; apply: val_inj; rewrite /= add0r. Qed.

Lemma gen_addNr : left_inverse gen0 genN genD.
Proof. by move=> x; apply: val_inj; rewrite /= addNr. Qed.

Definition gen_zmodMixin := ZmodMixin gen_addA gen_addC gen_add0r gen_addNr.
Canonical gen_zmodType := Eval hnf in ZmodType FA gen_zmodMixin.

Definition pval (x : FA) := rVpoly (val x).

Definition mxval (x : FA) := horner_mx A (pval x).

Definition gen (x : F) := inFA (poly_rV x%:P).

Lemma genK x : mxval (gen x) = x%:M.
Proof.
by rewrite /mxval [pval _]poly_rV_K ?horner_mx_C // size_polyC; case: (x != 0).
Qed.

Lemma mxval_inj : injective mxval.
Proof. exact: inj_comp horner_rVpoly_inj val_inj. Qed.

Lemma mxval0 : mxval 0 = 0.
Proof. by rewrite /mxval [pval _]raddf0 rmorph0. Qed.

Lemma mxvalN : {morph mxval : x / - x}.
Proof. by move=> x; rewrite /mxval [pval _]raddfN rmorphN. Qed.

Lemma mxvalD : {morph mxval : x y / x + y}.
Proof. by move=> x y; rewrite /mxval [pval _]raddfD rmorphD. Qed.

Definition mxval_sum := big_morph mxval mxvalD mxval0.

Definition gen1 := inFA (poly_rV 1).
Definition genM x y := inFA (poly_rV (pval x * pval y %% pA)).
Definition genV x := inFA (poly_rV (mx_inv_horner A (mxval x)^-1)).

Lemma mxval_gen1 : mxval gen1 = 1%:M.
Proof. by rewrite /mxval [pval _]poly_rV_K ?size_poly1 // horner_mx_C. Qed.

Lemma mxval_genM : {morph mxval : x y / genM x y >-> x *m y}.
Proof.
move=> x y; rewrite /mxval [pval _]poly_rV_K ?size_mod_mxminpoly //.
by rewrite -horner_mxK mx_inv_hornerK ?horner_mx_mem // rmorphM.
Qed.

Lemma mxval_genV : {morph mxval : x / genV x >-> invmx x}.
Proof.
move=> x; rewrite /mxval [pval _]poly_rV_K ?size_poly ?mx_inv_hornerK //.
pose m B : 'M[F]_(n * n) := lin_mx (mulmxr B); set B := mxval x.
case uB: (B \is a GRing.unit); last by rewrite invr_out ?uB ?horner_mx_mem.
have defAd: Ad = Ad *m m B *m m B^-1.
  apply/row_matrixP=> i.
  by rewrite !row_mul mul_rV_lin /= mx_rV_lin /= mulmxK ?vec_mxK.
rewrite -[B^-1]mul1mx -(mul_vec_lin (mulmxr_linear _ _)) defAd submxMr //.
rewrite -mxval_gen1 (submx_trans (horner_mx_mem _ _)) // {1}defAd.
rewrite -(geq_leqif (mxrank_leqif_sup _)) ?mxrankM_maxl // -{}defAd.
apply/row_subP=> i; rewrite row_mul rowK mul_vec_lin /= -{2}[A]horner_mx_X.
by rewrite -rmorphX mulmxE -rmorphM horner_mx_mem.
Qed.

Lemma gen_mulA : associative genM.
Proof. by move=> x y z; apply: mxval_inj; rewrite !mxval_genM mulmxA. Qed.

Lemma gen_mulC : commutative genM.
Proof. by move=> x y; rewrite /genM mulrC. Qed.

Lemma gen_mul1r : left_id gen1 genM.
Proof. by move=> x; apply: mxval_inj; rewrite mxval_genM mxval_gen1 mul1mx. Qed.

Lemma gen_mulDr : left_distributive genM +%R.
Proof.
by move=> x y z; apply: mxval_inj; rewrite !(mxvalD, mxval_genM) mulmxDl.
Qed.

Lemma gen_ntriv : gen1 != 0.
Proof. by rewrite -(inj_eq mxval_inj) mxval_gen1 mxval0 oner_eq0. Qed.

Definition gen_ringMixin :=
  ComRingMixin gen_mulA gen_mulC gen_mul1r gen_mulDr gen_ntriv.
Canonical gen_ringType := Eval hnf in RingType FA gen_ringMixin.
Canonical gen_comRingType := Eval hnf in ComRingType FA gen_mulC.

Lemma mxval1 : mxval 1 = 1%:M. Proof. exact: mxval_gen1. Qed.

Lemma mxvalM : {morph mxval : x y / x * y >-> x *m y}.
Proof. exact: mxval_genM. Qed.

Lemma mxval_sub : additive mxval.
Proof. by move=> x y; rewrite mxvalD mxvalN. Qed.
Canonical mxval_additive := Additive mxval_sub.

Lemma mxval_is_multiplicative : multiplicative mxval.
Proof. by split; [apply: mxvalM | apply: mxval1]. Qed.
Canonical mxval_rmorphism := AddRMorphism mxval_is_multiplicative.

Lemma mxval_centg x : centgmx rG (mxval x).
Proof.
rewrite [mxval _]horner_rVpoly -memmx_cent_envelop vec_mxK {x}mulmx_sub //.
apply/row_subP=> k; rewrite rowK memmx_cent_envelop; apply/centgmxP => g Gg /=.
by rewrite !mulmxE commrX // /GRing.comm -mulmxE (centgmxP cGA).
Qed.

Lemma gen_mulVr : GRing.Field.axiom genV.
Proof.
move=> x; rewrite -(inj_eq mxval_inj) mxval0.
move/(mx_Schur irrG (mxval_centg x)) => u_x.
by apply: mxval_inj; rewrite mxvalM mxval_genV mxval1 mulVmx.
Qed.

Lemma gen_invr0 : genV 0 = 0.
Proof. by apply: mxval_inj; rewrite mxval_genV !mxval0 -{2}invr0. Qed.

Definition gen_unitRingMixin := FieldUnitMixin gen_mulVr gen_invr0.
Canonical gen_unitRingType :=
  Eval hnf in UnitRingType FA gen_unitRingMixin.
Canonical gen_comUnitRingType := Eval hnf in [comUnitRingType of FA].
Definition gen_fieldMixin :=
  @FieldMixin _ _ _ _ : GRing.Field.mixin_of gen_unitRingType.
Definition gen_idomainMixin := FieldIdomainMixin gen_fieldMixin.
Canonical gen_idomainType := Eval hnf in IdomainType FA gen_idomainMixin.
Canonical gen_fieldType := Eval hnf in FieldType FA gen_fieldMixin.

Lemma mxvalV : {morph mxval : x / x^-1 >-> invmx x}.
Proof. exact: mxval_genV. Qed.

Lemma gen_is_rmorphism : rmorphism gen.
Proof.
split=> [x y|]; first by apply: mxval_inj; rewrite genK !rmorphB /= !genK.
by split=> // x y; apply: mxval_inj; rewrite genK !rmorphM /= !genK.
Qed.
Canonical gen_additive := Additive gen_is_rmorphism.
Canonical gen_rmorphism := RMorphism gen_is_rmorphism.

(* The generated field contains a root of the minimal polynomial (in some  *)
(* cases we want to use the construction solely for that purpose).         *)

Definition groot := inFA (poly_rV ('X %% pA)).

Lemma mxval_groot : mxval groot = A.
Proof.
rewrite /mxval [pval _]poly_rV_K ?size_mod_mxminpoly // -horner_mxK.
by rewrite mx_inv_hornerK ?horner_mx_mem // horner_mx_X.
Qed.

Lemma mxval_grootX k : mxval (groot ^+ k) = A ^+ k.
Proof. by rewrite rmorphX /= mxval_groot. Qed.

Lemma map_mxminpoly_groot : (map_poly gen pA).[groot] = 0.
Proof. (* The [_ groot] prevents divergence of simpl. *)
apply: mxval_inj; rewrite -horner_map [_ groot]/= mxval_groot mxval0.
rewrite -(mx_root_minpoly A); congr ((_ : {poly _}).[A]).
by apply/polyP=> i; rewrite 3!coef_map; apply: genK.
Qed.

(* Plugging the extension morphism gen into the ext_repr construction   *)
(* yields a (reducible) tensored representation.                           *)

Lemma non_linear_gen_reducible :
  d > 1 -> mxnonsimple (map_repr gen_rmorphism rG) 1%:M.
Proof.
rewrite ltnNge mxminpoly_linear_is_scalar => Anscal.
pose Af := map_mx gen A; exists (kermx (Af - groot%:M)).
rewrite submx1 kermx_centg_module /=; last first.
  apply/centgmxP=> z Gz; rewrite mulmxBl mulmxBr scalar_mxC.
  by rewrite -!map_mxM 1?(centgmxP cGA).
rewrite andbC mxrank_ker -subn_gt0 mxrank1 subKn ?rank_leq_row // lt0n.
rewrite mxrank_eq0 subr_eq0; case: eqP => [defAf | _].
  rewrite -(map_mx_is_scalar gen_rmorphism) -/Af in Anscal.
  by case/is_scalar_mxP: Anscal; exists groot.
rewrite -mxrank_eq0 mxrank_ker subn_eq0 row_leq_rank.
apply/row_freeP=> [[XA' XAK]].
have pAf0: (mxminpoly Af).[groot] == 0.
  by rewrite mxminpoly_map ?map_mxminpoly_groot.
have{pAf0} [q def_pAf]:= factor_theorem _ _ pAf0.
have q_nz: q != 0.
  case: eqP (congr1 (fun p : {poly _} => size p) def_pAf) => // ->.
  by rewrite size_mxminpoly mul0r size_poly0.
have qAf0: horner_mx Af q = 0.
  rewrite -[_ q]mulr1 -[1]XAK mulrA -{2}(horner_mx_X Af) -(horner_mx_C Af).
  by rewrite -rmorphB -rmorphM -def_pAf /= mx_root_minpoly mul0r.
have{qAf0} := dvdp_leq q_nz (mxminpoly_min qAf0); rewrite def_pAf.
by rewrite size_Mmonic ?monicXsubC // polyseqXsubC addn2 ltnn.
Qed.

(* An alternative to the above, used in the proof of the p-stability of       *)
(* groups of odd order, is to reconsider the original vector space as a       *)
(* vector space of dimension n / e over FA. This is applicable only if G is   *)
(* the largest group represented on the original vector space (i.e., if we    *)
(* are not studying a representation of G induced by one of a larger group,   *)
(* as in B & G Theorem 2.6 for instance). We can't fully exploit one of the   *)
(* benefits of this approach -- that the type domain for the vector space can *)
(* remain unchanged -- because we're restricting ourselves to row matrices;   *)
(* we have to use explicit bijections to convert between the two views.       *)

Definition subbase nA (B : 'rV_nA) : 'M_(nA * d, n) :=
  \matrix_ik mxvec (\matrix_(i, k) (row (B 0 i) (A ^+ k))) 0 ik.

Lemma gen_dim_ex_proof : exists nA, [exists B : 'rV_nA, row_free (subbase B)].
Proof. by exists 0%N; apply/existsP; exists 0. Qed.

Lemma gen_dim_ub_proof nA :
  [exists B : 'rV_nA, row_free (subbase B)] -> (nA <= n)%N.
Proof.
case/existsP=> B /eqnP def_nAd.
by rewrite (leq_trans _ (rank_leq_col (subbase B))) // def_nAd leq_pmulr.
Qed.

Definition gen_dim := ex_maxn gen_dim_ex_proof gen_dim_ub_proof.
Notation nA := gen_dim.

Definition gen_base : 'rV_nA := odflt 0 [pick B | row_free (subbase B)].
Definition base := subbase gen_base.

Lemma base_free : row_free base.
Proof.
rewrite /base /gen_base /nA; case: pickP => //; case: ex_maxnP => nA_max.
by case/existsP=> B Bfree _ no_free; rewrite no_free in Bfree.
Qed.

Lemma base_full : row_full base.
Proof.
rewrite /row_full (eqnP base_free) /nA; case: ex_maxnP => nA.
case/existsP=> /= B /eqnP Bfree nA_max; rewrite -Bfree eqn_leq rank_leq_col.
rewrite -{1}(mxrank1 F n) mxrankS //; apply/row_subP=> j; set u := row _ _.
move/implyP: {nA_max}(nA_max nA.+1); rewrite ltnn implybF.
apply: contraR => nBj; apply/existsP.
exists (row_mx (const_mx j : 'M_1) B); rewrite -row_leq_rank.
pose Bj := Ad *m lin1_mx (mulmx u \o vec_mx).
have rBj: \rank Bj = d.
  apply/eqP; rewrite eqn_leq rank_leq_row -subn_eq0 -mxrank_ker mxrank_eq0 /=.
  apply/rowV0P=> v /sub_kermxP; rewrite mulmxA mul_rV_lin1 /=.
  rewrite -horner_rVpoly; pose x := inFA v; rewrite -/(mxval x).
  have [[] // | nzx /(congr1 (mulmx^~ (mxval x^-1)))] := eqVneq x 0.
  rewrite mul0mx /= -mulmxA -mxvalM divff // mxval1 mulmx1.
  by move/rowP/(_ j)/eqP; rewrite !mxE !eqxx oner_eq0.
rewrite {1}mulSn -Bfree -{1}rBj {rBj} -mxrank_disjoint_sum.
  rewrite mxrankS // addsmx_sub -[nA.+1]/(1 + nA)%N; apply/andP; split.
    apply/row_subP=> k; rewrite row_mul mul_rV_lin1 /=.
    apply: eq_row_sub (mxvec_index (lshift _ 0) k)  _.
    by rewrite !rowK mxvecK mxvecE mxE row_mxEl mxE -row_mul mul1mx.
  apply/row_subP; case/mxvec_indexP=> i k.
  apply: eq_row_sub (mxvec_index (rshift 1 i) k) _.
  by rewrite !rowK !mxvecE 2!mxE row_mxEr.
apply/eqP/rowV0P=> v; rewrite sub_capmx => /andP[/submxP[w]].
set x := inFA w; rewrite {Bj}mulmxA mul_rV_lin1 /= -horner_rVpoly -/(mxval x).
have [-> | nzx ->] := eqVneq x 0; first by rewrite mxval0 mulmx0.
move/(submxMr (mxval x^-1)); rewrite -mulmxA -mxvalM divff {nzx}//.
rewrite mxval1 mulmx1 => Bx'j; rewrite (submx_trans Bx'j) in nBj => {Bx'j} //.
apply/row_subP; case/mxvec_indexP=> i k.
rewrite row_mul rowK mxvecE mxE rowE -mulmxA.
have ->: A ^+ k *m mxval x^-1 = mxval (groot ^+ k / x).
  by rewrite mxvalM rmorphX /= mxval_groot.
rewrite [mxval _]horner_rVpoly; move: {k u x}(val _) => u.
rewrite (mulmx_sum_row u) !linear_sum summx_sub //= => k _.
rewrite !linearZ scalemx_sub //= rowK mxvecK -rowE.
by apply: eq_row_sub (mxvec_index i k) _; rewrite rowK mxvecE mxE.
Qed.

Lemma gen_dim_factor : (nA * d)%N = n.
Proof. by rewrite -(eqnP base_free) (eqnP base_full). Qed.

Lemma gen_dim_gt0 : nA > 0.
Proof. by case: posnP gen_dim_factor => // ->. Qed.

Section Bijection.

Variable m : nat.

Definition in_gen (W : 'M[F]_(m, n)) : 'M[FA]_(m, nA) :=
  \matrix_(i, j) inFA (row j (vec_mx (row i W *m pinvmx base))).

Definition val_gen (W : 'M[FA]_(m, nA)) : 'M[F]_(m, n) :=
  \matrix_i (mxvec (\matrix_j val (W i j)) *m base).

Lemma in_genK : cancel in_gen val_gen.
Proof.
move=> W; apply/row_matrixP=> i; rewrite rowK; set w := row i W.
have b_w: (w <= base)%MS by rewrite submx_full ?base_full.
rewrite -{b_w}(mulmxKpV b_w); congr (_ *m _).
by apply/rowP; case/mxvec_indexP=> j k; rewrite mxvecE !mxE.
Qed.

Lemma val_genK : cancel val_gen in_gen.
Proof.
move=> W; apply/matrixP=> i j; apply: val_inj; rewrite mxE /= rowK.
case/row_freeP: base_free => B' BB'; rewrite -[_ *m _]mulmx1 -BB' mulmxA.
by rewrite mulmxKpV ?submxMl // -mulmxA BB' mulmx1 mxvecK rowK.
Qed.

Lemma in_gen0 : in_gen 0 = 0.
Proof. by apply/matrixP=> i j; rewrite !mxE !(mul0mx, linear0). Qed.

Lemma val_gen0 : val_gen 0 = 0.
Proof. by apply: (canLR in_genK); rewrite in_gen0. Qed.

Lemma in_genN : {morph in_gen : W / - W}.
Proof.
move=> W; apply/matrixP=> i j; apply: val_inj.
by rewrite !mxE !(mulNmx, linearN).
Qed.

Lemma val_genN : {morph val_gen : W / - W}.
Proof. by move=> W; apply: (canLR in_genK); rewrite in_genN val_genK. Qed.

Lemma in_genD : {morph in_gen : U V / U + V}.
Proof.
move=> U V; apply/matrixP=> i j; apply: val_inj.
by rewrite !mxE !(mulmxDl, linearD).
Qed.

Lemma val_genD : {morph val_gen : U V / U + V}.
Proof. by move=> U V; apply: (canLR in_genK); rewrite in_genD !val_genK. Qed.

Definition in_gen_sum := big_morph in_gen in_genD in_gen0.
Definition val_gen_sum := big_morph val_gen val_genD val_gen0.

Lemma in_genZ a : {morph in_gen : W / a *: W >-> gen a *: W}.
Proof.
move=> W; apply/matrixP=> i j; apply: mxval_inj.
rewrite !mxE mxvalM genK ![mxval _]horner_rVpoly /=.
by rewrite mul_scalar_mx !(I, scalemxAl, linearZ).
Qed.

End Bijection.

Prenex Implicits val_genK in_genK.

Lemma val_gen_rV (w : 'rV_nA) :
  val_gen w = mxvec (\matrix_j val (w 0 j)) *m base.
Proof. by apply/rowP=> j; rewrite mxE. Qed.

Section Bijection2.

Variable m : nat.

Lemma val_gen_row W (i : 'I_m) : val_gen (row i W) = row i (val_gen W).
Proof.
rewrite val_gen_rV rowK; congr (mxvec _ *m _).
by apply/matrixP=> j k; rewrite !mxE.
Qed.

Lemma in_gen_row W (i : 'I_m) : in_gen (row i W) = row i (in_gen W).
Proof. by apply: (canLR val_genK); rewrite val_gen_row in_genK. Qed.

Lemma row_gen_sum_mxval W (i : 'I_m) :
  row i (val_gen W) = \sum_j row (gen_base 0 j) (mxval (W i j)).
Proof.
rewrite -val_gen_row [row i W]row_sum_delta val_gen_sum.
apply: eq_bigr => /= j _; rewrite mxE; move: {W i}(W i j) => x.
have ->: x = \sum_k gen (val x 0 k) * inFA (delta_mx 0 k).
  case: x => u; apply: mxval_inj; rewrite {1}[u]row_sum_delta.
  rewrite mxval_sum [mxval _]horner_rVpoly mulmx_suml linear_sum /=.
  apply: eq_bigr => k _; rewrite mxvalM genK [mxval _]horner_rVpoly /=.
  by rewrite mul_scalar_mx -scalemxAl linearZ.
rewrite scaler_suml val_gen_sum mxval_sum linear_sum; apply: eq_bigr => k _.
rewrite mxvalM genK mul_scalar_mx linearZ [mxval _]horner_rVpoly /=.
rewrite -scalerA; apply: (canLR in_genK); rewrite in_genZ; congr (_ *: _).
apply: (canRL val_genK); transitivity (row (mxvec_index j k) base); last first.
  by rewrite -rowE rowK mxvecE mxE rowK mxvecK.
rewrite rowE -mxvec_delta -[val_gen _](row_id 0) rowK /=; congr (mxvec _ *m _).
apply/row_matrixP=> j'; rewrite rowK !mxE mulr_natr rowE mul_delta_mx_cond.
by rewrite !mulrb (fun_if rVval).
Qed.

Lemma val_genZ x : {morph @val_gen m : W / x *: W >-> W *m mxval x}.
Proof.
move=> W; apply/row_matrixP=> i; rewrite row_mul !row_gen_sum_mxval.
by rewrite mulmx_suml; apply: eq_bigr => j _; rewrite mxE mulrC mxvalM row_mul.
Qed.

End Bijection2.

Lemma submx_in_gen m1 m2 (U : 'M_(m1, n)) (V : 'M_(m2, n)) :
  (U <= V -> in_gen U <= in_gen V)%MS.
Proof.
move=> sUV; apply/row_subP=> i; rewrite -in_gen_row.
case/submxP: (row_subP sUV i) => u ->{i}.
rewrite mulmx_sum_row in_gen_sum summx_sub // => j _.
by rewrite in_genZ in_gen_row scalemx_sub ?row_sub.
Qed.

Lemma submx_in_gen_eq m1 m2 (U : 'M_(m1, n)) (V : 'M_(m2, n)) :
  (V *m A <= V -> (in_gen U <= in_gen V) = (U <= V))%MS.
Proof.
move=> sVA_V; apply/idP/idP=> siUV; last exact: submx_in_gen.
apply/row_subP=> i; rewrite -[row i U]in_genK in_gen_row.
case/submxP: (row_subP siUV i) => u ->{i U siUV}.
rewrite mulmx_sum_row val_gen_sum summx_sub // => j _.
rewrite val_genZ val_gen_row in_genK rowE -mulmxA mulmx_sub //.
rewrite [mxval _]horner_poly mulmx_sumr summx_sub // => [[k _]] _ /=.
rewrite mulmxA mul_mx_scalar -scalemxAl scalemx_sub {u j}//.
elim: k => [|k IHk]; first by rewrite mulmx1.
by rewrite exprSr mulmxA (submx_trans (submxMr A IHk)).
Qed.

Definition gen_mx g := \matrix_i in_gen (row (gen_base 0 i) (rG g)).

Let val_genJmx m :
  {in G, forall g, {morph @val_gen m : W / W *m gen_mx g >-> W *m rG g}}.
Proof.
move=> g Gg /= W; apply/row_matrixP=> i; rewrite -val_gen_row !row_mul.
rewrite mulmx_sum_row val_gen_sum row_gen_sum_mxval mulmx_suml.
apply: eq_bigr => /= j _; rewrite val_genZ rowK in_genK mxE -!row_mul.
by rewrite (centgmxP (mxval_centg _)).
Qed.

Lemma gen_mx_repr : mx_repr G gen_mx.
Proof.
split=> [|g h Gg Gh]; apply: (can_inj val_genK).
  by rewrite -[gen_mx 1]mul1mx val_genJmx // repr_mx1 mulmx1.
rewrite {1}[val_gen]lock -[gen_mx g]mul1mx !val_genJmx // -mulmxA -repr_mxM //.
by rewrite -val_genJmx ?groupM ?mul1mx -?lock.
Qed.
Canonical gen_repr := MxRepresentation gen_mx_repr.
Local Notation rGA := gen_repr.

Lemma val_genJ m :
  {in G, forall g, {morph @val_gen m : W / W *m rGA g >-> W *m rG g}}.
Proof. exact: val_genJmx. Qed.

Lemma in_genJ m :
  {in G, forall g, {morph @in_gen m : v / v *m rG g >-> v *m rGA g}}.
Proof.
by move=> g Gg /= v; apply: (canLR val_genK); rewrite val_genJ ?in_genK.
Qed.

Lemma rfix_gen (H : {set gT}) :
  H \subset G -> (rfix_mx rGA H :=: in_gen (rfix_mx rG H))%MS.
Proof.
move/subsetP=> sHG; apply/eqmxP/andP; split; last first.
  by apply/rfix_mxP=> g Hg; rewrite -in_genJ ?sHG ?rfix_mx_id.
rewrite -[rfix_mx rGA H]val_genK; apply: submx_in_gen.
by apply/rfix_mxP=> g Hg; rewrite -val_genJ ?rfix_mx_id ?sHG.
Qed.

Definition rowval_gen m U :=
  <<\matrix_ik
      mxvec (\matrix_(i < m, k < d) (row i (val_gen U) *m A ^+ k)) 0 ik>>%MS.

Lemma submx_rowval_gen m1 m2 (U : 'M_(m1, n)) (V : 'M_(m2, nA)) :
  (U <= rowval_gen V)%MS = (in_gen U <= V)%MS.
Proof.
rewrite genmxE; apply/idP/idP=> sUV.
  apply: submx_trans (submx_in_gen sUV) _.
  apply/row_subP; case/mxvec_indexP=> i k; rewrite -in_gen_row rowK mxvecE mxE.
  rewrite -mxval_grootX -val_gen_row -val_genZ val_genK scalemx_sub //.
  exact: row_sub.
rewrite -[U]in_genK; case/submxP: sUV => u ->{U}.
apply/row_subP=> i0; rewrite -val_gen_row row_mul; move: {i0 u}(row _ u) => u.
rewrite mulmx_sum_row val_gen_sum summx_sub // => i _.
rewrite val_genZ [mxval _]horner_rVpoly [_ *m Ad]mulmx_sum_row.
rewrite !linear_sum summx_sub // => k _.
rewrite !linearZ scalemx_sub {u}//= rowK mxvecK val_gen_row.
by apply: (eq_row_sub (mxvec_index i k)); rewrite rowK mxvecE mxE.
Qed.

Lemma rowval_genK m (U : 'M_(m,  nA)) : (in_gen (rowval_gen U) :=: U)%MS.
Proof.
apply/eqmxP; rewrite -submx_rowval_gen submx_refl /=.
by rewrite -{1}[U]val_genK submx_in_gen // submx_rowval_gen val_genK.
Qed.

Lemma rowval_gen_stable m (U : 'M_(m, nA)) :
  (rowval_gen U *m A <= rowval_gen U)%MS.
Proof.
rewrite -[A]mxval_groot -{1}[_ U]in_genK -val_genZ.
by rewrite submx_rowval_gen val_genK scalemx_sub // rowval_genK.
Qed.

Lemma rstab_in_gen m (U : 'M_(m, n)) : rstab rGA (in_gen U) = rstab rG U.
Proof.
apply/setP=> x; rewrite !inE; case Gx: (x \in G) => //=.
by rewrite -in_genJ // (inj_eq (can_inj in_genK)).
Qed.

Lemma rstabs_in_gen m (U : 'M_(m, n)) :
  rstabs rG U \subset rstabs rGA (in_gen U).
Proof.
apply/subsetP=> x; rewrite !inE => /andP[Gx nUx].
by rewrite -in_genJ Gx // submx_in_gen.
Qed.

Lemma rstabs_rowval_gen m (U : 'M_(m, nA)) :
  rstabs rG (rowval_gen U) = rstabs rGA U.
Proof.
apply/setP=> x; rewrite !inE; case Gx: (x \in G) => //=.
by rewrite submx_rowval_gen in_genJ // (eqmxMr _ (rowval_genK U)).
Qed.

Lemma mxmodule_rowval_gen m (U : 'M_(m, nA)) :
  mxmodule rG (rowval_gen U) = mxmodule rGA U.
Proof. by rewrite /mxmodule rstabs_rowval_gen. Qed.

Lemma gen_mx_irr : mx_irreducible rGA.
Proof.
apply/mx_irrP; split=> [|U Umod nzU]; first exact: gen_dim_gt0.
rewrite -sub1mx -rowval_genK -submx_rowval_gen submx_full //.
case/mx_irrP: irrG => _; apply; first by rewrite mxmodule_rowval_gen.
rewrite -(inj_eq (can_inj in_genK)) in_gen0.
by rewrite -mxrank_eq0 rowval_genK mxrank_eq0.
Qed.

Lemma rker_gen : rker rGA = rker rG.
Proof.
apply/setP=> g; rewrite !inE !mul1mx; case Gg: (g \in G) => //=.
apply/eqP/eqP=> g1; apply/row_matrixP=> i.
  by apply: (can_inj in_genK); rewrite rowE in_genJ //= g1 mulmx1 row1.
by apply: (can_inj val_genK); rewrite rowE val_genJ //= g1 mulmx1 row1.
Qed.

Lemma gen_mx_faithful : mx_faithful rGA = mx_faithful rG.
Proof. by rewrite /mx_faithful rker_gen. Qed.

End GenField.

Section DecideGenField.

Import MatrixFormula.

Variable F : decFieldType.

Local Notation False := GRing.False.
Local Notation True := GRing.True.
Local Notation Bool b := (GRing.Bool b%bool).
Local Notation term := (GRing.term F).
Local Notation form := (GRing.formula F).

Local Notation morphAnd f := ((big_morph f) true andb).

Variables (gT : finGroupType) (G : {group gT}) (n' : nat).
Local Notation n := n'.+1.
Variables (rG : mx_representation F G n) (A : 'M[F]_n).
Hypotheses (irrG : mx_irreducible rG) (cGA : centgmx rG A).
Local Notation FA := (gen_of irrG cGA).
Local Notation inFA := (Gen irrG cGA).

Local Notation d := (degree_mxminpoly A).
Let d_gt0 : d > 0 := mxminpoly_nonconstant A.
Local Notation Ad := (powers_mx A d).

Let mxT (u : 'rV_d) := vec_mx (mulmx_term u (mx_term Ad)).

Let eval_mxT e u : eval_mx e (mxT u) = mxval (inFA (eval_mx e u)).
Proof.
by rewrite eval_vec_mx eval_mulmx eval_mx_term [mxval _]horner_rVpoly.
Qed.

Let Ad'T := mx_term (pinvmx Ad).
Let mulT (u v : 'rV_d) := mulmx_term (mxvec (mulmx_term (mxT u) (mxT v))) Ad'T.

Lemma eval_mulT e u v :
  eval_mx e (mulT u v) = val (inFA (eval_mx e u) * inFA (eval_mx e v)).
Proof.
rewrite !(eval_mulmx, eval_mxvec) !eval_mxT eval_mx_term.
by apply: (can_inj rVpolyK); rewrite -mxvalM [rVpoly _]horner_rVpolyK.
Qed.

Fixpoint gen_term t := match t with
| 'X_k => row_var _ d k
| x%:T => mx_term (val (x : FA))
| n1%:R => mx_term (val (n1%:R : FA))%R
| t1 + t2 => \row_i (gen_term t1 0%R i + gen_term t2 0%R i)
| - t1 => \row_i (- gen_term t1 0%R i)
| t1 *+ n1 => mulmx_term (mx_term n1%:R%:M)%R (gen_term t1)
| t1 * t2 => mulT (gen_term t1) (gen_term t2)
| t1^-1 => gen_term t1
| t1 ^+ n1 => iter n1 (mulT (gen_term t1)) (mx_term (val (1%R : FA)))
end%T.

Definition gen_env (e : seq FA) := row_env (map val e).

Lemma nth_map_rVval (e : seq FA) j : (map val e)`_j = val e`_j.
Proof.
case: (ltnP j (size e)) => [| leej]; first exact: (nth_map 0 0).
by rewrite !nth_default ?size_map.
Qed.

Lemma set_nth_map_rVval (e : seq FA) j v :
  set_nth 0 (map val e) j v = map val (set_nth 0 e j (inFA v)).
Proof.
apply: (@eq_from_nth _ 0) => [|k _]; first by rewrite !(size_set_nth, size_map).
by rewrite !(nth_map_rVval, nth_set_nth) /= nth_map_rVval [rVval _]fun_if.
Qed.

Lemma eval_gen_term e t : 
  GRing.rterm t -> eval_mx (gen_env e) (gen_term t) = val (GRing.eval e t).
Proof.
elim: t => //=.
- by move=> k _; apply/rowP=> i; rewrite !mxE /= nth_row_env nth_map_rVval.
- by move=> x _; rewrite eval_mx_term.
- by move=> x _; rewrite eval_mx_term.
- move=> t1 IH1 t2 IH2 /andP[rt1 rt2]; rewrite -{}IH1 // -{}IH2 //.
  by apply/rowP=> k; rewrite !mxE.
- by move=> t1 IH1 rt1; rewrite -{}IH1 //; apply/rowP=> k; rewrite !mxE.
- move=> t1 IH1 n1 rt1; rewrite eval_mulmx eval_mx_term mul_scalar_mx.
  by rewrite scaler_nat {}IH1 //; elim: n1 => //= n1 IHn1; rewrite !mulrS IHn1.
- by move=> t1 IH1 t2 IH2 /andP[rt1 rt2]; rewrite eval_mulT IH1 ?IH2.
move=> t1 IH1 n1 /IH1 {IH1}IH1.
elim: n1 => [|n1 IHn1] /=; first by rewrite eval_mx_term.
by rewrite eval_mulT exprS IH1 IHn1.
Qed.

Fixpoint gen_form f := match f with
| Bool b => Bool b
| t1 == t2 => mxrank_form 0 (gen_term (t1 - t2))
| GRing.Unit t1 => mxrank_form 1 (gen_term t1)
| f1 /\ f2 => gen_form f1 /\ gen_form f2
| f1 \/ f2 =>  gen_form f1 \/ gen_form f2
| f1 ==> f2 => gen_form f1 ==> gen_form f2
| ~ f1 => ~ gen_form f1
| ('exists 'X_k, f1) => Exists_row_form d k (gen_form f1)
| ('forall 'X_k, f1) => ~ Exists_row_form d k (~ (gen_form f1))
end%T.

Lemma sat_gen_form e f : GRing.rformula f ->
  reflect (GRing.holds e f) (GRing.sat (gen_env e) (gen_form f)).
Proof.
have ExP := Exists_rowP; have set_val := set_nth_map_rVval.
elim: f e => //.
- by move=> b e _; apply: (iffP satP).
- rewrite /gen_form => t1 t2 e rt_t; set t := (_ - _)%T.
  have:= GRing.qf_evalP (gen_env e) (mxrank_form_qf 0 (gen_term t)).
  rewrite eval_mxrank mxrank_eq0 eval_gen_term // => tP.
  by rewrite (sameP satP tP) /= subr_eq0 val_eqE; apply: eqP.
- move=> f1 IH1 f2 IH2 s /= /andP[/(IH1 s)f1P /(IH2 s)f2P].
  by apply: (iffP satP) => [[/satP/f1P ? /satP/f2P] | [/f1P/satP ? /f2P/satP]].
- move=> f1 IH1 f2 IH2 s /= /andP[/(IH1 s)f1P /(IH2 s)f2P].
  by apply: (iffP satP) => /= [] [];
    try move/satP; do [move/f1P | move/f2P]; try move/satP; auto.
- move=> f1 IH1 f2 IH2 s /= /andP[/(IH1 s)f1P /(IH2 s)f2P].
  by apply: (iffP satP) => /= implP;
    try move/satP; move/f1P; try move/satP; move/implP;
    try move/satP; move/f2P; try move/satP.
- move=> f1 IH1 s /= /(IH1 s) f1P.
  by apply: (iffP satP) => /= notP; try move/satP; move/f1P; try move/satP.
- move=> k f1 IHf1 s /IHf1 f1P; apply: (iffP satP) => /= [|[[v f1v]]].
    by case/ExP=> // x /satP; rewrite set_val => /f1P; exists (inFA x).
  by apply/ExP=> //; exists v; rewrite set_val; apply/satP/f1P.
move=> i f1 IHf1 s /IHf1 f1P; apply: (iffP satP) => /= allf1 => [[v]|].
  apply/f1P; case: satP => // notf1x; case: allf1; apply/ExP=> //.
  by exists v; rewrite set_val.
by case/ExP=> //= v []; apply/satP; rewrite set_val; apply/f1P.
Qed.

Definition gen_sat e f := GRing.sat (gen_env e) (gen_form (GRing.to_rform f)).

Lemma gen_satP : GRing.DecidableField.axiom gen_sat.
Proof.
move=> e f; have [tor rto] := GRing.to_rformP e f.
exact: (iffP (sat_gen_form e (GRing.to_rform_rformula f))).
Qed.

Definition gen_decFieldMixin := DecFieldMixin gen_satP.

Canonical gen_decFieldType := Eval hnf in DecFieldType FA gen_decFieldMixin.

End DecideGenField.

Section FiniteGenField.

Variables (F : finFieldType) (gT : finGroupType) (G : {group gT}) (n' : nat).
Local Notation n := n'.+1.
Variables (rG : mx_representation F G n) (A : 'M[F]_n).
Hypotheses (irrG : mx_irreducible rG) (cGA : centgmx rG A).
Notation FA := (gen_of irrG cGA).

(* This should be [countMixin of FA by <:]*)
Definition gen_countMixin := (sub_countMixin (gen_subType irrG cGA)).
Canonical gen_countType := Eval hnf in CountType FA gen_countMixin.
Canonical gen_subCountType := Eval hnf in [subCountType of FA].
Definition gen_finMixin := [finMixin of FA by <:].
Canonical gen_finType := Eval hnf in FinType FA gen_finMixin.
Canonical gen_subFinType := Eval hnf in [subFinType of FA].
Canonical gen_finZmodType := Eval hnf in [finZmodType of FA].
Canonical gen_baseFinGroupType := Eval hnf in [baseFinGroupType of FA for +%R].
Canonical gen_finGroupType := Eval hnf in [finGroupType of FA for +%R].
Canonical gen_finRingType := Eval hnf in [finRingType of FA].
Canonical gen_finComRingType := Eval hnf in [finComRingType of FA].
Canonical gen_finUnitRingType := Eval hnf in [finUnitRingType of FA].
Canonical gen_finComUnitRingType := Eval hnf in [finComUnitRingType of FA].
Canonical gen_finIdomainType := Eval hnf in [finIdomainType of FA].
Canonical gen_finFieldType := Eval hnf in [finFieldType of FA].

Lemma card_gen : #|{:FA}| = (#|F| ^ degree_mxminpoly A)%N.
Proof. by rewrite card_sub card_matrix mul1n. Qed.

End FiniteGenField.

End MatrixGenField.

Bind Scope ring_scope with gen_of.
Arguments rVval {F gT G%G n'%N rG A%R irrG cGA} x%R : rename.
Prenex Implicits gen_of Gen rVval pval mxval gen groot.
Arguments subbase {F n'} A {nA}.
Prenex Implicits gen_dim gen_base base val_gen gen_mx rowval_gen.
Arguments in_gen {F gT G n' rG A} irrG cGA {m} W.
Arguments in_genK {F gT G n' rG A} irrG cGA {m} W : rename.
Arguments val_genK {F gT G n' rG A irrG cGA m} W : rename.
Prenex Implicits gen_env gen_term gen_form gen_sat.

Canonical gen_subType.
Canonical gen_eqType.
Canonical gen_choiceType.
Canonical gen_countType.
Canonical gen_subCountType.
Canonical gen_finType.
Canonical gen_subFinType.
Canonical gen_zmodType.
Canonical gen_finZmodType.
Canonical gen_baseFinGroupType.
Canonical gen_finGroupType.
Canonical gen_ringType.
Canonical gen_finRingType.
Canonical gen_comRingType.
Canonical gen_finComRingType.
Canonical gen_unitRingType.
Canonical gen_finUnitRingType.
Canonical gen_comUnitRingType.
Canonical gen_finComUnitRingType.
Canonical gen_idomainType.
Canonical gen_finIdomainType.
Canonical gen_fieldType.
Canonical gen_finFieldType.
Canonical gen_decFieldType.

(* Classical splitting and closure field constructions provide convenient     *)
(* packaging for the pointwise construction.                                  *)
Section BuildSplittingField.

Implicit Type gT : finGroupType.
Implicit Type F : fieldType.

Lemma group_splitting_field_exists gT (G : {group gT}) F :
  classically {Fs : fieldType & {rmorphism F -> Fs}
                              & group_splitting_field Fs G}.
Proof.
move: F => F0 [] // nosplit; pose nG := #|G|; pose aG F := regular_repr F G.
pose m := nG.+1; pose F := F0; pose U : seq 'M[F]_nG := [::].
suffices: size U + m <= nG by rewrite ltnn.
have: mx_subseries (aG F) U /\ path ltmx 0 U by [].
pose f : {rmorphism F0 -> F} := [rmorphism of idfun].
elim: m F U f => [|m IHm] F U f [modU ltU].
  by rewrite addn0 (leq_trans (max_size_mx_series ltU)) ?rank_leq_row.
rewrite addnS ltnNge -implybF; apply/implyP=> le_nG_Um; apply nosplit.
exists F => //; case=> [|n] rG irrG; first by case/mx_irrP: irrG.
apply/idPn=> nabsG; pose cG := ('C(enveloping_algebra_mx rG))%MS.
have{nabsG} [A]: exists2 A, (A \in cG)%MS & ~~ is_scalar_mx A.
  apply/has_non_scalar_mxP; rewrite ?scalar_mx_cent // ltnNge.
  by apply: contra nabsG; apply: cent_mx_scalar_abs_irr.
rewrite {cG}memmx_cent_envelop -mxminpoly_linear_is_scalar -ltnNge => cGA.
move/(non_linear_gen_reducible irrG cGA).
set F' := gen_fieldType _ _; set rG' := @map_repr _ F' _ _ _ _ rG.
move: F' (gen_rmorphism _ _ : {rmorphism F -> F'}) => F' f' in rG' * => irrG'.
pose U' := [seq map_mx f' Ui | Ui <- U].
have modU': mx_subseries (aG F') U'.
  apply: etrans modU; rewrite /mx_subseries all_map; apply: eq_all => Ui.
  rewrite -(mxmodule_map f'); apply: eq_subset_r => x.
  by rewrite !inE map_regular_repr.
case: notF; apply: (mx_Schreier modU ltU) => [[V [compV lastV sUV]]].
have{lastV} [] := rsim_regular_series irrG compV lastV.
have{sUV} defV: V = U.
  apply/eqP; rewrite eq_sym -(geq_leqif (size_subseq_leqif sUV)).
  rewrite -(leq_add2r m); apply: leq_trans le_nG_Um.
  by apply: IHm f _; rewrite (mx_series_lt compV); case: compV.
rewrite {V}defV in compV * => i rsimVi.
apply: (mx_Schreier modU') => [|[V' [compV' _ sUV']]].
  rewrite {modU' compV modU i le_nG_Um rsimVi}/U' -(map_mx0 f').
  by apply: etrans ltU; elim: U 0 => //= Ui U IHU Ui'; rewrite IHU map_ltmx.
have{sUV'} defV': V' = U'; last rewrite {V'}defV' in compV'.
  apply/eqP; rewrite eq_sym -(geq_leqif (size_subseq_leqif sUV')) size_map.
  rewrite -(leq_add2r m); apply: leq_trans le_nG_Um.
  apply: IHm [rmorphism of f' \o f] _.
  by rewrite (mx_series_lt compV'); case: compV'.
suffices{irrG'}: mx_irreducible rG' by case/mxsimpleP=> _ _ [].
have ltiU': i < size U' by rewrite size_map.
apply: mx_rsim_irr (mx_rsim_sym _ ) (mx_series_repr_irr compV' ltiU').
by apply: mx_rsim_trans (mx_rsim_map f' rsimVi) _; apply: map_regular_subseries.
Qed.

Lemma group_closure_field_exists gT F :
  classically {Fs : fieldType & {rmorphism F -> Fs}
                              & group_closure_field Fs gT}.
Proof.
set n := #|{group gT}|.
suffices: classically {Fs : fieldType & {rmorphism F -> Fs}
   & forall G : {group gT}, enum_rank G < n -> group_splitting_field Fs G}.
- apply: classic_bind => [[Fs f splitFs]] _ -> //.
  by exists Fs => // G; apply: splitFs.
elim: (n) => [|i IHi]; first by move=> _ -> //; exists F => //; exists id.
apply: classic_bind IHi => [[F' f splitF']].
have [le_n_i _ -> // | lt_i_n] := leqP n i.
  by exists F' => // G _; apply: splitF'; apply: leq_trans le_n_i.
have:= @group_splitting_field_exists _ (enum_val (Ordinal lt_i_n)) F'.
apply: classic_bind => [[Fs f' splitFs]] _ -> //.
exists Fs => [|G]; first exact: [rmorphism of (f' \o f)].
rewrite ltnS leq_eqVlt -{1}[i]/(val (Ordinal lt_i_n)) val_eqE.
case/predU1P=> [defG | ltGi]; first by rewrite -[G]enum_rankK defG.
by apply: (extend_group_splitting_field f'); apply: splitF'.
Qed.

Lemma group_closure_closed_field (F : closedFieldType) gT :
  group_closure_field F gT.
Proof.
move=> G [|n] rG irrG; first by case/mx_irrP: irrG.
apply: cent_mx_scalar_abs_irr => //; rewrite leqNgt.
apply/(has_non_scalar_mxP (scalar_mx_cent _ _)) => [[A cGA nscalA]].
have [a]: exists a, eigenvalue A a.
  pose P := mxminpoly A; pose d := degree_mxminpoly A.
  have Pd1: P`_d = 1.
    by rewrite -(eqP (mxminpoly_monic A)) /lead_coef size_mxminpoly.
  have d_gt0: d > 0 := mxminpoly_nonconstant A.
  have [a def_ad] := solve_monicpoly (nth 0 (- P)) d_gt0.
  exists a; rewrite eigenvalue_root_min -/P /root -oppr_eq0 -hornerN.
  rewrite horner_coef size_opp size_mxminpoly -/d big_ord_recr -def_ad.
  by rewrite coefN Pd1 mulN1r /= subrr.
case/negP; rewrite kermx_eq0 row_free_unit (mx_Schur irrG) ?subr_eq0 //.
  by rewrite -memmx_cent_envelop -raddfN linearD addmx_sub ?scalar_mx_cent.
by apply: contraNneq nscalA => ->; apply: scalar_mx_is_scalar.
Qed.

End BuildSplittingField.
