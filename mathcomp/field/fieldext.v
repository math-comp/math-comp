(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq div choice fintype.
From mathcomp
Require Import tuple finfun bigop ssralg finalg zmodp matrix vector falgebra.
From mathcomp
Require Import poly polydiv mxpoly generic_quotient.

(******************************************************************************)
(*  * Finite dimensional field extentions                                     *)
(*      fieldExtType F == the interface type for finite field extensions of F *)
(*                        it simply combines the fieldType and FalgType F     *)
(*                        interfaces.                                         *)
(* [fieldExtType F of L] == a fieldExt F structure for a type L that has both *)
(*                        FalgType F and fieldType canonical instances. The   *)
(*                        field class instance must be manifest with explicit *)
(*                        comRing, idomain, and field mixins. If L has an     *)
(*                        abstract field class should use the 'for' variant.  *)
(* [fieldExtType F of L for K] == a fieldExtType F structure for a type L     *)
(*                        that has an FalgType F canonical structure, given   *)
(*                        a K : fieldType whose unitRingType projection       *)
(*                        coincides with the canonical unitRingType for F.    *)
(*        {subfield L} == the type of subfields of L that are also extensions *)
(*                        of F; since we are in a finite dimensional setting  *)
(*                        these are exactly the F-subalgebras of L, and       *)
(*                        indeed {subfield L} is just display notation for    *)
(*                        {aspace L} when L is an extFieldType.               *)
(*  --> All aspace operations apply to {subfield L}, but there are several    *)
(*      additional lemmas and canonical instances specific to {subfield L}    *)
(*      spaces, e.g., subvs_of E is an extFieldType F when E : {subfield L}.  *)
(*  --> Also note that not all constructive subfields have type {subfield E}  *)
(*      in the same way that not all constructive subspaces have type         *)
(*      {vspace E}. These types only include the so called "detachable"       *)
(*      subspaces (and subalgebras).                                          *)
(*                                                                            *)
(* (E :&: F)%AS, (E * F)%AS == the intersection and product (meet and join)   *)
(*                           of E and F as subfields.                         *)
(*    subFExtend iota z p == Given a field morphism iota : F -> L, this is a  *)
(*                           type for the field F^iota(z) obtained by         *)
(*                           adjoining z to the image of F in L under iota.   *)
(*                           The construction requires a non-zero polynomial  *)
(*                           p in F such that z is a root of p^iota; it       *)
(*                           returns the field F^iota if this is not so.      *)
(*                           However, p need not be irredicible.              *)
(*            subfx_inj x == The injection of F^iota(z) into L.               *)
(*   inj_subfx iota z p x == The injection of F into F^iota(z).               *)
(*  subfx_eval iota z p q == Given q : {poly F} returns q.[z] as a value of   *)
(*                           type F^iota(z).                                  *)
(*    subfx_root iota z p == The generator of F^iota(z) over F.               *)
(* SubFieldExtType pz0 irr_p == A fieldExtType F structure for F^iota(z)      *)
(*                           (more precisely, subFExtend iota z p), given     *)
(*                           proofs pz0: root (map_poly iota p) z and         *)
(*                           irr_p : irreducible_poly p. The corresponding    *)
(*                           vectType substructure (SubfxVectType pz0 irr_p)  *)
(*                           has dimension (size p).-1 over F.                *)
(*            minPoly K x == the monic minimal polynomial of x over the       *)
(*                           subfield K.                                      *)
(*      adjoin_degree K x == the degree of the minimial polynomial or the     *)
(*                           dimension of K(x)/K.                             *)
(*     Fadjoin_poly K x y == a polynomial p over K such that y = p.[x].       *)
(*                                                                            *)
(*            fieldOver F == L, but with an extFieldType (subvs_of F)         *)
(*                           structure, for F : {subfield L}                  *)
(*         vspaceOver F V == the smallest subspace of fieldOver F containing  *)
(*                           V; this coincides with V if V is an F-module.    *)
(*        baseFieldType L == L, but with an extFieldType F0 structure, when L *)
(*                           has a canonical extFieldType F structure and F   *)
(*                           in turn has an extFieldType F0 structure.        *)
(*           baseVspace V == the subspace of baseFieldType L that coincides   *)
(*                           with V : {vspace L}.                             *)
(* --> Some caution must be exercised when using fieldOver and baseFieldType, *)
(*     because these are convertible to L while carrying different Lmodule    *)
(*     structures. This means that the safeguards engineered in the ssralg    *)
(*     library that normally curb the Coq kernel's inclination to diverge are *)
(*     no longer effectcive, so additional precautions should be taken when   *)
(*     matching or rewriting terms of the form a *: u, because Coq may take   *)
(*     forever to realize it's dealing with a *: in the wrong structure. The  *)
(*     baseField_scaleE and fieldOver_scaleE lemmas should be used to expand  *)
(*     or fold such "trans-structure" operations explicitly beforehand.       *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory.

Module FieldExt.

Import GRing.

Section FieldExt.

Variable R : ringType.

Record class_of T := Class {
  base : Falgebra.class_of R T;
  comm_ext : commutative (Ring.mul base);
  idomain_ext : IntegralDomain.axiom (Ring.Pack base);
  field_ext : Field.mixin_of (UnitRing.Pack base)
}.

Local Coercion base : class_of >-> Falgebra.class_of.

Section Bases.
Variables (T : Type) (c : class_of T).
Definition base1 := ComRing.Class (@comm_ext T c).
Definition base2 := @ComUnitRing.Class T base1 c.
Definition base3 := @IntegralDomain.Class T base2 (@idomain_ext T c).
Definition base4 := @Field.Class T base3 (@field_ext T c).
End Bases.
Local Coercion base1 : class_of >-> ComRing.class_of.
Local Coercion base2 : class_of >-> ComUnitRing.class_of.
Local Coercion base3 : class_of >-> IntegralDomain.class_of.
Local Coercion base4 : class_of >-> Field.class_of.

Structure type (phR : phant R) := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.

Variables (phR : phant R) (T : Type) (cT : type phR).
Definition class := let: Pack _ c :=  cT return class_of cT in c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack :=
  fun (bT : Falgebra.type phR) b
    & phant_id (Falgebra.class bT : Falgebra.class_of R bT)
               (b : Falgebra.class_of R T) =>
  fun mT Cm IDm Fm & phant_id (Field.class mT) (@Field.Class T
        (@IntegralDomain.Class T (@ComUnitRing.Class T (@ComRing.Class T b
          Cm) b) IDm) Fm) => Pack phR (@Class T b Cm IDm Fm).

Definition pack_eta K :=
  let cK := Field.class K in let Cm := ComRing.mixin cK in
  let IDm := IntegralDomain.mixin cK in let Fm := Field.mixin cK in
  fun (bT : Falgebra.type phR) b & phant_id (Falgebra.class bT) b =>
  fun cT_ & phant_id (@Class T b) cT_ => @Pack phR T (cT_ Cm IDm Fm).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition zmodType := @Zmodule.Pack cT xclass.
Definition ringType := @Ring.Pack cT xclass.
Definition unitRingType := @UnitRing.Pack cT xclass.
Definition comRingType := @ComRing.Pack cT xclass.
Definition comUnitRingType := @ComUnitRing.Pack cT xclass.
Definition idomainType := @IntegralDomain.Pack cT xclass.
Definition fieldType := @Field.Pack cT xclass.
Definition lmodType := @Lmodule.Pack R phR cT xclass.
Definition lalgType := @Lalgebra.Pack R phR cT xclass.
Definition algType := @Algebra.Pack R phR cT xclass.
Definition unitAlgType := @UnitAlgebra.Pack R phR cT xclass.
Definition vectType := @Vector.Pack R phR cT xclass.
Definition FalgType := @Falgebra.Pack R phR cT xclass.

Definition Falg_comRingType := @ComRing.Pack FalgType xclass.
Definition Falg_comUnitRingType := @ComUnitRing.Pack FalgType xclass.
Definition Falg_idomainType := @IntegralDomain.Pack FalgType xclass.
Definition Falg_fieldType := @Field.Pack FalgType xclass.

Definition vect_comRingType := @ComRing.Pack vectType xclass.
Definition vect_comUnitRingType := @ComUnitRing.Pack vectType xclass.
Definition vect_idomainType := @IntegralDomain.Pack vectType xclass.
Definition vect_fieldType := @Field.Pack vectType xclass.

Definition unitAlg_comRingType := @ComRing.Pack unitAlgType xclass.
Definition unitAlg_comUnitRingType := @ComUnitRing.Pack unitAlgType xclass.
Definition unitAlg_idomainType := @IntegralDomain.Pack unitAlgType xclass.
Definition unitAlg_fieldType := @Field.Pack unitAlgType xclass.

Definition alg_comRingType := @ComRing.Pack algType xclass.
Definition alg_comUnitRingType := @ComUnitRing.Pack algType xclass.
Definition alg_idomainType := @IntegralDomain.Pack algType xclass.
Definition alg_fieldType := @Field.Pack algType xclass.

Definition lalg_comRingType := @ComRing.Pack lalgType xclass.
Definition lalg_comUnitRingType := @ComUnitRing.Pack lalgType xclass.
Definition lalg_idomainType := @IntegralDomain.Pack lalgType xclass.
Definition lalg_fieldType := @Field.Pack lalgType xclass.

Definition lmod_comRingType := @ComRing.Pack lmodType xclass.
Definition lmod_comUnitRingType := @ComUnitRing.Pack lmodType xclass.
Definition lmod_idomainType := @IntegralDomain.Pack lmodType xclass.
Definition lmod_fieldType := @Field.Pack lmodType xclass.

End FieldExt.

Module Exports.

Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion base : class_of >-> Falgebra.class_of.
Coercion base4 : class_of >-> Field.class_of.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> Ring.type.
Canonical ringType.
Coercion unitRingType : type >-> UnitRing.type.
Canonical unitRingType.
Coercion comRingType : type >-> ComRing.type.
Canonical comRingType.
Coercion comUnitRingType : type >-> ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> IntegralDomain.type.
Canonical idomainType.
Coercion fieldType : type >-> Field.type.
Canonical fieldType.
Coercion lmodType : type >-> Lmodule.type.
Canonical lmodType.
Coercion lalgType : type >-> Lalgebra.type.
Canonical lalgType.
Coercion algType : type >-> Algebra.type.
Canonical algType.
Coercion unitAlgType : type >-> UnitAlgebra.type.
Canonical unitAlgType.
Coercion vectType : type >-> Vector.type.
Canonical vectType.
Coercion FalgType : type >-> Falgebra.type.
Canonical FalgType.

Canonical Falg_comRingType.
Canonical Falg_comUnitRingType.
Canonical Falg_idomainType.
Canonical Falg_fieldType.
Canonical vect_comRingType.
Canonical vect_comUnitRingType.
Canonical vect_idomainType.
Canonical vect_fieldType.
Canonical unitAlg_comRingType.
Canonical unitAlg_comUnitRingType.
Canonical unitAlg_idomainType.
Canonical unitAlg_fieldType.
Canonical alg_comRingType.
Canonical alg_comUnitRingType.
Canonical alg_idomainType.
Canonical alg_fieldType.
Canonical lalg_comRingType.
Canonical lalg_comUnitRingType.
Canonical lalg_idomainType.
Canonical lalg_fieldType.
Canonical lmod_comRingType.
Canonical lmod_comUnitRingType.
Canonical lmod_idomainType.
Canonical lmod_fieldType.
Notation fieldExtType R := (type (Phant R)).

Notation "[ 'fieldExtType' F 'of' L ]" :=
  (@pack _ (Phant F) L _ _ id _ _ _ _ id)
  (at level 0, format "[ 'fieldExtType'  F  'of'  L ]") : form_scope.

Notation "[ 'fieldExtType' F 'of' L 'for' K ]" :=
  (@pack_eta _ (Phant F) L K _ _ id _ id)
  (at level 0, format "[ 'fieldExtType'  F  'of'  L  'for'  K ]") : form_scope.

Notation "{ 'subfield' L }" := (@aspace_of _ (FalgType _) (Phant L))
  (at level 0, format "{ 'subfield'  L }") : type_scope.

End Exports.
End FieldExt.
Export FieldExt.Exports.

Canonical regular_fieldExtType (F : fieldType) := [fieldExtType F of F^o for F].

Section FieldExtTheory.

Variables (F0 : fieldType) (L : fieldExtType F0).
Implicit Types (U V M : {vspace L}) (E F K : {subfield L}).

Lemma dim_cosetv U x : x != 0 -> \dim (U * <[x]>) = \dim U.
Proof.
move=> nz_x; rewrite -limg_amulr limg_dim_eq //.
apply/eqP; rewrite -subv0; apply/subvP=> y.
by rewrite memv_cap memv0 memv_ker lfunE mulf_eq0 (negPf nz_x) orbF => /andP[].
Qed.

Lemma prodvC : commutative (@prodv F0 L).
Proof.
move=> U V; without loss suffices subC: U V / (U * V <= V * U)%VS.
  by apply/eqP; rewrite eqEsubv !{1}subC.
by apply/prodvP=> x y Ux Vy; rewrite mulrC memv_mul.
Qed.
Canonical prodv_comoid := Monoid.ComLaw prodvC.

Lemma prodvCA : left_commutative (@prodv F0 L).
Proof. exact: Monoid.mulmCA. Qed.

Lemma prodvAC : right_commutative (@prodv F0 L).
Proof. exact: Monoid.mulmAC. Qed.

Lemma algid1 K : algid K = 1. Proof. exact/skew_field_algid1/fieldP. Qed.

Lemma mem1v K : 1 \in K. Proof. by rewrite -algid_eq1 algid1. Qed.
Lemma sub1v K : (1 <= K)%VS. Proof. exact: mem1v. Qed.

Lemma subfield_closed K : agenv K = K.
Proof.
by apply/eqP; rewrite eqEsubv sub_agenv agenv_sub_modr ?sub1v ?asubv.
Qed.

Lemma AHom_lker0 (rT : FalgType F0) (f : 'AHom(L, rT)) : lker f == 0%VS.
Proof. by apply/lker0P; apply: fmorph_inj. Qed.

Lemma AEnd_lker0 (f : 'AEnd(L)) : lker f == 0%VS. Proof. exact: AHom_lker0. Qed.

Fact aimg_is_aspace (rT : FalgType F0) (f : 'AHom(L, rT)) (E : {subfield L}) :
  is_aspace (f @: E).
Proof.
rewrite /is_aspace -aimgM limgS ?prodv_id // has_algid1 //.
by apply/memv_imgP; exists 1; rewrite ?mem1v ?rmorph1.
Qed.
Canonical aimg_aspace rT f E := ASpace (@aimg_is_aspace rT f E).

Lemma Fadjoin_idP {K x} : reflect (<<K; x>>%VS = K) (x \in K).
Proof.
apply: (iffP idP) => [/addv_idPl-> | <-]; first exact: subfield_closed.
exact: memv_adjoin.
Qed.

Lemma Fadjoin0 K : <<K; 0>>%VS = K.
Proof. by rewrite addv0 subfield_closed. Qed.

Lemma Fadjoin_nil K : <<K & [::]>>%VS = K.
Proof. by rewrite adjoin_nil subfield_closed. Qed.

Lemma FadjoinP {K x E} :
  reflect (K <= E /\ x \in E)%VS (<<K; x>>%AS <= E)%VS.
Proof.
apply: (iffP idP) => [sKxE | /andP].
  by rewrite (subvP sKxE) ?memv_adjoin // (subv_trans _ sKxE) ?subv_adjoin.
by rewrite -subv_add => /agenvS; rewrite subfield_closed.
Qed.

Lemma Fadjoin_seqP {K} {rs : seq L} {E} :
  reflect (K <= E /\ {subset rs <= E})%VS (<<K & rs>> <= E)%VS.
Proof.
apply: (iffP idP) => [sKrsE | [sKE /span_subvP/(conj sKE)/andP]].
  split=> [|x rs_x]; first exact: subv_trans (subv_adjoin_seq _ _) sKrsE.
  by rewrite (subvP sKrsE) ?seqv_sub_adjoin.
by rewrite -subv_add => /agenvS; rewrite subfield_closed.
Qed.

Lemma alg_polyOver E p : map_poly (in_alg L) p \is a polyOver E.
Proof. by apply/(polyOverS (subvP (sub1v _)))/polyOver1P; exists p. Qed.

Lemma sub_adjoin1v x E : (<<1; x>> <= E)%VS = (x \in E)%VS.
Proof. by rewrite (sameP FadjoinP andP) sub1v. Qed.

Fact vsval_multiplicative K : multiplicative (vsval : subvs_of K -> L).
Proof. by split => //=; apply: algid1. Qed.
Canonical vsval_rmorphism K := AddRMorphism (vsval_multiplicative K).
Canonical vsval_lrmorphism K : {lrmorphism subvs_of K -> L} :=
  [lrmorphism of vsval].

Lemma vsval_invf K (w : subvs_of K) : val w^-1 = (vsval w)^-1.
Proof.
have [-> | Uv] := eqVneq w 0; first by rewrite !invr0.
by apply: vsval_invr; rewrite unitfE.
Qed.

Fact aspace_divr_closed K : divr_closed K.
Proof. by split=> [|u v Ku Kv]; rewrite ?mem1v ?memvM ?memvV. Qed.
Canonical aspace_mulrPred K := MulrPred (aspace_divr_closed K).
Canonical aspace_divrPred K := DivrPred (aspace_divr_closed K).
Canonical aspace_smulrPred K := SmulrPred (aspace_divr_closed K).
Canonical aspace_sdivrPred K := SdivrPred (aspace_divr_closed K).
Canonical aspace_semiringPred K := SemiringPred (aspace_divr_closed K).
Canonical aspace_subringPred K := SubringPred (aspace_divr_closed K).
Canonical aspace_subalgPred K := SubalgPred (memv_submod_closed K).
Canonical aspace_divringPred K := DivringPred (aspace_divr_closed K).
Canonical aspace_divalgPred K := DivalgPred (memv_submod_closed K).

Definition subvs_mulC K := [comRingMixin of subvs_of K by <:].
Canonical subvs_comRingType K :=
  Eval hnf in ComRingType (subvs_of K) (@subvs_mulC K).
Canonical subvs_comUnitRingType K :=
  Eval hnf in [comUnitRingType of subvs_of K].
Definition subvs_mul_eq0 K := [idomainMixin of subvs_of K by <:].
Canonical subvs_idomainType K :=
  Eval hnf in IdomainType (subvs_of K) (@subvs_mul_eq0 K).
Lemma subvs_fieldMixin K : GRing.Field.mixin_of (@subvs_idomainType K).
Proof.
by move=> w nz_w; rewrite unitrE -val_eqE /= vsval_invf algid1 divff.
Qed.
Canonical subvs_fieldType K :=
  Eval hnf in FieldType (subvs_of K) (@subvs_fieldMixin K).
Canonical subvs_fieldExtType K := Eval hnf in [fieldExtType F0 of subvs_of K].

Lemma polyOver_subvs {K} {p : {poly L}} :
  reflect (exists q : {poly subvs_of K}, p = map_poly vsval q)
          (p \is a polyOver K).
Proof.
apply: (iffP polyOverP) => [Hp | [q ->] i]; last by rewrite coef_map // subvsP.
exists (\poly_(i < size p) (Subvs (Hp i))); rewrite -{1}[p]coefK.
by apply/polyP=> i; rewrite coef_map !coef_poly; case: ifP.
Qed.

Lemma divp_polyOver K : {in polyOver K &, forall p q, p %/ q \is a polyOver K}.
Proof.
move=> _ _ /polyOver_subvs[p ->] /polyOver_subvs[q ->].
by apply/polyOver_subvs; exists (p %/ q); rewrite map_divp.
Qed.

Lemma modp_polyOver K : {in polyOver K &, forall p q, p %% q \is a polyOver K}.
Proof.
move=> _ _ /polyOver_subvs[p ->] /polyOver_subvs[q ->].
by apply/polyOver_subvs; exists (p %% q); rewrite map_modp.
Qed.

Lemma gcdp_polyOver K :
  {in polyOver K &, forall p q, gcdp p q \is a polyOver K}.
Proof.
move=> _ _ /polyOver_subvs[p ->] /polyOver_subvs[q ->].
by apply/polyOver_subvs; exists (gcdp p q); rewrite gcdp_map.
Qed.

Fact prodv_is_aspace E F : is_aspace (E * F).
Proof.
rewrite /is_aspace prodvCA -!prodvA prodvA !prodv_id has_algid1 //=.
by rewrite -[1]mulr1 memv_mul ?mem1v.
Qed.
Canonical prodv_aspace E F : {subfield L} := ASpace (prodv_is_aspace E F).

Fact field_mem_algid E F : algid E \in F. Proof. by rewrite algid1 mem1v. Qed.
Canonical capv_aspace E F : {subfield L} := aspace_cap (field_mem_algid E F).

Lemma polyOverSv U V : (U <= V)%VS -> {subset polyOver U <= polyOver V}.
Proof. by move/subvP=> sUV; apply: polyOverS. Qed.

Lemma field_subvMl F U : (U <= F * U)%VS.
Proof. by rewrite -{1}[U]prod1v prodvSl ?sub1v. Qed.

Lemma field_subvMr U F : (U <= U * F)%VS.
Proof. by rewrite prodvC field_subvMl. Qed.

Lemma field_module_eq F M : (F * M <= M)%VS -> (F * M)%VS = M.
Proof. by move=> modM; apply/eqP; rewrite eqEsubv modM field_subvMl. Qed.

Lemma sup_field_module F E : (F * E <= E)%VS = (F <= E)%VS.
Proof.
apply/idP/idP; first exact: subv_trans (field_subvMr F E).
by move/(prodvSl E)/subv_trans->; rewrite ?asubv.
Qed.

Lemma field_module_dimS F M : (F * M <= M)%VS -> (\dim F %| \dim M)%N.
Proof. exact/skew_field_module_dimS/fieldP. Qed.

Lemma field_dimS F E : (F <= E)%VS -> (\dim F %| \dim E)%N.
Proof. exact/skew_field_dimS/fieldP. Qed.

Lemma dim_field_module F M : (F * M <= M)%VS -> \dim M = (\dim_F M * \dim F)%N.
Proof. by move/field_module_dimS/divnK. Qed.

Lemma dim_sup_field F E : (F <= E)%VS -> \dim E = (\dim_F E * \dim F)%N.
Proof. by move/field_dimS/divnK. Qed.

Lemma field_module_semisimple F M (m := \dim_F M) :
    (F * M <= M)%VS ->
  {X : m.-tuple L | {subset X <= M} /\ 0 \notin X
     & let FX := (\sum_(i < m) F * <[X`_i]>)%VS in FX = M /\ directv FX}.
Proof.
move=> modM; have dimM: (m * \dim F)%N = \dim M by rewrite -dim_field_module.
have [X [defM dxFX nzX]] := skew_field_module_semisimple (@fieldP L) modM.
have szX: size X == m.
  rewrite -(eqn_pmul2r (adim_gt0 F)) dimM -defM (directvP dxFX) /=.
  rewrite -sum1_size big_distrl; apply/eqP/eq_big_seq => x Xx /=.
  by rewrite mul1n dim_cosetv ?(memPn nzX).
rewrite directvE /= !(big_nth 0) (eqP szX) !big_mkord -directvE /= in defM dxFX.
exists (Tuple szX) => //; split=> // _ /tnthP[i ->]; rewrite (tnth_nth 0) /=.
by rewrite -defM memvE (sumv_sup i) ?field_subvMl.
Qed.

Section FadjoinPolyDefinitions.

Variables (U : {vspace L}) (x : L).

Definition adjoin_degree := (\dim_U <<U; x>>).-1.+1.
Local Notation n := adjoin_degree.

Definition Fadjoin_sum := (\sum_(i < n) U * <[x ^+ i]>)%VS.

Definition Fadjoin_poly v : {poly L} :=
  \poly_(i < n) (sumv_pi Fadjoin_sum (inord i) v / x ^+ i).

Definition minPoly : {poly L} := 'X^n - Fadjoin_poly (x ^+ n).

Lemma size_Fadjoin_poly v : size (Fadjoin_poly v) <= n.
Proof. exact: size_poly. Qed.

Lemma Fadjoin_polyOver v : Fadjoin_poly v \is a polyOver U.
Proof.
apply/(all_nthP 0) => i _; rewrite coef_poly /=.
case: ifP => lti; last exact: mem0v.
have /memv_cosetP[y Uy ->] := memv_sum_pi (erefl Fadjoin_sum) (inord i) v.
rewrite inordK //; have [-> | /mulfK-> //] := eqVneq (x ^+ i) 0.
by rewrite mulr0 mul0r mem0v.
Qed.

Fact Fadjoin_poly_is_linear : linear_for (in_alg L \; *:%R) Fadjoin_poly.
Proof.
move=> a u v; apply/polyP=> i; rewrite coefD coefZ !coef_poly.
case: ifP => lti; last by rewrite mulr0 addr0.
by rewrite linearP mulrA -mulrDl mulr_algl.
Qed.
Canonical Fadjoin_poly_additive := Additive Fadjoin_poly_is_linear.
Canonical Fadjoin_poly_linear := AddLinear Fadjoin_poly_is_linear.

Lemma size_minPoly : size minPoly = n.+1.
Proof. by rewrite size_addl ?size_polyXn // size_opp ltnS size_poly. Qed.

Lemma monic_minPoly : minPoly \is monic.
Proof.
rewrite monicE /lead_coef size_minPoly coefB coefXn eqxx.
by rewrite nth_default ?subr0 ?size_poly.
Qed.

End FadjoinPolyDefinitions.

Section FadjoinPoly.

Variables (K : {subfield L}) (x : L).
Local Notation n := (adjoin_degree (asval K) x).
Local Notation sumKx := (Fadjoin_sum (asval K) x).

Lemma adjoin_degreeE : n = \dim_K <<K; x>>.
Proof. by rewrite [n]prednK // divn_gt0 ?adim_gt0 // dimvS ?subv_adjoin. Qed.

Lemma dim_Fadjoin : \dim <<K; x>> = (n * \dim K)%N.
Proof. by rewrite adjoin_degreeE -dim_sup_field ?subv_adjoin. Qed.

Lemma adjoin0_deg : adjoin_degree K 0 = 1%N.
Proof. by rewrite /adjoin_degree addv0 subfield_closed divnn adim_gt0. Qed.

Lemma adjoin_deg_eq1 : (n == 1%N) = (x \in K).
Proof.
rewrite (sameP Fadjoin_idP eqP) adjoin_degreeE; have sK_Kx := subv_adjoin K x.
apply/eqP/idP=> [dimKx1 | /eqP->]; last by rewrite divnn adim_gt0.
by rewrite eq_sym eqEdim sK_Kx /= (dim_sup_field sK_Kx) dimKx1 mul1n.
Qed.

Lemma Fadjoin_sum_direct : directv sumKx.
Proof.
rewrite directvE /=; case Dn: {-2}n (leqnn n) => // [m] {Dn}.
elim: m => [|m IHm] ltm1n; rewrite ?big_ord1 // !(big_ord_recr m.+1) /=.
do [move/(_ (ltnW ltm1n))/eqP; set S := (\sum_i _)%VS] in IHm *.
rewrite -IHm dimv_add_leqif; apply/subvP=> z; rewrite memv_cap => /andP[Sz].
case/memv_cosetP=> y Ky Dz; rewrite memv0 Dz mulf_eq0 expf_eq0 /=.
apply: contraLR ltm1n => /norP[nz_y nz_x].
rewrite -leqNgt -(leq_pmul2r (adim_gt0 K)) -dim_Fadjoin.
have{IHm} ->: (m.+1 * \dim K)%N = \dim S.
  rewrite -[m.+1]card_ord -sum_nat_const IHm.
  by apply: eq_bigr => i; rewrite dim_cosetv ?expf_neq0.
apply/dimvS/agenv_sub_modl; first by rewrite (sumv_sup 0) //= prodv1 sub1v.
rewrite prodvDl subv_add -[S]big_distrr prodvA prodv_id subvv !big_distrr /=.
apply/subv_sumP=> i _; rewrite -expv_line prodvCA -expvSl expv_line.
have [ltim | lemi] := ltnP i m; first by rewrite (sumv_sup (Sub i.+1 _)).
have{lemi} /eqP->: i == m :> nat by rewrite eqn_leq leq_ord.
rewrite -big_distrr -2!{2}(prodv_id K) /= -!prodvA big_distrr -/S prodvSr //=.
by rewrite -(canLR (mulKf nz_y) Dz) -memvE memv_mul ?rpredV.
Qed.

Let nz_x_i (i : 'I_n) : x ^+ i != 0.
Proof.
by rewrite expf_eq0; case: eqP i => [->|_] [[]] //; rewrite adjoin0_deg.
Qed.

Lemma Fadjoin_eq_sum : <<K; x>>%VS = sumKx.
Proof.
apply/esym/eqP; rewrite eqEdim eq_leq ?andbT.
  apply/subv_sumP=> i _; rewrite -agenvM prodvS ?subv_adjoin //.
  by rewrite -expv_line (subv_trans (subX_agenv _ _)) ?agenvS ?addvSr.
rewrite dim_Fadjoin -[n]card_ord -sum_nat_const (directvP Fadjoin_sum_direct).
by apply: eq_bigr => i _; rewrite /= dim_cosetv.
Qed.

Lemma Fadjoin_poly_eq v : v \in <<K; x>>%VS -> (Fadjoin_poly K x v).[x] = v.
Proof.
move/(sumv_pi_sum Fadjoin_eq_sum)=> {2}<-; rewrite horner_poly.
by apply: eq_bigr => i _; rewrite inord_val mulfVK.
Qed.

Lemma mempx_Fadjoin p : p \is a polyOver K -> p.[x] \in <<K; x>>%VS.
Proof.
move=> Kp; rewrite rpred_horner ?memv_adjoin ?(polyOverS _ Kp) //.
exact: subvP_adjoin.
Qed.

Lemma Fadjoin_polyP {v} :
  reflect (exists2 p, p \in polyOver K & v = p.[x]) (v \in <<K; x>>%VS).
Proof.
apply: (iffP idP) => [Kx_v | [p Kp ->]]; last exact: mempx_Fadjoin.
by exists (Fadjoin_poly K x v); rewrite ?Fadjoin_polyOver ?Fadjoin_poly_eq.
Qed.

Lemma Fadjoin_poly_unique p v :
  p \is a polyOver K -> size p <= n -> p.[x] = v -> Fadjoin_poly K x v = p.
Proof.
have polyKx q i: q \is a polyOver K -> q`_i * x ^+ i \in (K * <[x ^+ i]>)%VS.
  by move/polyOverP=> Kq; rewrite memv_mul ?Kq ?memv_line.
move=> Kp szp Dv; have /Fadjoin_poly_eq/eqP := mempx_Fadjoin Kp.
rewrite {1}Dv {Dv} !(@horner_coef_wide _ n) ?size_poly //.
move/polyKx in Kp; have /polyKx K_pv := Fadjoin_polyOver K x v.
rewrite (directv_sum_unique Fadjoin_sum_direct) // => /eqfunP eq_pq.
apply/polyP=> i; have [leni|?] := leqP n i; last exact: mulIf (eq_pq (Sub i _)).
by rewrite !nth_default ?(leq_trans _ leni) ?size_poly.
Qed.

Lemma Fadjoin_polyC v : v \in K -> Fadjoin_poly K x v = v%:P.
Proof.
move=> Kv; apply: Fadjoin_poly_unique; rewrite ?polyOverC ?hornerC //.
by rewrite size_polyC (leq_trans (leq_b1 _)).
Qed.

Lemma Fadjoin_polyX : x \notin K -> Fadjoin_poly K x x = 'X.
Proof.
move=> K'x; apply: Fadjoin_poly_unique; rewrite ?polyOverX ?hornerX //.
by rewrite size_polyX ltn_neqAle andbT eq_sym adjoin_deg_eq1.
Qed.

Lemma minPolyOver : minPoly K x \is a polyOver K.
Proof. by rewrite /minPoly rpredB ?rpredX ?polyOverX ?Fadjoin_polyOver. Qed.

Lemma minPolyxx : (minPoly K x).[x] = 0.
Proof.
by rewrite !hornerE hornerXn Fadjoin_poly_eq ?subrr ?rpredX ?memv_adjoin.
Qed.

Lemma root_minPoly : root (minPoly K x) x. Proof. exact/rootP/minPolyxx. Qed.

Lemma Fadjoin_poly_mod p :
  p \is a polyOver K -> Fadjoin_poly K x p.[x] = p %% minPoly K x.
Proof.
move=> Kp; rewrite {1}(divp_eq p (minPoly K x)) 2!hornerE minPolyxx mulr0 add0r.
apply: Fadjoin_poly_unique => //; first by rewrite modp_polyOver // minPolyOver.
by rewrite -ltnS -size_minPoly ltn_modp // monic_neq0 ?monic_minPoly.
Qed.

Lemma minPoly_XsubC : reflect (minPoly K x = 'X - x%:P) (x \in K).
Proof.
set p := minPoly K x; apply: (iffP idP) => [Kx | Dp]; last first.
  suffices ->: x = - p`_0 by rewrite rpredN (polyOverP minPolyOver).
  by rewrite Dp coefB coefX coefC add0r opprK.
rewrite (@all_roots_prod_XsubC _ p [:: x]) /= ?root_minPoly //.
  by rewrite big_seq1 (monicP (monic_minPoly K x)) scale1r.
by apply/eqP; rewrite size_minPoly eqSS adjoin_deg_eq1.
Qed.

Lemma root_small_adjoin_poly p :
  p \is a polyOver K -> size p <= n -> root p x = (p == 0).
Proof.
move=> Kp szp; apply/rootP/eqP=> [px0 | ->]; last by rewrite horner0.
rewrite -(Fadjoin_poly_unique Kp szp px0).
by apply: Fadjoin_poly_unique; rewrite ?polyOver0 ?size_poly0 ?horner0.
Qed.

Lemma minPoly_irr p :
  p \is a polyOver K -> p %| minPoly K x -> (p %= minPoly K x) || (p %= 1).
Proof.
rewrite dvdp_eq; set q := _ %/ _ => Kp def_pq.
have Kq: q \is a polyOver K by rewrite divp_polyOver // minPolyOver.
move: q Kq def_pq root_minPoly (size_minPoly K x) => q Kq /eqP->.
rewrite rootM => pqx0 szpq.
have [nzq nzp]: q != 0 /\ p != 0.
  by apply/norP; rewrite -mulf_eq0 -size_poly_eq0 szpq.
without loss{pqx0} qx0: q p Kp Kq nzp nzq szpq / root q x.
  move=> IH; case/orP: pqx0 => /IH{IH}IH; first exact: IH.
  have{IH} /orP[]: (q %= p * q) || (q %= 1) by apply: IH => //; rewrite mulrC.
    by rewrite orbC -{1}[q]mul1r eqp_mul2r // eqp_sym => ->.
  by rewrite -{1}[p]mul1r eqp_sym eqp_mul2r // => ->.
apply/orP; right; rewrite -size_poly_eq1 eqn_leq lt0n size_poly_eq0 nzp andbT.
rewrite -(leq_add2r (size q)) -leq_subLR subn1 -size_mul // mulrC szpq.
by rewrite ltnNge; apply: contra nzq => /(root_small_adjoin_poly Kq) <-.
Qed.

Lemma minPoly_dvdp p : p \is a polyOver K -> root p x -> (minPoly K x) %| p.
Proof.
move=> Kp rootp.
have gcdK : gcdp (minPoly K x) p \is a polyOver K.
  by rewrite gcdp_polyOver ?minPolyOver.
have /orP[gcd_eqK|gcd_eq1] := minPoly_irr gcdK (dvdp_gcdl (minPoly K x) p).
  by rewrite -(eqp_dvdl _ gcd_eqK) dvdp_gcdr.
case/negP: (root1 x).
by rewrite -(eqp_root gcd_eq1) root_gcd rootp root_minPoly.
Qed.

End FadjoinPoly.

Lemma minPolyS K E a : (K <= E)%VS -> minPoly E a %| minPoly K a.
Proof.
move=> sKE; apply: minPoly_dvdp; last exact: root_minPoly.
by apply: (polyOverSv sKE); rewrite minPolyOver.
Qed.

Arguments Fadjoin_polyP {K x v}.
Lemma Fadjoin1_polyP x v :
  reflect (exists p, v = (map_poly (in_alg L) p).[x]) (v \in <<1; x>>%VS).
Proof.
apply: (iffP Fadjoin_polyP) => [[_ /polyOver1P]|] [p ->]; first by exists p.
by exists (map_poly (in_alg L) p) => //; apply: alg_polyOver.
Qed.

Section Horner.

Variables z : L.

Definition fieldExt_horner := horner_morph (fun x => mulrC z (in_alg L x)).
Canonical fieldExtHorner_additive := [additive of fieldExt_horner].
Canonical fieldExtHorner_rmorphism := [rmorphism of fieldExt_horner].
Lemma fieldExt_hornerC b : fieldExt_horner b%:P = b%:A.
Proof. exact: horner_morphC. Qed.
Lemma fieldExt_hornerX : fieldExt_horner 'X = z.
Proof. exact: horner_morphX. Qed.
Fact fieldExt_hornerZ : scalable fieldExt_horner.
Proof.
move=> a p; rewrite -mul_polyC rmorphM /= fieldExt_hornerC.
by rewrite -scalerAl mul1r.
Qed.
Canonical fieldExt_horner_linear := AddLinear fieldExt_hornerZ.
Canonical fieldExt_horner_lrmorhism := [lrmorphism of fieldExt_horner].

End Horner.

End FieldExtTheory.

Notation "E :&: F" := (capv_aspace E F) : aspace_scope.
Notation "'C_ E [ x ]" := (capv_aspace E 'C[x]) : aspace_scope.
Notation "'C_ ( E ) [ x ]" := (capv_aspace E 'C[x])
  (only parsing) : aspace_scope.
Notation "'C_ E ( V )" := (capv_aspace E 'C(V)) : aspace_scope.
Notation "'C_ ( E ) ( V )" := (capv_aspace E 'C(V))
  (only parsing) : aspace_scope.
Notation "E * F" := (prodv_aspace E F) : aspace_scope.
Notation "f @: E" := (aimg_aspace f E) : aspace_scope.

Arguments Fadjoin_idP {F0 L K x}.
Arguments FadjoinP {F0 L K x E}.
Arguments Fadjoin_seqP {F0 L K rs E}.
Arguments polyOver_subvs {F0 L K p}.
Arguments Fadjoin_polyP {F0 L K x v}.
Arguments Fadjoin1_polyP {F0 L x v}.
Arguments minPoly_XsubC {F0 L K x}.

Section MapMinPoly.

Variables (F0 : fieldType) (L rL : fieldExtType F0) (f : 'AHom(L, rL)).
Variables (K : {subfield L}) (x : L).

Lemma adjoin_degree_aimg : adjoin_degree (f @: K) (f x) = adjoin_degree K x.
Proof.
rewrite !adjoin_degreeE -aimg_adjoin.
by rewrite !limg_dim_eq ?(eqP (AHom_lker0 f)) ?capv0.
Qed.

Lemma map_minPoly :  map_poly f (minPoly K x) = minPoly (f @: K) (f x).
Proof.
set fp := minPoly (f @: K) (f x); pose fM := [rmorphism of f].
have [p Kp Dp]: exists2 p, p \is a polyOver K & map_poly f p = fp.
  have Kfp: fp \is a polyOver (f @: K)%VS by apply: minPolyOver.
  exists (map_poly f^-1%VF fp).
    apply/polyOver_poly=> j _; have /memv_imgP[y Ky ->] := polyOverP Kfp j.
    by rewrite lker0_lfunK ?AHom_lker0.
  rewrite -map_poly_comp map_poly_id // => _ /(allP Kfp)/memv_imgP[y _ ->].
  by rewrite /= limg_lfunVK ?memv_img ?memvf.
apply/eqP; rewrite -eqp_monic ?monic_map ?monic_minPoly // -Dp eqp_map.
have: ~~ (p %= 1) by rewrite -size_poly_eq1 -(size_map_poly fM) Dp size_minPoly.
apply: implyP; rewrite implyNb orbC eqp_sym minPoly_irr //.
rewrite -(dvdp_map fM) Dp minPoly_dvdp ?fmorph_root ?root_minPoly //.
by apply/polyOver_poly=> j _; apply/memv_img/polyOverP/minPolyOver.
Qed.

End MapMinPoly.

(* Changing up the reference field of a fieldExtType. *)
Section FieldOver.

Variables (F0 : fieldType) (L : fieldExtType F0) (F : {subfield L}).

Definition fieldOver of {vspace L} : Type := L.
Local Notation K_F := (subvs_of F).
Local Notation L_F := (fieldOver F).

Canonical fieldOver_eqType := [eqType of L_F].
Canonical fieldOver_choiceType := [choiceType of L_F].
Canonical fieldOver_zmodType := [zmodType of L_F].
Canonical fieldOver_ringType := [ringType of L_F].
Canonical fieldOver_unitRingType := [unitRingType of L_F].
Canonical fieldOver_comRingType := [comRingType of L_F].
Canonical fieldOver_comUnitRingType := [comUnitRingType of L_F].
Canonical fieldOver_idomainType := [idomainType of L_F].
Canonical fieldOver_fieldType := [fieldType of L_F].

Definition fieldOver_scale (a : K_F) (u : L_F) : L_F := vsval a * u.
Local Infix "*F:" := fieldOver_scale (at level 40).

Fact fieldOver_scaleA a b u : a *F: (b *F: u) = (a * b) *F: u.
Proof. exact: mulrA. Qed.

Fact fieldOver_scale1 u : 1 *F: u = u.
Proof. by rewrite /(1 *F: u) /= algid1 mul1r. Qed.

Fact fieldOver_scaleDr a u v : a *F: (u + v) = a *F: u + a *F: v.
Proof. exact: mulrDr. Qed.

Fact fieldOver_scaleDl v a b : (a + b) *F: v = a *F: v + b *F: v.
Proof. exact: mulrDl. Qed.

Definition fieldOver_lmodMixin :=
  LmodMixin fieldOver_scaleA fieldOver_scale1
            fieldOver_scaleDr fieldOver_scaleDl.

Canonical fieldOver_lmodType := LmodType K_F L_F fieldOver_lmodMixin.

Lemma fieldOver_scaleE a (u : L) : a *: (u : L_F) = vsval a * u.
Proof. by []. Qed.

Fact fieldOver_scaleAl a u v : a *F: (u * v) = (a *F: u) * v.
Proof. exact: mulrA. Qed.

Canonical fieldOver_lalgType := LalgType K_F L_F fieldOver_scaleAl.

Fact fieldOver_scaleAr a u v : a *F: (u * v) = u * (a *F: v).
Proof. exact: mulrCA. Qed.

Canonical fieldOver_algType := AlgType K_F L_F fieldOver_scaleAr.
Canonical fieldOver_unitAlgType := [unitAlgType K_F of L_F].

Fact fieldOver_vectMixin : Vector.mixin_of fieldOver_lmodType.
Proof.
have [bL [_ nz_bL] [defL dxSbL]] := field_module_semisimple (subvf (F * _)).
do [set n := \dim_F {:L} in bL nz_bL *; set SbL := (\sum_i _)%VS] in defL dxSbL.
have in_bL i (a : K_F) : val a * (bL`_i : L_F) \in (F * <[bL`_i]>)%VS.
  by rewrite memv_mul ?(valP a) ?memv_line.
have nz_bLi (i : 'I_n): bL`_i != 0 by rewrite (memPn nz_bL) ?memt_nth.
pose r2v (v : 'rV[K_F]_n) : L_F := \sum_i v 0 i *: (bL`_i : L_F).
have r2v_lin: linear r2v.
  move=> a u v; rewrite /r2v scaler_sumr -big_split /=; apply: eq_bigr => i _.
  by rewrite scalerA -scalerDl !mxE.
have v2rP x: {r : 'rV[K_F]_n | x = r2v r}.
  apply: sig_eqW; have /memv_sumP[y Fy ->]: x \in SbL by rewrite defL memvf.
  have /fin_all_exists[r Dr] i: exists r, y i = r *: (bL`_i : L_F).
    by have /memv_cosetP[a Fa ->] := Fy i isT; exists (Subvs Fa).
  by exists (\row_i r i); apply: eq_bigr => i _; rewrite mxE.
pose v2r x := sval (v2rP x).
have v2rK: cancel v2r (Linear r2v_lin) by rewrite /v2r => x; case: (v2rP x).
suffices r2vK: cancel r2v v2r.
  by exists n, v2r; [apply: can2_linear v2rK | exists r2v].
move=> r; apply/rowP=> i; apply/val_inj/(mulIf (nz_bLi i))/eqP; move: i isT.
by apply/forall_inP; move/directv_sum_unique: dxSbL => <- //; apply/eqP/v2rK.
Qed.

Canonical fieldOver_vectType := VectType K_F L_F fieldOver_vectMixin.
Canonical fieldOver_FalgType := [FalgType K_F of L_F].
Canonical fieldOver_fieldExtType := [fieldExtType K_F of L_F].

Implicit Types (V : {vspace L}) (E : {subfield L}).

Lemma trivial_fieldOver : (1%VS : {vspace L_F}) =i F.
Proof.
move=> x; apply/vlineP/idP=> [[{x}x ->] | Fx].
  by rewrite fieldOver_scaleE mulr1 (valP x).
by exists (vsproj F x); rewrite fieldOver_scaleE mulr1 vsprojK.
Qed.

Definition vspaceOver V := <<vbasis V : seq L_F>>%VS.

Lemma mem_vspaceOver V : vspaceOver V =i (F * V)%VS.
Proof.
move=> y; apply/idP/idP; last rewrite unlock; move/coord_span->.
  rewrite (@memv_suml F0 L) // => i _.
  by rewrite memv_mul ?subvsP // vbasis_mem ?memt_nth.
rewrite memv_suml // => ij _; rewrite -tnth_nth; set x := tnth _ ij.
have/allpairsP[[u z] /= [Fu Vz {x}->]]: x \in _ := mem_tnth ij _.
by rewrite scalerAl (memvZ (Subvs _)) ?memvZ ?memv_span //= vbasis_mem.
Qed.

Lemma mem_aspaceOver E : (F <= E)%VS -> vspaceOver E =i E.
Proof.
by move=> sFE y; rewrite mem_vspaceOver field_module_eq ?sup_field_module.
Qed.

Fact aspaceOver_suproof E : is_aspace (vspaceOver E).
Proof.
rewrite /is_aspace has_algid1; last by rewrite mem_vspaceOver (@mem1v _ L).
by apply/prodvP=> u v; rewrite !mem_vspaceOver; apply: memvM.
Qed.
Canonical aspaceOver E := ASpace (aspaceOver_suproof E).

Lemma dim_vspaceOver M : (F * M <= M)%VS -> \dim (vspaceOver M) = \dim_F M.
Proof.
move=> modM; have [] := field_module_semisimple modM.
set n := \dim_F M => b [Mb nz_b] [defM dx_b].
suff: basis_of (vspaceOver M) b by apply: size_basis.
apply/andP; split.
  rewrite eqEsubv; apply/andP; split; apply/span_subvP=> u.
    by rewrite mem_vspaceOver field_module_eq // => /Mb.
  move/(@vbasis_mem _ _ _ M); rewrite -defM => /memv_sumP[{u}u Fu ->].
  apply: memv_suml => i _; have /memv_cosetP[a Fa ->] := Fu i isT.
  by apply: (memvZ (Subvs Fa)); rewrite memv_span ?memt_nth.
apply/freeP=> a /(directv_sum_independent dx_b) a_0 i.
have{a_0}: a i *: (b`_i : L_F) == 0.
  by rewrite a_0 {i}// => i _; rewrite memv_mul ?memv_line ?subvsP.
by rewrite scaler_eq0=> /predU1P[] // /idPn[]; rewrite (memPn nz_b) ?memt_nth.
Qed.

Lemma dim_aspaceOver E : (F <= E)%VS -> \dim (vspaceOver E) = \dim_F E.
Proof. by rewrite -sup_field_module; apply: dim_vspaceOver. Qed.

Lemma vspaceOverP V_F :
  {V | [/\ V_F = vspaceOver V, (F * V <= V)%VS & V_F =i V]}.
Proof.
pose V := (F * <<vbasis V_F : seq L>>)%VS.
have idV: (F * V)%VS = V by rewrite prodvA prodv_id.
suffices defVF: V_F = vspaceOver V.
  by exists V; split=> [||u]; rewrite ?defVF ?mem_vspaceOver ?idV.
apply/vspaceP=> v; rewrite mem_vspaceOver idV.
do [apply/idP/idP; last rewrite /V unlock] => [/coord_vbasis|/coord_span] ->.
  by apply: memv_suml => i _; rewrite memv_mul ?subvsP ?memv_span ?memt_nth.
apply: memv_suml => i _; rewrite -tnth_nth; set xu := tnth _ i.
have /allpairsP[[x u] /=]: xu \in _ := mem_tnth i _.
case=> /vbasis_mem Fx /vbasis_mem Vu ->.
rewrite scalerAl (coord_span Vu) mulr_sumr memv_suml // => j_.
by rewrite -scalerCA (memvZ (Subvs _)) ?memvZ // vbasis_mem ?memt_nth.
Qed.

Lemma aspaceOverP (E_F : {subfield L_F}) :
  {E | [/\ E_F = aspaceOver E, (F <= E)%VS & E_F =i E]}.
Proof.
have [V [defEF modV memV]] := vspaceOverP E_F.
have algE: has_algid V && (V * V <= V)%VS.
  rewrite has_algid1; last by rewrite -memV mem1v.
  by apply/prodvP=> u v; rewrite -!memV; apply: memvM.
by exists (ASpace algE); rewrite -sup_field_module; split; first apply: val_inj.
Qed.

End FieldOver.

(* Changing the reference field to a smaller field. *)
Section BaseField.

Variables (F0 : fieldType) (F : fieldExtType F0) (L : fieldExtType F).

Definition baseField_type of phant L : Type := L.
Notation L0 := (baseField_type (Phant (FieldExt.sort L))).

Canonical baseField_eqType := [eqType of L0].
Canonical baseField_choiceType := [choiceType of L0].
Canonical baseField_zmodType := [zmodType of L0].
Canonical baseField_ringType := [ringType of L0].
Canonical baseField_unitRingType := [unitRingType of L0].
Canonical baseField_comRingType := [comRingType of L0].
Canonical baseField_comUnitRingType := [comUnitRingType of L0].
Canonical baseField_idomainType := [idomainType of L0].
Canonical baseField_fieldType := [fieldType of L0].

Definition baseField_scale (a : F0) (u : L0) : L0 := in_alg F a *: u.
Local Infix "*F0:" := baseField_scale (at level 40).

Fact baseField_scaleA a b u : a *F0: (b *F0: u) = (a * b) *F0: u.
Proof. by rewrite [_ *F0: _]scalerA -rmorphM. Qed.

Fact baseField_scale1 u : 1 *F0: u = u.
Proof. by rewrite /(1 *F0: u) rmorph1 scale1r. Qed.

Fact baseField_scaleDr a u v : a *F0: (u + v) = a *F0: u + a *F0: v.
Proof. exact: scalerDr. Qed.

Fact baseField_scaleDl v a b : (a + b) *F0: v = a *F0: v + b *F0: v.
Proof. by rewrite -scalerDl -rmorphD. Qed.

Definition baseField_lmodMixin :=
  LmodMixin baseField_scaleA baseField_scale1
            baseField_scaleDr baseField_scaleDl.

Canonical baseField_lmodType := LmodType F0 L0 baseField_lmodMixin.

Lemma baseField_scaleE a (u : L) : a *: (u : L0) = a%:A *: u.
Proof. by []. Qed.

Fact baseField_scaleAl a (u v : L0) : a *F0: (u * v) = (a *F0: u) * v.
Proof. exact: scalerAl. Qed.

Canonical baseField_lalgType := LalgType F0 L0 baseField_scaleAl.

Fact baseField_scaleAr a u v : a *F0: (u * v) = u * (a *F0: v).
Proof. exact: scalerAr. Qed.

Canonical baseField_algType := AlgType F0 L0 baseField_scaleAr.
Canonical baseField_unitAlgType := [unitAlgType F0 of L0].

Let n := \dim {:F}.
Let bF : n.-tuple F := vbasis {:F}.
Let coordF (x : F) := (coord_vbasis (memvf x)).

Fact baseField_vectMixin : Vector.mixin_of baseField_lmodType.
Proof.
pose bL := vbasis {:L}; set m := \dim {:L} in bL.
pose v2r (x : L0) := mxvec (\matrix_(i, j) coord bF j (coord bL i x)).
have v2r_lin: linear v2r.
  move=> a x y; rewrite -linearP; congr (mxvec _); apply/matrixP=> i j.
  by rewrite !mxE linearP mulr_algl linearP.
pose r2v r := \sum_(i < m) (\sum_(j < n) vec_mx r i j *: bF`_j) *: bL`_i.
have v2rK: cancel v2r r2v.
  move=> x; transitivity (\sum_(i < m) coord bL i x *: bL`_i); last first.
    by rewrite -coord_vbasis ?memvf.
    (* GG: rewrite {2}(coord_vbasis (memvf x)) -/m would take 8s; *)
    (* The -/m takes 8s, and without it then apply: eq_bigr takes 12s. *)
    (* The time drops to 2s with  a -[GRing.Field.ringType F]/(F : fieldType) *)
  apply: eq_bigr => i _; rewrite mxvecK; congr (_ *: _ : L).
  by rewrite (coordF (coord bL i x)); apply: eq_bigr => j _; rewrite mxE.
exists (m * n)%N, v2r => //; exists r2v => // r.
apply: (canLR vec_mxK); apply/matrixP=> i j; rewrite mxE.
by rewrite !coord_sum_free ?(basis_free (vbasisP _)).
Qed.

Canonical baseField_vectType := VectType F0 L0 baseField_vectMixin.
Canonical baseField_FalgType := [FalgType F0 of L0].
Canonical baseField_extFieldType := [fieldExtType F0 of L0].

Let F0ZEZ a x v : a *: ((x *: v : L) : L0)  = (a *: x) *: v.
Proof. by rewrite [a *: _]scalerA -scalerAl mul1r. Qed.

Let baseVspace_basis V : seq L0 :=
  [seq tnth bF ij.2 *: tnth (vbasis V) ij.1 | ij : 'I_(\dim V) * 'I_n].
Definition baseVspace V := <<baseVspace_basis V>>%VS.

Lemma mem_baseVspace V : baseVspace V =i V.
Proof.
move=> y; apply/idP/idP=> [/coord_span->|/coord_vbasis->]; last first.
  apply: memv_suml => i _; rewrite (coordF (coord _ i (y : L))) scaler_suml -/n.
  apply: memv_suml => j _; rewrite -/bF -F0ZEZ memvZ ?memv_span // -!tnth_nth.
  by apply/imageP; exists (i, j).
  (* GG: the F0ZEZ lemma avoids serious performance issues here. *)
apply: memv_suml => k _; rewrite nth_image; case: (enum_val k) => i j /=.
by rewrite F0ZEZ memvZ ?vbasis_mem ?mem_tnth.
Qed.

Lemma dim_baseVspace V : \dim (baseVspace V) = (\dim V * n)%N.
Proof.
pose bV0 := baseVspace_basis V; set m := \dim V in bV0 *.
suffices /size_basis->: basis_of (baseVspace V) bV0.
  by rewrite card_prod !card_ord.
rewrite /basis_of eqxx.
apply/freeP=> s sb0 k; rewrite -(enum_valK k); case/enum_val: k => i j.
have free_baseP := freeP (basis_free (vbasisP _)).
move: j; apply: (free_baseP _ _ fullv); move: i; apply: (free_baseP _ _ V).
transitivity (\sum_i \sum_j s (enum_rank (i, j)) *: bV0`_(enum_rank (i, j))).
  apply: eq_bigr => i _; rewrite scaler_suml; apply: eq_bigr => j _.
  by rewrite -F0ZEZ nth_image enum_rankK -!tnth_nth.
rewrite pair_bigA (reindex _ (onW_bij _ (enum_val_bij _))); apply: etrans sb0.
by apply: eq_bigr => k _; rewrite -{5 6}[k](enum_valK k); case/enum_val: k.
Qed.

Fact baseAspace_suproof (E : {subfield L}) : is_aspace (baseVspace E).
Proof.
rewrite /is_aspace has_algid1; last by rewrite mem_baseVspace (mem1v E).
by apply/prodvP=> u v; rewrite !mem_baseVspace; apply: memvM.
Qed.
Canonical baseAspace E := ASpace (baseAspace_suproof E).

Fact refBaseField_key : unit. Proof. by []. Qed.
Definition refBaseField := locked_with refBaseField_key (baseAspace 1).
Canonical refBaseField_unlockable := [unlockable of refBaseField].
Notation F1 := refBaseField.

Lemma dim_refBaseField : \dim F1 = n.
Proof. by rewrite [F1]unlock dim_baseVspace dimv1 mul1n. Qed.

Lemma baseVspace_module V (V0 := baseVspace V) : (F1 * V0 <= V0)%VS.
Proof.
apply/prodvP=> u v; rewrite [F1]unlock !mem_baseVspace => /vlineP[x ->] Vv.
by rewrite -(@scalerAl F L) mul1r; apply: memvZ.
Qed.

Lemma sub_baseField (E : {subfield L}) : (F1 <= baseVspace E)%VS.
Proof. by rewrite -sup_field_module baseVspace_module. Qed.

Lemma vspaceOver_refBase V : vspaceOver F1 (baseVspace V) =i V.
Proof.
move=> v; rewrite mem_vspaceOver field_module_eq ?baseVspace_module //.
by rewrite mem_baseVspace.
Qed.

Lemma module_baseVspace M0 :
  (F1 * M0 <= M0)%VS -> {V | M0 = baseVspace V & M0 =i V}.
Proof.
move=> modM0; pose V := <<vbasis (vspaceOver F1 M0) : seq L>>%VS.
suffices memM0: M0 =i V.
  by exists V => //; apply/vspaceP=> v; rewrite mem_baseVspace memM0.
move=> v; rewrite -{1}(field_module_eq modM0) -(mem_vspaceOver M0) {}/V.
move: (vspaceOver F1 M0) => M.
apply/idP/idP=> [/coord_vbasis|/coord_span]->; apply/memv_suml=> i _.
  rewrite /(_ *: _) /= /fieldOver_scale; case: (coord _ i _) => /= x.
  rewrite {1}[F1]unlock mem_baseVspace => /vlineP[{x}x ->].
  by rewrite -(@scalerAl F L) mul1r memvZ ?memv_span ?memt_nth.
move: (coord _ i _) => x; rewrite -[_`_i]mul1r scalerAl -tnth_nth.
have F1x: x%:A \in F1.
  by rewrite [F1]unlock mem_baseVspace (@memvZ F L) // mem1v.
by congr (_ \in M): (memvZ (Subvs F1x) (vbasis_mem (mem_tnth i _))).
Qed.

Lemma module_baseAspace (E0 : {subfield L0}) :
  (F1 <= E0)%VS -> {E | E0 = baseAspace E & E0 =i E}.
Proof.
rewrite -sup_field_module => /module_baseVspace[E defE0 memE0].
suffices algE: is_aspace E by exists (ASpace algE); first apply: val_inj.
rewrite /is_aspace has_algid1 -?memE0 ?mem1v //.
by apply/prodvP=> u v; rewrite -!memE0; apply: memvM.
Qed.

End BaseField.

Notation baseFieldType L := (baseField_type (Phant L)).

(* Base of fieldOver, finally. *)
Section MoreFieldOver.

Variables (F0 : fieldType) (L : fieldExtType F0) (F : {subfield L}).

Lemma base_vspaceOver V : baseVspace (vspaceOver F V) =i (F * V)%VS.
Proof. by move=> v; rewrite mem_baseVspace mem_vspaceOver. Qed.

Lemma base_moduleOver V : (F * V <= V)%VS -> baseVspace (vspaceOver F V) =i V.
Proof. by move=> /field_module_eq defV v; rewrite base_vspaceOver defV. Qed.

Lemma base_aspaceOver (E : {subfield L}) :
  (F <= E)%VS -> baseVspace (vspaceOver F E) =i E.
Proof. by rewrite -sup_field_module; apply: base_moduleOver. Qed.

End MoreFieldOver.

Section SubFieldExtension.

Local Open Scope quotient_scope.

Variables (F L : fieldType) (iota : {rmorphism F -> L}).
Variables (z : L) (p : {poly F}).

Local Notation "p ^iota" := (map_poly (GRing.RMorphism.apply iota) p)
  (at level 2, format "p ^iota") : ring_scope.

Let wf_p := (p != 0) && root p^iota z.
Let p0 : {poly F} := if wf_p then (lead_coef p)^-1 *: p else 'X.
Let z0 := if wf_p then z else 0.
Let n := (size p0).-1.

Let p0_mon : p0 \is monic.
Proof.
rewrite /p0; case: ifP => [/andP[nz_p _] | _]; last exact: monicX.
by rewrite monicE lead_coefZ mulVf ?lead_coef_eq0.
Qed.

Let nz_p0 : p0 != 0. Proof. by rewrite monic_neq0 // p0_mon. Qed.

Let p0z0 : root p0^iota z0.
Proof.
rewrite /p0 /z0; case: ifP => [/andP[_ pz0]|]; last by rewrite map_polyX rootX.
by rewrite map_polyZ rootE hornerZ (rootP pz0) mulr0.
Qed.

Let n_gt0: 0 < n.
Proof.
rewrite /n -subn1 subn_gt0 -(size_map_poly iota).
by rewrite (root_size_gt1 _ p0z0) ?map_poly_eq0.
Qed.

Let z0Ciota : commr_rmorph iota z0. Proof. by move=> x; apply: mulrC. Qed.
Local Notation iotaPz := (horner_morph z0Ciota).
Let iotaFz (x : 'rV[F]_n) := iotaPz (rVpoly x).

Definition equiv_subfext x y := (iotaFz x == iotaFz y).

Fact equiv_subfext_is_equiv : equiv_class_of equiv_subfext.
Proof. by rewrite /equiv_subfext; split=> x // y w /eqP->. Qed.

Canonical equiv_subfext_equiv := EquivRelPack equiv_subfext_is_equiv.
Canonical equiv_subfext_encModRel := defaultEncModRel equiv_subfext.

Definition subFExtend := {eq_quot equiv_subfext}.
Canonical subFExtend_eqType := [eqType of subFExtend].
Canonical subFExtend_choiceType := [choiceType of subFExtend].
Canonical subFExtend_quotType := [quotType of subFExtend].
Canonical subFExtend_eqQuotType := [eqQuotType equiv_subfext of subFExtend].

Definition subfx_inj := lift_fun1 subFExtend iotaFz.

Fact pi_subfx_inj : {mono \pi : x / iotaFz x >-> subfx_inj x}.
Proof.
unlock subfx_inj => x; apply/eqP; rewrite -/(equiv_subfext _ x).
by rewrite -eqmodE reprK.
Qed.
Canonical pi_subfx_inj_morph := PiMono1 pi_subfx_inj.

Let iotaPz_repr x : iotaPz (rVpoly (repr (\pi_(subFExtend) x))) = iotaFz x.
Proof. by rewrite -/(iotaFz _) -!pi_subfx_inj reprK. Qed.

Definition subfext0 := lift_cst subFExtend 0.
Canonical subfext0_morph := PiConst subfext0.

Definition subfext_add := lift_op2 subFExtend +%R.
Fact pi_subfext_add : {morph \pi : x y / x + y >-> subfext_add x y}.
Proof.
unlock subfext_add => x y /=; apply/eqmodP/eqP.
by rewrite /iotaFz !linearD /= !iotaPz_repr.
Qed.
Canonical pi_subfx_add_morph := PiMorph2 pi_subfext_add.

Definition subfext_opp := lift_op1 subFExtend -%R.
Fact pi_subfext_opp : {morph \pi : x / - x >-> subfext_opp x}.
Proof.
unlock subfext_opp => y /=; apply/eqmodP/eqP.
by rewrite /iotaFz !linearN /= !iotaPz_repr.
Qed.
Canonical pi_subfext_opp_morph := PiMorph1 pi_subfext_opp.

Fact addfxA : associative subfext_add.
Proof. by move=> x y t; rewrite -[x]reprK -[y]reprK -[t]reprK !piE addrA. Qed.

Fact addfxC : commutative subfext_add.
Proof. by move=> x y; rewrite -[x]reprK -[y]reprK !piE addrC. Qed.

Fact add0fx : left_id subfext0 subfext_add.
Proof. by move=> x; rewrite -[x]reprK !piE add0r. Qed.

Fact addfxN : left_inverse subfext0 subfext_opp subfext_add.
Proof. by move=> x; rewrite -[x]reprK !piE addNr. Qed.

Definition subfext_zmodMixin :=  ZmodMixin addfxA addfxC add0fx addfxN.
Canonical subfext_zmodType :=
  Eval hnf in ZmodType subFExtend subfext_zmodMixin.

Let poly_rV_modp_K q : rVpoly (poly_rV (q %% p0) : 'rV[F]_n) = q %% p0.
Proof. by apply: poly_rV_K; rewrite -ltnS -polySpred // ltn_modp. Qed.

Let iotaPz_modp q : iotaPz (q %% p0) = iotaPz q.
Proof.
rewrite {2}(divp_eq q p0) rmorphD rmorphM /=.
by rewrite [iotaPz p0](rootP p0z0) mulr0 add0r.
Qed.

Definition subfx_mul_rep (x y : 'rV[F]_n) : 'rV[F]_n :=
  poly_rV ((rVpoly x) * (rVpoly y) %% p0).

Definition subfext_mul := lift_op2 subFExtend subfx_mul_rep.
Fact pi_subfext_mul :
  {morph \pi : x y / subfx_mul_rep x y >-> subfext_mul x y}.
Proof.
unlock subfext_mul => x y /=; apply/eqmodP/eqP.
by rewrite /iotaFz !poly_rV_modp_K !iotaPz_modp !rmorphM /= !iotaPz_repr.
Qed.
Canonical pi_subfext_mul_morph := PiMorph2 pi_subfext_mul.

Definition subfext1 := lift_cst subFExtend (poly_rV 1).
Canonical subfext1_morph := PiConst subfext1.

Fact mulfxA : associative (subfext_mul).
Proof.
elim/quotW=> x; elim/quotW=> y; elim/quotW=> w; rewrite !piE /subfx_mul_rep.
by rewrite !poly_rV_modp_K [_ %% p0 * _]mulrC !modp_mul // mulrA mulrC.
Qed.

Fact mulfxC : commutative subfext_mul.
Proof.
by elim/quotW=> x; elim/quotW=> y; rewrite !piE /subfx_mul_rep /= mulrC.
Qed.

Fact mul1fx : left_id subfext1 subfext_mul.
Proof.
elim/quotW=> x; rewrite !piE /subfx_mul_rep poly_rV_K ?size_poly1 // mul1r.
by rewrite modp_small ?rVpolyK // (polySpred nz_p0) ltnS size_poly.
Qed.

Fact mulfx_addl : left_distributive subfext_mul subfext_add.
Proof.
elim/quotW=> x; elim/quotW=> y; elim/quotW=> w; rewrite !piE /subfx_mul_rep.
by rewrite linearD /= mulrDl modp_add linearD.
Qed.

Fact nonzero1fx : subfext1 != subfext0.
Proof.
rewrite !piE /equiv_subfext /iotaFz !linear0.
by rewrite poly_rV_K ?rmorph1 ?oner_eq0 // size_poly1.
Qed.

Definition subfext_comRingMixin :=
  ComRingMixin mulfxA mulfxC mul1fx mulfx_addl nonzero1fx.
Canonical subfext_Ring := Eval hnf in RingType subFExtend subfext_comRingMixin.
Canonical subfext_comRing := Eval hnf in ComRingType subFExtend mulfxC.

Definition subfx_poly_inv (q : {poly F}) : {poly F} :=
  if iotaPz q == 0 then 0 else
  let r := gdcop q p0 in let: (u, v) := egcdp q r in
  ((u * q + v * r)`_0)^-1 *: u.

Let subfx_poly_invE q : iotaPz (subfx_poly_inv q) = (iotaPz q)^-1.
Proof.
rewrite /subfx_poly_inv.
have [-> | nzq] := altP eqP; first by rewrite rmorph0 invr0.
rewrite [nth]lock -[_^-1]mul1r; apply: canRL (mulfK nzq) _; rewrite -rmorphM /=.
have rz0: iotaPz (gdcop q p0) = 0.
  by apply/rootP; rewrite gdcop_map root_gdco ?map_poly_eq0 // p0z0 nzq.
do [case: gdcopP => r _; rewrite (negPf nz_p0) orbF => co_r_q _] in rz0 *.
case: (egcdp q r) (egcdpE q r) => u v /=/eqp_size/esym/eqP.
rewrite coprimep_size_gcd 1?coprimep_sym // => /size_poly1P[a nz_a Da].
rewrite Da -scalerAl (canRL (addrK _) Da) -lock coefC linearZ linearB /=.
by rewrite rmorphM /= rz0 mulr0 subr0 horner_morphC -rmorphM mulVf ?rmorph1.
Qed.

Definition subfx_inv_rep (x : 'rV[F]_n) : 'rV[F]_n :=
  poly_rV (subfx_poly_inv (rVpoly x) %% p0).

Definition subfext_inv := lift_op1 subFExtend subfx_inv_rep.
Fact pi_subfext_inv : {morph \pi : x / subfx_inv_rep x >-> subfext_inv x}.
Proof.
unlock subfext_inv => x /=; apply/eqmodP/eqP; rewrite /iotaFz.
by rewrite 2!{1}poly_rV_modp_K 2!{1}iotaPz_modp !subfx_poly_invE iotaPz_repr.
Qed.
Canonical pi_subfext_inv_morph := PiMorph1 pi_subfext_inv.

Fact subfx_fieldAxiom :
  GRing.Field.axiom (subfext_inv : subFExtend -> subFExtend).
Proof.
elim/quotW=> x; apply: contraNeq; rewrite !piE /equiv_subfext /iotaFz !linear0.
apply: contraR => nz_x; rewrite poly_rV_K ?size_poly1 // !poly_rV_modp_K.
by rewrite iotaPz_modp rmorph1 rmorphM /= iotaPz_modp subfx_poly_invE mulVf.
Qed.

Fact subfx_inv0 : subfext_inv (0 : subFExtend) = (0 : subFExtend).
Proof.
apply/eqP; rewrite !piE /equiv_subfext /iotaFz /subfx_inv_rep !linear0.
by rewrite /subfx_poly_inv rmorph0 eqxx mod0p !linear0.
Qed.

Definition subfext_unitRingMixin := FieldUnitMixin subfx_fieldAxiom subfx_inv0.
Canonical subfext_unitRingType :=
  Eval hnf in UnitRingType subFExtend subfext_unitRingMixin.
Canonical subfext_comUnitRing := Eval hnf in [comUnitRingType of subFExtend].
Definition subfext_fieldMixin := @FieldMixin _ _ subfx_fieldAxiom subfx_inv0.
Definition subfext_idomainMixin := FieldIdomainMixin subfext_fieldMixin.
Canonical subfext_idomainType :=
  Eval hnf in IdomainType subFExtend subfext_idomainMixin.
Canonical subfext_fieldType :=
  Eval hnf in FieldType subFExtend subfext_fieldMixin.

Fact subfx_inj_is_rmorphism : rmorphism subfx_inj.
Proof.
do 2?split; last by rewrite piE /iotaFz poly_rV_K ?rmorph1 ?size_poly1.
  by elim/quotW=> x; elim/quotW=> y; rewrite !piE /iotaFz linearB rmorphB.
elim/quotW=> x; elim/quotW=> y; rewrite !piE /subfx_mul_rep /iotaFz.
by rewrite poly_rV_modp_K iotaPz_modp rmorphM.
Qed.
Canonical subfx_inj_additive := Additive subfx_inj_is_rmorphism.
Canonical subfx_inj_rmorphism := RMorphism subfx_inj_is_rmorphism.

Definition subfx_eval := lift_embed subFExtend (fun q => poly_rV (q %% p0)).
Canonical subfx_eval_morph := PiEmbed subfx_eval.

Definition subfx_root := subfx_eval 'X.

Lemma subfx_eval_is_rmorphism : rmorphism subfx_eval.
Proof.
do 2?split=> [x y|] /=; apply/eqP; rewrite piE.
- by rewrite -linearB modp_add modNp.
- by rewrite /subfx_mul_rep !poly_rV_modp_K !(modp_mul, mulrC _ y).
by rewrite modp_small // size_poly1 -subn_gt0 subn1.
Qed.
Canonical subfx_eval_additive := Additive subfx_eval_is_rmorphism.
Canonical subfx_eval_rmorphism := AddRMorphism subfx_eval_is_rmorphism.

Definition inj_subfx := (subfx_eval \o polyC).
Canonical inj_subfx_addidive := [additive of inj_subfx].
Canonical inj_subfx_rmorphism := [rmorphism of inj_subfx].

Lemma subfxE x: exists p, x = subfx_eval p.
Proof.
elim/quotW: x => x; exists (rVpoly x); apply/eqP; rewrite piE /equiv_subfext.
by rewrite /iotaFz poly_rV_modp_K iotaPz_modp.
Qed.

Definition subfx_scale a x := inj_subfx a * x.
Fact subfx_scalerA a b x :
  subfx_scale a (subfx_scale b x) = subfx_scale (a * b) x.
Proof. by rewrite /subfx_scale rmorphM mulrA. Qed.
Fact subfx_scaler1r : left_id 1 subfx_scale.
Proof. by move=> x; rewrite /subfx_scale rmorph1 mul1r. Qed.
Fact subfx_scalerDr : right_distributive subfx_scale +%R.
Proof. by move=> a; apply: mulrDr. Qed.
Fact subfx_scalerDl x : {morph subfx_scale^~ x : a b / a + b}.
Proof. by move=> a b; rewrite /subfx_scale rmorphD mulrDl. Qed.
Definition subfx_lmodMixin :=
  LmodMixin subfx_scalerA subfx_scaler1r subfx_scalerDr subfx_scalerDl.
Canonical subfx_lmodType := LmodType F subFExtend subfx_lmodMixin.

Fact subfx_scaleAl : GRing.Lalgebra.axiom ( *%R : subFExtend -> _).
Proof. by move=> a; apply: mulrA. Qed.
Canonical subfx_lalgType := LalgType F subFExtend subfx_scaleAl.

Fact subfx_scaleAr : GRing.Algebra.axiom subfx_lalgType.
Proof. by move=> a; apply: mulrCA. Qed.
Canonical subfx_algType := AlgType F subFExtend subfx_scaleAr.
Canonical subfext_unitAlgType := [unitAlgType F of subFExtend].

Fact subfx_evalZ : scalable subfx_eval.
Proof. by move=> a q; rewrite -mul_polyC rmorphM. Qed.
Canonical subfx_eval_linear := AddLinear subfx_evalZ.
Canonical subfx_eval_lrmorphism := [lrmorphism of subfx_eval].

Hypothesis (pz0 : root p^iota z).

Section NonZero.

Hypothesis nz_p : p != 0.

Lemma subfx_inj_eval q : subfx_inj (subfx_eval q) = q^iota.[z].
Proof.
by rewrite piE /iotaFz poly_rV_modp_K iotaPz_modp /iotaPz /z0 /wf_p nz_p pz0.
Qed.

Lemma subfx_inj_root : subfx_inj subfx_root = z.
Proof. by rewrite subfx_inj_eval // map_polyX hornerX. Qed.

Lemma subfx_injZ b x : subfx_inj (b *: x) = iota b * subfx_inj x.
Proof. by rewrite rmorphM /= subfx_inj_eval // map_polyC hornerC. Qed.

Lemma subfx_inj_base b : subfx_inj b%:A = iota b.
Proof. by rewrite subfx_injZ rmorph1 mulr1. Qed.

Lemma subfxEroot x : {q | x = (map_poly (in_alg subFExtend) q).[subfx_root]}.
Proof.
have /sig_eqW[q ->] := subfxE x; exists q.
apply: (fmorph_inj subfx_inj_rmorphism).
rewrite -horner_map /= subfx_inj_root subfx_inj_eval //.
by rewrite -map_poly_comp (eq_map_poly subfx_inj_base).
Qed.

Lemma subfx_irreducibleP :
 (forall q, root q^iota z -> q != 0 -> size p <= size q) <-> irreducible_poly p.
Proof.
split=> [min_p | irr_p q qz0 nz_q].
  split=> [|q nonC_q q_dv_p].
    by rewrite -(size_map_poly iota) (root_size_gt1 _ pz0) ?map_poly_eq0.
  have /dvdpP[r Dp] := q_dv_p; rewrite -dvdp_size_eqp // eqn_leq dvdp_leq //=.
  have [nz_r nz_q]: r != 0 /\ q != 0 by apply/norP; rewrite -mulf_eq0 -Dp.
  have: root r^iota z || root q^iota z by rewrite -rootM -rmorphM -Dp.
  case/orP=> /min_p; [case/(_ _)/idPn=> // | exact].
  rewrite polySpred // -leqNgt Dp size_mul //= polySpred // -subn2 ltn_subRL.
  by rewrite addSnnS addnC ltn_add2l ltn_neqAle eq_sym nonC_q size_poly_gt0.
pose r := gcdp p q; have nz_r: r != 0 by rewrite gcdp_eq0 (negPf nz_p).
suffices /eqp_size <-: r %= p by rewrite dvdp_leq ?dvdp_gcdr.
rewrite (irr_p _) ?dvdp_gcdl // -(size_map_poly iota) gtn_eqF //.
by rewrite (@root_size_gt1 _ z) ?map_poly_eq0 // gcdp_map root_gcd pz0.
Qed.

End NonZero.

Section Irreducible.

Hypothesis irr_p : irreducible_poly p.
Let nz_p : p != 0. Proof. exact: irredp_neq0. Qed.

(* The Vector axiom requires irreducibility. *)
Lemma min_subfx_vectAxiom : Vector.axiom (size p).-1 subfx_lmodType.
Proof.
move/subfx_irreducibleP: irr_p => /=/(_ nz_p) min_p; set d := (size p).-1.
have Dd: d.+1 = size p by rewrite polySpred.
pose Fz2v x : 'rV_d := poly_rV (sval (sig_eqW (subfxE x)) %% p).
pose vFz : 'rV_d -> subFExtend := subfx_eval \o rVpoly.
have FLinj: injective subfx_inj by apply: fmorph_inj.
have Fz2vK: cancel Fz2v vFz.
  move=> x; rewrite /vFz /Fz2v; case: (sig_eqW _) => /= q ->.
  apply: FLinj; rewrite !subfx_inj_eval // {2}(divp_eq q p) rmorphD rmorphM /=.
  by rewrite !hornerE (eqP pz0) mulr0 add0r poly_rV_K // -ltnS Dd ltn_modpN0.
suffices vFzK: cancel vFz Fz2v.
  by exists Fz2v; [apply: can2_linear Fz2vK | exists vFz].
apply: inj_can_sym Fz2vK _ => v1 v2 /(congr1 subfx_inj)/eqP.
rewrite -subr_eq0 -!raddfB /= subfx_inj_eval // => /min_p/implyP.
rewrite leqNgt implybNN -Dd ltnS size_poly linearB subr_eq0 /=.
by move/eqP/(can_inj rVpolyK).
Qed.

Definition SubfxVectMixin := VectMixin min_subfx_vectAxiom.
Definition SubfxVectType := VectType F subFExtend SubfxVectMixin.
Definition SubfxFalgType := Eval simpl in [FalgType F of SubfxVectType].
Definition SubFieldExtType := Eval simpl in [fieldExtType F of SubfxFalgType].

End Irreducible.

End SubFieldExtension.

Prenex Implicits subfx_inj.

Lemma irredp_FAdjoin (F : fieldType) (p : {poly F}) :
    irreducible_poly p ->
  {L : fieldExtType F & \dim {:L} = (size p).-1 &
    {z | root (map_poly (in_alg L) p) z & <<1; z>>%VS = fullv}}.
Proof.
case=> p_gt1 irr_p; set n := (size p).-1; pose vL := [vectType F of 'rV_n].
have Dn: n.+1 = size p := ltn_predK p_gt1.
have nz_p: p != 0 by rewrite -size_poly_eq0 -Dn.
suffices [L dimL [toPF [toL toPF_K toL_K]]]:
   {L : fieldExtType F & \dim {:L} = (size p).-1
      & {toPF : {linear L -> {poly F}} & {toL : {lrmorphism {poly F} -> L} |
         cancel toPF toL & forall q, toPF (toL q) = q %% p}}}.
- exists L => //; pose z := toL 'X; set iota := in_alg _.
  suffices q_z q: toPF (map_poly iota q).[z] = q %% p.
    exists z; first by rewrite /root -(can_eq toPF_K) q_z modpp linear0.
    apply/vspaceP=> x; rewrite memvf; apply/Fadjoin_polyP.
    exists (map_poly iota (toPF x)).
      by apply/polyOverP=> i; rewrite coef_map memvZ ?mem1v.
    by apply: (can_inj toPF_K); rewrite q_z -toL_K toPF_K.
  elim/poly_ind: q => [|a q IHq].
    by rewrite map_poly0 horner0 linear0 mod0p.
  rewrite rmorphD rmorphM /= map_polyX map_polyC hornerMXaddC linearD /=.
  rewrite linearZ /= -(rmorph1 toL) toL_K -modp_scalel alg_polyC modp_add.
  congr (_ + _); rewrite -toL_K rmorphM /= -/z; congr (toPF (_ * z)).
  by apply: (can_inj toPF_K); rewrite toL_K.
pose toL q : vL := poly_rV (q %% p); pose toPF (x : vL) := rVpoly x.
have toL_K q : toPF (toL q) = q %% p.
  by rewrite /toPF poly_rV_K // -ltnS Dn ?ltn_modp -?Dn.
have toPF_K: cancel toPF toL.
  by move=> x; rewrite /toL modp_small ?rVpolyK // -Dn ltnS size_poly.
have toPinj := can_inj toPF_K.
pose mul x y := toL (toPF x * toPF y); pose L1 := toL 1.
have L1K: toPF L1 = 1 by rewrite toL_K modp_small ?size_poly1.
have mulC: commutative mul by rewrite /mul => x y; rewrite mulrC.
have mulA: associative mul.
  by move=> x y z; apply: toPinj; rewrite -!(mulC z) !toL_K !modp_mul mulrCA.
have mul1: left_id L1 mul.
  by move=> x; apply: toPinj; rewrite mulC !toL_K modp_mul mulr1 -toL_K toPF_K.
have mulD: left_distributive mul +%R.
  move=> x y z; apply: toPinj; rewrite /toPF raddfD /= -!/(toPF _).
  by rewrite !toL_K /toPF raddfD mulrDl modp_add.
have nzL1: L1 != 0 by rewrite -(inj_eq toPinj) L1K /toPF raddf0 oner_eq0.
pose mulM := ComRingMixin mulA mulC mul1 mulD nzL1.
pose rL := ComRingType (RingType vL mulM) mulC.
have mulZl: GRing.Lalgebra.axiom mul.
  move=> a x y; apply: toPinj; rewrite toL_K /toPF !linearZ /= -!/(toPF _).
  by rewrite toL_K -scalerAl modp_scalel.
have mulZr: GRing.Algebra.axiom (LalgType F rL mulZl).
  by move=> a x y; rewrite !(mulrC x) scalerAl.
pose aL := AlgType F _ mulZr; pose urL := FalgUnitRingType aL.
pose uaL := [unitAlgType F of AlgType F urL mulZr].
pose faL := [FalgType F of uaL].
have unitE: GRing.Field.mixin_of urL.
  move=> x nz_x; apply/unitrP; set q := toPF x.
  have nz_q: q != 0 by rewrite -(inj_eq toPinj) /toPF raddf0 in nz_x.
  have /Bezout_eq1_coprimepP[u upq1]: coprimep p q.
    apply: contraLR (leq_gcdpr p nz_q) => /irr_p/implyP.
    rewrite dvdp_gcdl -ltnNge /= => /eqp_size->.
    by rewrite (polySpred nz_p) ltnS size_poly.
  suffices: x * toL u.2 = 1 by exists (toL u.2); rewrite mulrC.
  apply: toPinj; rewrite !toL_K -upq1 modp_mul modp_add mulrC.
  by rewrite modp_mull add0r.
pose ucrL := [comUnitRingType of ComRingType urL mulC].
have mul0 := GRing.Field.IdomainMixin unitE.
pose fL := FieldType (IdomainType ucrL mul0) unitE.
exists [fieldExtType F of faL for fL]; first by rewrite dimvf; apply: mul1n.
exists [linear of toPF as rVpoly].
suffices toLM: lrmorphism (toL : {poly F} -> aL) by exists (LRMorphism toLM).
have toLlin: linear toL.
  by move=> a q1 q2; rewrite -linearP -modp_scalel -modp_add.
do ?split; try exact: toLlin; move=> q r /=.
by apply: toPinj; rewrite !toL_K modp_mul -!(mulrC r) modp_mul.
Qed.

(*Coq 8.3 processes this shorter proof correctly, but then crashes on Qed.
  In Coq 8.4 Qed takes about 18s.
  In Coq 8.7, everything seems to be all right *)
(*
Lemma Xirredp_FAdjoin' (F : fieldType) (p : {poly F}) :
    irreducible_poly p ->
  {L : fieldExtType F & Vector.dim L = (size p).-1 &
    {z | root (map_poly (in_alg L) p) z & <<1; z>>%VS = fullv}}.
Proof.
case=> p_gt1 irr_p; set n := (size p).-1; pose vL := [vectType F of 'rV_n].
have Dn: n.+1 = size p := ltn_predK p_gt1.
have nz_p: p != 0 by rewrite -size_poly_eq0 -Dn.
pose toL q : vL := poly_rV (q %% p).
have toL_K q : rVpoly (toL q) = q %% p.
  by rewrite poly_rV_K // -ltnS Dn ?ltn_modp -?Dn.
pose mul (x y : vL) : vL := toL (rVpoly x * rVpoly y).
pose L1 : vL := poly_rV 1.
have L1K: rVpoly L1 = 1 by rewrite poly_rV_K // size_poly1 -ltnS Dn.
have mulC: commutative mul by rewrite /mul => x y; rewrite mulrC.
have mulA: associative mul.
  by move=> x y z; rewrite -!(mulC z) /mul !toL_K /toL !modp_mul mulrCA.
have mul1: left_id L1 mul.
  move=> x; rewrite /mul L1K mul1r /toL modp_small ?rVpolyK // -Dn ltnS.
  by rewrite size_poly.
have mulD: left_distributive mul +%R.
  move=> x y z; apply: canLR rVpolyK _.
  by rewrite !raddfD mulrDl /= !toL_K /toL modp_add.
have nzL1: L1 != 0 by rewrite -(can_eq rVpolyK) L1K raddf0 oner_eq0.
pose mulM := ComRingMixin mulA mulC mul1 mulD nzL1.
pose rL := ComRingType (RingType vL mulM) mulC.
have mulZl: GRing.Lalgebra.axiom mul.
  move=> a x y; apply: canRL rVpolyK _; rewrite !linearZ /= toL_K.
  by rewrite -scalerAl modp_scalel.
have mulZr: @GRing.Algebra.axiom _ (LalgType F rL mulZl).
  by move=> a x y; rewrite !(mulrC x) scalerAl.
pose aL := AlgType F _ mulZr; pose urL := FalgUnitRingType aL.
pose uaL := [unitAlgType F of AlgType F urL mulZr].
pose faL := [FalgType F of uaL].
have unitE: GRing.Field.mixin_of urL.
  move=> x nz_x; apply/unitrP; set q := rVpoly x.
  have nz_q: q != 0 by rewrite -(can_eq rVpolyK) raddf0 in nz_x.
  have /Bezout_eq1_coprimepP[u upq1]: coprimep p q.
    have /contraR := irr_p _ _ (dvdp_gcdl p q); apply.
    have: size (gcdp p q) <= size q by apply: leq_gcdpr.
    rewrite leqNgt; apply: contra; move/eqp_size ->.
    by rewrite (polySpred nz_p) ltnS size_poly.
  suffices: x * toL u.2 = 1 by exists (toL u.2); rewrite mulrC.
  congr (poly_rV _); rewrite toL_K modp_mul mulrC (canRL (addKr _) upq1).
  by rewrite -mulNr modp_addl_mul_small ?size_poly1.
pose ucrL := [comUnitRingType of ComRingType urL mulC].
pose fL := FieldType (IdomainType ucrL (GRing.Field.IdomainMixin unitE)) unitE.
exists [fieldExtType F of faL for fL]; first exact: mul1n.
pose z : vL := toL 'X; set iota := in_alg _.
have q_z q: rVpoly (map_poly iota q).[z] = q %% p.
  elim/poly_ind: q => [|a q IHq].
    by rewrite map_poly0 horner0 linear0 mod0p.
  rewrite rmorphD rmorphM /= map_polyX map_polyC hornerMXaddC linearD /=.
  rewrite linearZ /= L1K alg_polyC modp_add; congr (_ + _); last first.
    by rewrite modp_small // size_polyC; case: (~~ _) => //; apply: ltnW.
  by rewrite !toL_K IHq mulrC modp_mul mulrC modp_mul.
exists z; first by rewrite /root -(can_eq rVpolyK) q_z modpp linear0.
apply/vspaceP=> x; rewrite memvf; apply/Fadjoin_polyP.
exists (map_poly iota (rVpoly x)).
  by apply/polyOverP=> i; rewrite coef_map memvZ ?mem1v.
by apply/(can_inj rVpolyK); rewrite q_z modp_small // -Dn ltnS size_poly.
Qed.
*)
