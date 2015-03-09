(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div path fintype.
Require Import bigop finset prime fingroup morphism perm automorphism quotient.
Require Import action gproduct gfunctor pgroup cyclic center commutator.
Require Import gseries nilpotent sylow abelian maximal hall frobenius.
Require Import BGsection1 BGsection2 BGsection3 BGsection4 BGsection5.
Require Import BGsection6 BGsection7 BGsection9 BGsection10 BGsection12.
Require Import BGsection13 BGsection14 BGsection15.

(******************************************************************************)
(*   This file covers B & G, section 16; it summarises all the results of the *)
(* local analysis. Some of the definitions of B & G have been adapted to fit  *)
(* in beter with Peterfalvi, section 8, dropping unused properties and adding *)
(* a few missing ones. This file also defines the following:                  *)
(*    of_typeF M U <-> M = M`_\F ><| U is of type F, in the sense of          *)
(*                     Petervalvi (8.1) rather than B & G section 14.         *)
(* is_typeF_complement M U U0 <-> U0 is a subgroup of U with the same         *)
(*                     exponent as U, such that M`_\F ><| U0 is a Frobenius   *)
(*                     group; this corresponds to Peterfalvi (8.1)(c).        *)
(*    is_typeF_inertia M U U1 <-> U1 <| U is abelian and contains 'C_U[x] for *)
(*                     all x in M`_\F^#, and thus the inertia groups of all   *)
(*                     nonprincipal irreducible characters of M`_\F; this     *)
(*                     corresponds to Peterfalvi (8.1)(b).                    *)
(*    of_typeI M U <-> M = M`_\F ><| U is of type I, in the sense of          *)
(*                     Peterfalvi (8.3); this definition is almost identical  *)
(*                     to B & G conditions (Ii) - (Iv), except that (Iiv) is  *)
(*                     dropped, as is the condition p \in \pi* in (Iv)(c).    *)
(*                     Also, the condition 'O_p^'(M) cyclic, present in both  *)
(*                     B & G and Peterfalvi, is weakened to 'O_p^'(M`_\F)     *)
(*                     cyclic, because B & G, Theorem 15.7 only proves the    *)
(*                     weaker statement, and we did not manage to improve it. *)
(*                     This appears to be a typo in B & G that was copied     *)
(*                     over to Petrfalvi (8.3). It is probably no consequence *)
(*                     because (8.3) is only used in (12.6) and (12.10) and   *)
(*                     neither use the assumption that 'O_p^'(M) is cyclic.   *)
(*   For defW : W1 \x W2 = W we also define:                                  *)
(* of_typeP M U defW <-> M = M`_\F ><| U ><| W1 is of type P, in the sense of *)
(*                     Peterfalvi (8.4) rather than B & G section 14, where   *)
(*                     (8.4)(d,e) hold for W and W2 (i.e., W2 = C_M^(1)(W1)). *)
(* of_typeII_IV M U defW <-> M = M`_\F ><| U ><| W1 is of type II, III, or IV *)
(*                     in the sense of Peterfalvi (8.6)(a). This is almost    *)
(*                     exactly the contents of B & G, (T1)-(T7), except that  *)
(*                     (T6) is dropped, and 'C_(M`_\F)(W1) \subset M^`(2) is  *)
(*                     added (PF, (8.4)(d) and B & G, Theorem C(3)).          *)
(*  of_typeII M U defW <-> M = M`_\F ><| U ><| W1 is of type II in the sense  *)
(*                     of Peterfalvi (8.6); this differs from B & G by        *)
(*                     dropping the rank 2 clause in IIiii and replacing IIv  *)
(*                     by B(2)(3) (note that IIv is stated incorrectly: M'    *)
(*                     should be M'^#).                                       *)
(* of_typeIII M U defW <-> M = M`_\F ><| U ><| W1 is of type III in the sense *)
(*                     of Peterfalvi (8.6).                                   *)
(*  of_typeIV M U defW <-> M = M`_\F ><| U ><| W1 is of type IV in the sense  *)
(*                     of Peterfalvi (8.6).                                   *)
(*   of_typeV M U defW <-> U = 1 and M = M`_\F ><| W1 is of type V in the     *)
(*                     sense of Peterfalvi (8.7); this differs from B & G (V) *)
(*                     dropping the p \in \pi* condition in clauses (V)(b)    *)
(*                     and (V)(c).                                            *)
(*   exists_typeP spec <-> spec U defW holds for some groups U, W, W1 and W2  *)
(*                     such that defW : W1 \x W2 = W; spec will be one of     *)
(*                     (of_typeP M), (of_typeII_IV M), (of_typeII M), etc.    *)
(* FTtype_spec i M <-> M is of type i, for 0 < i <= 5, in the sense of the    *)
(*                     predicates above, for the appropriate complements to   *)
(*                     M`_\F and M^`(1).                                      *)
(*        FTtype M == the type of M, in the sense above, when M is a maximal  *)
(*                    subgroup of G (this is an integer i between 1 and 5).   *)
(*           M`_\s == an alternative, combinatorial definition of M`_\sigma   *)
(*                 := M`_\F if M is of type I or II, else M^`(1)              *)
(*          'A1(M) == the "inner Dade support" of a maximal group M, as       *)
(*                    defined in Peterfalvi (8.10).                           *)
(*                 := (M`_\s)^#                                               *)
(*           'A(M) == the "Dade support" of M as defined in Peterfalvi (8.10) *)
(*                    (this differs from B & G by excluding 1).               *)
(*          'A0(M) == the "outer Dade support" of M as defined in Peterfalvi  *)
(*                    (8.10) (this differs from B & G by excluding 1).        *)
(*            'M^G == a transversal of the conjugacy classes of 'M.           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Section GeneralDefinitions.

Variable gT : finGroupType.
Implicit Types V W X : {set gT}.

End GeneralDefinitions.

Section Definitions.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).

Implicit Types M U V W X : {set gT}.

Definition is_typeF_inertia M U (H := M`_\F) U1 :=
  [/\ U1 <| U, abelian U1 & {in H^#, forall x, 'C_U[x] \subset U1}].

Definition is_typeF_complement M U (H := M`_\F) U0 :=
  [/\ U0 \subset U, exponent U0 = exponent U & [Frobenius H <*> U0 = H ><| U0]].

Definition of_typeF M U (H := M`_\F) :=
 [/\ (*a*) [/\ H != 1, U :!=: 1 & H ><| U = M],
     (*b*) exists U1 : {group gT}, is_typeF_inertia M U U1
   & (*c*) exists U0 : {group gT}, is_typeF_complement M U U0].

Definition of_typeI M (H := M`_\F) U :=
    of_typeF M U
  /\ [\/ (*a*) normedTI H^# G M,
         (*b*) abelian H /\ 'r(H) = 2
       | (*c*) {in \pi(H), forall p, exponent U %| p.-1}
            /\ (exists2 p, p \in \pi(H) & cyclic 'O_p^'(H))].

Section Ptypes.

Variables M U W W1 W2 : {set gT}.
Let H := M`_\F.
Let M' := M^`(1).
Implicit Type defW : W1 \x W2 = W.

Definition of_typeP defW :=
  [/\ (*a*) [/\ cyclic W1, Hall M W1, W1 != 1 & M' ><| W1 = M],
      (*b*) [/\ nilpotent U, U \subset M', W1 \subset 'N(U) & H ><| U = M'],
      (*c*) [/\ ~~ cyclic H, M^`(2) \subset 'F(M), H * 'C_M(H) = 'F(M)
              & 'F(M) \subset M'],
      (*d*) [/\ cyclic W2, W2 != 1, W2 \subset H, W2 \subset M^`(2)
              & {in W1^#, forall x, 'C_M'[x] = W2}]
    & (*e*) normedTI (W :\: (W1 :|: W2)) G W].

Definition of_typeII_IV defW :=
  [/\ of_typeP defW, U != 1, prime #|W1| & normedTI 'F(M)^# G M].

Definition of_typeII defW :=
  [/\ of_typeII_IV defW, abelian U, ~~ ('N(U) \subset M),
      of_typeF M' U & M'`_\F = H].

Definition of_typeIII defW :=
  [/\ of_typeII_IV defW, abelian U & 'N(U) \subset M].

Definition of_typeIV defW :=
  [/\ of_typeII_IV defW, ~~ abelian U & 'N(U) \subset M].

Definition of_typeV defW :=
  [/\ of_typeP defW /\ U = 1
   & [\/ (*a*) normedTI H^# G M,
         (*b*) exists2 p, p \in \pi(H) & #|W1| %| p.-1 /\ cyclic 'O_p^'(H)
      |  (*c*) exists2 p, p \in \pi(H)
             & [/\ #|'O_p(H)| = (p ^ 3)%N, #|W1| %| p.+1 & cyclic 'O_p^'(H)]]].

End Ptypes.

CoInductive exists_typeP (spec : forall U W W1 W2, W1 \x W2 = W -> Prop) : Prop
  := FTtypeP_Spec (U W W1 W2 : {group gT}) defW of spec U W W1 W2 defW.

Definition FTtype_spec i M :=
  match i with
  | 1%N => exists U : {group gT}, of_typeI M U
  | 2 => exists_typeP (of_typeII M)
  | 3 => exists_typeP (of_typeIII M)
  | 4 => exists_typeP (of_typeIV M)
  | 5 => exists_typeP (of_typeV M)
  | _ => False
  end.

Definition FTtype M :=
  if \kappa(M)^'.-group M then 1%N else
  if M`_\sigma != M^`(1) then 2 else
  if M`_\F == M`_\sigma then 5 else
  if abelian (M`_\sigma / M`_\F) then 3 else 4.

Lemma FTtype_range M : 0 < FTtype M <= 5.
Proof. by rewrite /FTtype; do 4!case: ifP => // _. Qed.

Definition FTcore M := if 0 < FTtype M <= 2 then M`_\F else M^`(1).
Fact FTcore_is_group M : group_set (FTcore M).
Proof. rewrite /FTcore; case: ifP => _; exact: groupP. Qed.
Canonical Structure FTcore_group M := Group (FTcore_is_group M).

Definition FTsupport1 M := (FTcore M)^#.

Let FTder M := M^`(FTtype M != 1%N).

Definition FTsupport M := \bigcup_(x in FTsupport1 M) 'C_(FTder M)[x]^#.

Definition FTsupport0 M (pi := \pi(FTder M)) :=
  FTsupport M :|: [set x in M | ~~ pi.-elt x & ~~ pi^'.-elt x].

Definition mmax_transversal U := orbit_transversal 'JG U 'M.

End Definitions.

Notation "M `_ \s" := (FTcore M) (at level 3, format "M `_ \s") : group_scope.
Notation "M `_ \s" := (FTcore_group M) : Group_scope.

Notation "''A1' ( M )" := (FTsupport1 M)
  (at level 8, format "''A1' ( M )") : group_scope.

Notation "''A' ( M )" := (FTsupport M)
  (at level 8, format "''A' ( M )") : group_scope.

Notation "''A0' ( M )" := (FTsupport0 M)
  (at level 8, format "''A0' ( M )") : group_scope.

Notation "''M^' G" := (mmax_transversal G)
  (at level 3, format "''M^' G") : group_scope.

Section Section16.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).
Implicit Types p q q_star r : nat.
Implicit Types x y z : gT.
Implicit Types A E H K L M Mstar N P Q Qstar R S T U V W X Y Z : {group gT}.

(* Structural properties of the M`_\s definition. *)
Lemma FTcore_char M : M`_\s \char M.
Proof. by rewrite /FTcore; case: ifP; rewrite gFchar. Qed.

Lemma FTcore_normal M : M`_\s <| M.
Proof. by rewrite char_normal ?FTcore_char. Qed.

Lemma FTcore_norm M : M \subset 'N(M`_\s).
Proof. by rewrite char_norm ?FTcore_char. Qed.

Lemma FTcore_sub M : M`_\s \subset M.
Proof. by rewrite char_sub ?FTcore_char. Qed.

Lemma FTcore_type1 M : FTtype M == 1%N -> M`_\s = M`_\F.
Proof. by rewrite /M`_\s => /eqP->. Qed.

Lemma FTcore_type2 M : FTtype M == 2 -> M`_\s = M`_\F.
Proof. by rewrite /M`_\s => /eqP->. Qed.

Lemma FTcore_type_gt2 M : FTtype M > 2 -> M`_\s = M^`(1).
Proof. by rewrite /M`_\s => /subnKC <-. Qed.

Lemma FTsupp1_type1 M : FTtype M == 1%N -> 'A1(M) = M`_\F^#.
Proof. by move/FTcore_type1 <-. Qed.

Lemma FTsupp1_type2 M : FTtype M == 2 -> 'A1(M) = M`_\F^#.
Proof. by move/FTcore_type2 <-. Qed.

Lemma FTsupp1_type_gt2 M : FTtype M > 2 -> 'A1(M) = M^`(1)^#.
Proof. by move/FTcore_type_gt2 <-. Qed.

(* This section covers the characterization of the F, P, P1 and P2 types of   *)
(* maximal subgroups summarized at the top of p. 125. in B & G.               *)
Section KappaClassification.

Variables M U K : {group gT}.
Hypotheses (maxM : M \in 'M) (complU : kappa_complement M U K).

Remark trivgFmax : (M \in 'M_'F) = (K :==: 1).
Proof. by rewrite (trivg_kappa maxM); case: complU. Qed.

Remark trivgPmax : (M \in 'M_'P) = (K :!=: 1).
Proof. by rewrite inE trivgFmax maxM andbT. Qed.

Remark FmaxP : reflect (K :==: 1 /\ U :!=: 1) (M \in 'M_'F). 
Proof.
rewrite (trivg_kappa_compl maxM complU) 2!inE.
have [_ hallK _] := complU; rewrite (trivg_kappa maxM hallK).
by apply: (iffP idP) => [-> | []].
Qed.

Remark P1maxP : reflect (K :!=: 1 /\ U :==: 1) (M \in 'M_'P1).
Proof.
rewrite (trivg_kappa_compl maxM complU) inE -trivgPmax.
by apply: (iffP idP) => [|[] //]; case/andP=> ->.
Qed.

Remark P2maxP : reflect (K :!=: 1 /\ U :!=: 1) (M \in 'M_'P2).
Proof.
rewrite (trivg_kappa_compl maxM complU) -trivgPmax.
by apply: (iffP setDP) => [] [].
Qed.

End KappaClassification.

(* This section covers the combinatorial statements of B & G, Lemma 16.1. It  *)
(* needs to appear before summary theorems A-E because we are following       *)
(* Peterfalvi in anticipating the classification in the definition of the     *)
(* kernel sets A1(M), A(M) and A0(M). The actual correspondence between the   *)
(* combinatorial classification and the mathematical description, i.e., the   *)
(* of_typeXX predicates, will be given later.                                 *)
Section FTtypeClassification.

Variable M : {group gT}.
Hypothesis maxM : M \in 'M.

Lemma kappa_witness :
  exists UK : {group gT} * {group gT}, kappa_complement M UK.1 UK.2.
Proof.
have [K hallK] := Hall_exists \kappa(M) (mmax_sol maxM).
by have [U complU] := ex_kappa_compl maxM hallK; exists (U, K).
Qed.

(* This is B & G, Lemma 16.1(a). *)
Lemma FTtype_Fmax : (M \in 'M_'F) = (FTtype M == 1%N).
Proof.
by rewrite inE maxM /FTtype; case: (_.-group M) => //; do 3!case: ifP => // _.
Qed.

Lemma FTtype_Pmax : (M \in 'M_'P) = (FTtype M != 1%N).
Proof. by rewrite inE maxM andbT FTtype_Fmax. Qed.

(* This is B & G, Lemma 16.1(b). *)
Lemma FTtype_P2max : (M \in 'M_'P2) = (FTtype M == 2).
Proof.
have [[U K] /= complU] := kappa_witness.
rewrite (sameP (P2maxP maxM complU) andP) -(trivgFmax maxM complU) FTtype_Fmax.
have [-> // | notMtype1] := altP eqP.
have ntK: K :!=: 1 by rewrite -(trivgFmax maxM complU) FTtype_Fmax.
have [_ [//|defM' _] _ _ _] := kappa_structure maxM complU.
do [rewrite /FTtype; case: ifP => // _] in notMtype1 *.
rewrite -cardG_gt1 eqEcard Msigma_der1 //= -(sdprod_card defM') -ltnNge.
rewrite -(@ltn_pmul2l #|M`_\sigma|) ?cardG_gt0 //= muln1.
by case: leqP => // _; do 2!case: ifP=> //.
Qed.

(* This covers the P1 part of B & G, Lemma 16.1 (c) and (d). *)
Lemma FTtype_P1max : (M \in 'M_'P1) = (2 < FTtype M <= 5).
Proof.
rewrite 2!ltn_neqAle -!andbA FTtype_range andbT eq_sym -FTtype_P2max.
rewrite eq_sym -FTtype_Pmax in_setD inE.
by case: (M \in _); rewrite ?andbT ?andbF ?negbK.
Qed.

Lemma Msigma_eq_der1 : M \in 'M_'P1 -> M`_\sigma = M^`(1).
Proof.
have [[U K] /= complU] := kappa_witness.
case/(P1maxP maxM complU)=> ntK; move/eqP=> U1.
by have [_ [//|<- _] _ _ _] := kappa_structure maxM complU; rewrite U1 sdprodg1.
Qed.

Lemma def_FTcore : M`_\s = M`_\sigma.
Proof.
rewrite /FTcore -mem_iota 2!inE -FTtype_Fmax -FTtype_P2max.
have [notP1maxM |] := ifPn.
  by apply/Fcore_eq_Msigma; rewrite ?notP1type_Msigma_nil.
case/norP=> notFmaxM; rewrite inE andbC inE maxM notFmaxM negbK => P1maxM.
by rewrite Msigma_eq_der1.
Qed.

(* Other relations between the 'core' groups. *)

Lemma FTcore_sub_der1 : M`_\s \subset M^`(1)%g.
Proof. by rewrite def_FTcore Msigma_der1. Qed.

Lemma Fcore_sub_FTcore : M`_\F \subset M`_\s.
Proof. by rewrite def_FTcore Fcore_sub_Msigma. Qed.

Lemma mmax_Fcore_neq1 : M`_\F != 1.
Proof. by have [[]] := Fcore_structure maxM. Qed.

Lemma mmax_Fitting_neq1 : 'F(M) != 1.
Proof. exact: subG1_contra (Fcore_sub_Fitting M) mmax_Fcore_neq1. Qed.

Lemma FTcore_neq1 : M`_\s != 1.
Proof. exact: subG1_contra Fcore_sub_FTcore mmax_Fcore_neq1. Qed.

Lemma norm_mmax_Fcore : 'N(M`_\F) = M.
Proof. exact: mmax_normal (gFnormal _ _) mmax_Fcore_neq1. Qed.

Lemma norm_FTcore : 'N(M`_\s) = M.
Proof. exact: mmax_normal (FTcore_normal _) FTcore_neq1. Qed.

Lemma norm_mmax_Fitting : 'N('F(M)) = M.
Proof. exact: mmax_normal (gFnormal _ _) mmax_Fitting_neq1. Qed.

(* This is B & G, Lemma 16.1(f). *)
Lemma Fcore_eq_FTcore : reflect (M`_\F = M`_\s) (FTtype M \in pred3 1%N 2 5).
Proof.
rewrite /FTcore -mem_iota 3!inE orbA; case type12M: (_ || _); first by left.
move: type12M FTtype_P1max; rewrite /FTtype; do 2![case: ifP => // _] => _.
rewrite !(fun_if (leq^~ 5)) !(fun_if (leq 3)) !if_same /= => P1maxM.
rewrite Msigma_eq_der1 // !(fun_if (eq_op^~ 5)) if_same.
by rewrite [if _ then _ else _]andbT; apply: eqP.
Qed.

(* This is the second part of B & G, Lemma 16.1(c). *)
Lemma Fcore_neq_FTcore : (M`_\F != M`_\s) = (FTtype M \in pred2 3 4).
Proof.
have:= FTtype_range M; rewrite -mem_iota (sameP eqP Fcore_eq_FTcore).
by do 5!case/predU1P=> [-> //|].
Qed.

Lemma FTcore_eq_der1 : FTtype M > 2 -> M`_\s = M^`(1).
Proof.
move=> FTtype_gt2; rewrite def_FTcore Msigma_eq_der1 // FTtype_P1max.
by rewrite FTtype_gt2; case/andP: (FTtype_range M).
Qed.

End FTtypeClassification.

(* Internal automorphism. *)
Lemma FTtypeJ M x : FTtype (M :^ x) = FTtype M.
Proof.
rewrite /FTtype (eq_p'group _ (kappaJ _ _)) pgroupJ MsigmaJ FcoreJ derJ.
rewrite !(can_eq (conjsgK x)); do 4!congr (if _ then _ else _).
rewrite -quotientInorm normJ -conjIg /= setIC -{1 3}(setIidPr (normG M`_\F)).
rewrite -!morphim_conj -morphim_quotm ?normalG //= => nsMFN.
by rewrite injm_abelian /= ?im_quotient // injm_quotm ?injm_conj.
Qed.

Lemma FTcoreJ M x : (M :^ x)`_\s = M`_\s :^ x.
Proof. by rewrite /FTcore FTtypeJ FcoreJ derJ; case: ifP. Qed. 

Lemma FTsupp1J M x : 'A1(M :^ x) = 'A1(M) :^ x.
Proof. by rewrite conjD1g -FTcoreJ. Qed.

Lemma FTsuppJ M x : 'A(M :^ x) = 'A(M) :^ x.
Proof.
rewrite -bigcupJ /'A(_) FTsupp1J big_imset /=; last exact: in2W (conjg_inj x).
by apply: eq_bigr => y _; rewrite FTtypeJ derJ cent1J -conjIg conjD1g.
Qed.

Lemma FTsupp0J M x : 'A0(M :^ x) = 'A0(M) :^ x.
Proof.
apply/setP=> y; rewrite mem_conjg !inE FTsuppJ !mem_conjg; congr (_ || _ && _).
by rewrite FTtypeJ !p_eltJ derJ /= cardJg.
Qed.

(* Inclusion/normality of class function supports. *)

Lemma FTsupp_sub0 M : 'A(M) \subset 'A0(M).
Proof. exact: subsetUl. Qed.

Lemma FTsupp0_sub M : 'A0(M) \subset M^#.
Proof.
rewrite subUset andbC subsetD1 setIdE subsetIl !inE p_elt1 andbF /=.
by apply/bigcupsP=> x _; rewrite setSD ?subIset ?der_sub.
Qed.

Lemma FTsupp_sub M : 'A(M) \subset M^#.
Proof. exact: subset_trans (FTsupp_sub0 M) (FTsupp0_sub M). Qed.

Lemma FTsupp1_norm M : M \subset 'N('A1(M)).
Proof. by rewrite normD1 (normal_norm (FTcore_normal M)). Qed.

Lemma FTsupp_norm M : M \subset 'N('A(M)).
Proof.
apply/subsetP=> y My; rewrite inE -bigcupJ; apply/bigcupsP=> x A1x.
rewrite (bigcup_max (x ^ y)) ?memJ_norm ?(subsetP (FTsupp1_norm M)) //.
by rewrite conjD1g conjIg cent1J (normsP _ y My) ?gFnorm.
Qed.

Lemma FTsupp0_norm M : M \subset 'N('A0(M)).
Proof.
rewrite normsU ?FTsupp_norm // setIdE normsI //.
by apply/normsP=> x _; apply/setP=> y; rewrite mem_conjg !inE !p_eltJ.
Qed.

Section MmaxFTsupp.
(* Support inclusions that depend on the maximality of M. *)

Variable M : {group gT}.
Hypothesis maxM : M \in 'M.

Lemma FTsupp1_sub : 'A1(M) \subset 'A(M).
Proof.
apply/subsetP=> x A1x; apply/bigcupP; exists x => //.
have [ntx Ms_x] := setD1P A1x; rewrite 3!inE ntx cent1id (subsetP _ x Ms_x) //.
by case: (~~ _); rewrite ?FTcore_sub_der1 ?FTcore_sub.
Qed.

Lemma FTsupp1_sub0 : 'A1(M) \subset 'A0(M).
Proof. exact: subset_trans FTsupp1_sub (FTsupp_sub0 M). Qed.

Lemma FTsupp1_neq0 : 'A1(M) != set0.
Proof. by rewrite setD_eq0 subG1 FTcore_neq1. Qed.

Lemma FTsupp_neq0 : 'A(M) != set0.
Proof.
by apply: contraNneq FTsupp1_neq0 => AM_0; rewrite -subset0 -AM_0 FTsupp1_sub.
Qed.

Lemma FTsupp0_neq0 : 'A0(M) != set0.
Proof.
by apply: contraNneq FTsupp_neq0 => A0M_0; rewrite -subset0 -A0M_0 FTsupp_sub0.
Qed.

Lemma Fcore_sub_FTsupp1 : M`_\F^# \subset 'A1(M).
Proof. exact: setSD (Fcore_sub_FTcore maxM). Qed.

Lemma Fcore_sub_FTsupp : M`_\F^# \subset 'A(M).
Proof. exact: subset_trans Fcore_sub_FTsupp1 FTsupp1_sub. Qed.

Lemma Fcore_sub_FTsupp0 : M`_\F^# \subset 'A0(M).
Proof. exact: subset_trans Fcore_sub_FTsupp1 FTsupp1_sub0. Qed.

Lemma Fitting_sub_FTsupp : 'F(M)^# \subset 'A(M).
Proof.
pose pi := \pi(M`_\F); have nilF := Fitting_nil M.
have [U defF]: {U : {group gT} | M`_\F \x U = 'F(M)}.
  have hallH := pHall_subl (Fcore_sub_Fitting M) (gFsub _ _) (Fcore_Hall M).
  exists 'O_pi^'('F(M))%G; rewrite (nilpotent_Hall_pcore nilF hallH).
  exact: nilpotent_pcoreC.
apply/subsetP=> xy /setD1P[ntxy Fxy]; apply/bigcupP.
have [x [y [Hx Vy Dxy _]]] := mem_dprod defF Fxy.
have [z [ntz Hz czxy]]: exists z, [/\ z != 1%g, z \in M`_\F & x \in 'C[z]].
  have [-> | ntx] := eqVneq x 1%g; last by exists x; rewrite ?cent1id.
  by have /trivgPn[z ntz] := mmax_Fcore_neq1 maxM; exists z; rewrite ?group1.
exists z; first by rewrite !inE ntz (subsetP (Fcore_sub_FTcore maxM)).
rewrite 3!inE ntxy {2}Dxy groupMl //= andbC (subsetP _ y Vy) //=; last first.
  by rewrite sub_cent1 (subsetP _ _ Hz) // centsC; have [] := dprodP defF.
rewrite -FTtype_Pmax // (subsetP _ xy Fxy) //.
case MtypeP: (M \in _); last exact: gFsub.
by have [_ _ _ ->] := Fitting_structure maxM.
Qed.

Lemma Fitting_sub_FTsupp0 : 'F(M)^# \subset 'A0(M).
Proof. exact: subset_trans Fitting_sub_FTsupp (FTsupp_sub0 M). Qed.

Lemma FTsupp_eq1 : (2 < FTtype M)%N -> 'A(M) = 'A1(M).
Proof.
move=> typeMgt2; rewrite /'A(M) -(subnKC typeMgt2) /= -FTcore_eq_der1 //.
apply/setP=> y; apply/bigcupP/idP=> [[x A1x /setD1P[nty /setIP[Ms_y _]]] | A1y].
  exact/setD1P.
by exists y; rewrite // inE in_setI cent1id andbT -in_setD.
Qed.

End MmaxFTsupp.

Section SingleGroupSummaries.

Variables M U K : {group gT}.
Hypotheses (maxM : M \in 'M) (complU : kappa_complement M U K).

Let Kstar := 'C_(M`_\sigma)(K).

Theorem BGsummaryA :
 [/\ (*1*) [/\ M`_\sigma <| M, \sigma(M).-Hall(M) M`_\sigma &
               \sigma(M).-Hall(G) M`_\sigma],
     (*2*) \kappa(M).-Hall(M) K /\ cyclic K,
     (*3*) [/\ U \in [complements to M`_\sigma <*> K in M],
               K \subset 'N(U),
               M`_\sigma <*> U <| M,
               U <| U <*> K
             & M`_\sigma * U * K = M],
     (*4*) {in K^#, forall k, 'C_U[k] = 1}
  & 
 [/\ (*5*) Kstar != 1 /\ {in K^#, forall k, K \x Kstar = 'C_M[k]},
     (*6*) [/\ M`_\F != 1, M`_\F \subset M`_\sigma, M`_\sigma \subset M^`(1),
               M^`(1) \proper M & nilpotent (M^`(1) / M`_\F)],
     (*7*) [/\ M^`(2) \subset 'F(M), M`_\F * 'C_M(M`_\F) = 'F(M)
             & K :!=: 1 -> 'F(M) \subset M^`(1)]
   & (*8*) M`_\F != M`_\sigma ->
           [/\ U :=: 1, normedTI 'F(M)^# G M & prime #|K| ]]].
Proof.
have [hallU hallK _] := complU; split.
- by rewrite pcore_normal Msigma_Hall // Msigma_Hall_G.
- by have [[]] := kappa_structure maxM complU.
- have [_ defM _ _ _] := kappa_compl_context maxM complU.
  have [[_ UK _ defUK]] := sdprodP defM; rewrite defUK.
  have [nsKUK _ mulUK nUK _] := sdprod_context defUK.
  rewrite -mulUK mulG_subG mulgA => mulMsUK /andP[nMsU nMsK] _.
  rewrite (norm_joinEr nUK) mulUK; split=> //.
    rewrite inE coprime_TIg /= norm_joinEr //=.
      by rewrite -mulgA (normC nUK) mulgA mulMsUK !eqxx.
    rewrite (pnat_coprime _ (pHall_pgroup hallU)) // -pgroupE pgroupM.
    rewrite (sub_pgroup _ (pHall_pgroup hallK)) => [|p k_p]; last first.
      by apply/orP; right.
    by rewrite (sub_pgroup _ (pcore_pgroup _ _)) => // p s_p; apply/orP; left.
  have{defM} [[defM _ _] _ _ _ _] := kappa_structure maxM complU.
  have [[MsU _ defMsU] _ _ _ _] := sdprodP defM; rewrite defMsU in defM.
  have [_ mulMsU _ _] := sdprodP defMsU.
  by rewrite norm_joinEr // mulMsU; case/sdprod_context: defM.
- by have [] := kappa_compl_context maxM complU.
split.
- have [K1 | ntK] := eqsVneq K 1.
    rewrite /Kstar K1 cent1T setIT Msigma_neq1 // setDv.
    by split=> // k; rewrite inE.
  have PmaxM: M \in 'M_'P by rewrite inE -(trivg_kappa maxM hallK) ntK.
  have [_ [defNK _] [-> _] _ _] := Ptype_structure PmaxM hallK.
  have [_ _ cKKs tiKKs] := dprodP defNK; rewrite dprodEY //; split=> // k Kk.
  by have [_ _ [_ _ _ [_ _ -> // _ _] _]] := Ptype_embedding PmaxM hallK.
- have [_ _ [_ ->] _] := Fitting_structure maxM.
  by have [[]] := Fcore_structure maxM.
- have [_ [-> defF _] _ sFM'] := Fitting_structure maxM.
  have [_ -> _] := cprodP defF; split=> // ntK.
  by rewrite sFM' // inE -(trivg_kappa maxM hallK) ntK.
move=> not_nilMs; pose q := #|Kstar|.
have solMs: solvable M`_\sigma := solvableS (pcore_sub _ _) (mmax_sol maxM).
have [D hallD] := Hall_exists q^' solMs.
have [_] := Fcore_structure maxM; case/(_ K D)=> //.
case=> P1maxM _ _ [-> _ _ _] _ _ _; split=> //.
  by apply/eqP; rewrite (trivg_kappa_compl maxM complU).
by apply: contraR not_nilMs; case/nonTI_Fitting_facts=> // _ -> _.
Qed.

(* This is a variant of B & G, Lemma 16.1(e) that better fits the Peterfalvi  *)
(* definitions.                                                               *)
Lemma sdprod_FTder : M`_\sigma ><| U = M^`(FTtype M != 1%N).
Proof.
rewrite -FTtype_Fmax // (trivgFmax maxM complU).
have [[defM _ _] defM' _ _ _] := kappa_structure maxM complU.
by case: (altP eqP) defM' defM => [-> _ | _ [] //]; rewrite sdprodg1.
Qed.

Theorem BGsummaryB :
 [/\ (*1*) forall p S, p.-Sylow(U) S -> abelian S /\ 'r(S) <= 2,
     (*2*) abelian <<U :&: 'A(M)>>,
     (*3*) exists U0 : {group gT},
           [/\ U0 \subset U, exponent U0 = exponent U & [disjoint U0 & 'A(M)]]
  &  (*4*) (forall X, X \subset U -> X :!=: 1 -> 'C_(M`_\sigma)(X) != 1 ->
            'M('C(X)) = [set M])
  /\ (*5*) ('A(M) != 'A1(M) -> normedTI ('A(M) :\: 'A1(M)) G M)].
Proof.
split.
- move=> p S sylS; have [hallU _ _] := complU; have [sUM sk'U _] := and3P hallU.
  have [-> | ntS] := eqsVneq S 1; first by rewrite abelian1 rank1.
  have sk'p: p \in \sigma_kappa(M)^'.
    by rewrite (pnatPpi sk'U) // -p_rank_gt0 -(rank_Sylow sylS) rank_gt0.
  have{sylS} sylS := subHall_Sylow hallU sk'p sylS.
  have [[sSM pS _] [/= s'p _]] := (and3P sylS, norP sk'p).
  rewrite (sigma'_nil_abelian maxM) ?(pi_pgroup pS) ?(pgroup_nil pS) //.
  rewrite (rank_Sylow sylS) leqNgt (contra _ s'p) //; exact: alpha_sub_sigma.
- have [_ _ _ cUA_UA _] := kappa_structure maxM complU.
  apply: abelianS cUA_UA; rewrite genS // -big_distrr ?setIS -?def_FTcore //=.
  by apply/bigcupsP=> x A1x; rewrite (bigcup_max x) // setDE setIAC subsetIr.
- have [-> | ntU] := eqsVneq U 1.
    exists 1%G; split; rewrite // disjoint_sym disjoints_subset.
    by apply/bigcupsP=> x _; rewrite setDE subsetIr.
  have [_ _ _ _ [// | U0 [sU0U expU0 frobU0]]] := kappa_structure maxM complU.
  exists U0; split; rewrite // -setI_eq0 big_distrr /= /'A1(M) def_FTcore //.
  rewrite big1 // => x A1x; apply/eqP; rewrite setIDA setD_eq0 setICA.
  by rewrite (Frobenius_reg_compl frobU0) ?subsetIr.
set part4 := forall X, _; have part4holds: part4.
  move=> X sXU ntX nregX.
  by have [_ _] := kappa_structure maxM complU; case/(_ X).
have [[nsMsM _ _] _ [_ _ nsMsUM _ _] _ _] := BGsummaryA.
have{nsMsM nsMsUM}[[_ nMsM] [_ nMsUM]] := (andP nsMsM, andP nsMsUM).
rewrite eqEsubset FTsupp1_sub // -setD_eq0 andbT; set B := _ :\: _.
have nBM: M \subset 'N(B) by rewrite normsD ?FTsupp_norm ?FTsupp1_norm.
have uniqB y (u := y.`_\sigma(M)^'): y \in B -> 'M('C[u]) = [set M].
  case/setDP=> /bigcupP[x /setD1P[ntx Ms_x] /setD1P[nty /setIP[M'y cxy]]].
  rewrite !inE nty def_FTcore //= in Ms_x * => notMs_y; set M' := M^`(_) in M'y.
  have [nsMsM' _ _ _ _] := sdprod_context sdprod_FTder.
  have [[sMsM' nMsM'] sM'M]:= (andP nsMsM', der_sub _ M : M' \subset M).
  have hallMs := pHall_subl sMsM' sM'M (Msigma_Hall maxM).
  have hallU: \sigma(M)^'.-Hall(M') U.
    by rewrite -(compl_pHall _ hallMs) sdprod_compl ?sdprod_FTder.
  have suM': <[u]> \subset M' by rewrite cycle_subG groupX.
  have solM': solvable M' := solvableS sM'M (mmax_sol maxM).
  have [z M'z suzU] := Hall_Jsub solM' hallU suM' (p_elt_constt _ _).
  have Mz': z^-1 \in M by rewrite groupV (subsetP sM'M).
  rewrite -(conjgK z u) -(group_inj (conjGid Mz')) -cent_cycle.
  rewrite !cycleJ centJ; apply: def_uniq_mmaxJ (part4holds _ suzU _ _).
    rewrite /= -cycleJ cycle_eq1 -consttJ; apply: contraNneq notMs_y.
    move/constt1P; rewrite p_eltNK p_eltJ => sMy.
    by rewrite (mem_normal_Hall hallMs).
  rewrite -(normsP nMsM' z M'z) centJ -conjIg -(isog_eq1 (conj_isog _ _)).
  by apply/trivgPn; exists x; rewrite //= inE Ms_x cent_cycle cent1C groupX.
split=> // nzB; apply/normedTI_P; rewrite setTI; split=> // a _.
case/pred0Pn=> x /andP[/= Bx]; rewrite mem_conjg => /uniqB/(def_uniq_mmaxJ a).
rewrite consttJ -normJ conjg_set1 conjgKV uniqB // => /set1_inj defM.
by rewrite -(norm_mmax maxM) inE {2}defM.
Qed.

Let Z := K <*> Kstar.
Let Zhat := Z :\: (K :|: Kstar).

(*    We strengthened the uniqueness condition in part (4) to                 *)
(* 'M_\sigma(K) = [set Mstar].                                                *)
Theorem BGsummaryC : K :!=: 1 ->
 [/\
  [/\ (*1*) abelian U /\ ~~ ('N(U) \subset M),
      (*2*) [/\ cyclic Kstar, Kstar != 1, Kstar \subset M`_\F & ~~ cyclic M`_\F]
    & (*3*) M`_\sigma ><| U = M^`(1) /\ Kstar \subset M^`(2)],
  exists Mstar,
  [/\ (*4*) [/\ Mstar \in 'M_'P, 'C_(Mstar`_\sigma)(Kstar) = K,
                \kappa(Mstar).-Hall(Mstar) Kstar
              & 'M_\sigma(K) = [set Mstar]], (* uniqueness *)
      (*5*) {in 'E^1(Kstar), forall X, 'M('C(X)) = [set M]}
         /\ {in 'E^1(K), forall Y, 'M('C(Y)) = [set Mstar]},
      (*6*) [/\ M :&: Mstar = Z, K \x Kstar = Z & cyclic Z]
    & (*7*) (M \in 'M_'P2 \/ Mstar \in 'M_'P2)
         /\ {in 'M_'P, forall H, gval H \in M :^: G :|: Mstar :^: G}]
& [/\ (*8*) normedTI Zhat G Z,
      (*9*) let B := 'A0(M) :\: 'A(M) in
            B = class_support Zhat M /\ normedTI B G M,
     (*10*) U :!=: 1 ->
            [/\ prime #|K|, normedTI 'F(M)^# G M & M`_\sigma \subset 'F(M)]
   & (*11*) U :==: 1 -> prime #|Kstar| ]].
Proof.
move=> ntK; have [_ hallK _] := complU.
have PmaxM: M \in 'M_'P by rewrite inE -(trivg_kappa maxM hallK) ntK.
split.
- have [_ [//|-> ->] _ _ _] := kappa_structure maxM complU.
  have [-> -> -> -> ->] := Ptype_cyclics PmaxM hallK; do 2!split=> //.
  have [L maxCK_L] := mmax_exists (mFT_cent_proper ntK).
  have [-> | ntU] := eqsVneq U 1.
    by rewrite norm1 proper_subn // mmax_proper.
  have P2maxM: M \in 'M_'P2 by rewrite inE -(trivg_kappa_compl maxM complU) ntU.
  have [r _ rU] := rank_witness U; have [R sylR] := Sylow_exists r U.
  have ntR: R :!=: 1 by rewrite -rank_gt0 (rank_Sylow sylR) -rU rank_gt0.
  have ltRG: R \proper G := mFT_pgroup_proper (pHall_pgroup sylR).
  have [H maxNR_H] := mmax_exists (mFT_norm_proper ntR ltRG).
  apply: contra (subset_trans (subsetIr H _)) _.
  by have [_ _ _ [->]] := P2type_signalizer P2maxM complU maxCK_L sylR maxNR_H.
- have [L [PmaxL _] [uniqL []]] := Ptype_embedding PmaxM hallK.
  rewrite -/Kstar -/Z -/Zhat => hallKstar _ [defK _] [cycZ defML _ _ _].
  case=> _ P2_MorL Pmax_conjMorL _; exists L.
  suffices uniqMSK: 'M_\sigma(K) = [set L].
    have [_ [defNK _] [_ uniqM] _ _] := Ptype_structure PmaxM hallK.
    do 2!split=> //; last by case: P2_MorL => [] [-> _]; [left | right].
    by have [_ _ cKKs tiKKs] := dprodP defNK; rewrite dprodEY.
  have sKLs: K \subset L`_\sigma by rewrite -defK subsetIl.
  have [X E1X]: exists X, X \in 'E^1(K) by apply/rank_geP; rewrite rank_gt0.
  have sXK: X \subset K by case/nElemP: E1X => ? /pnElemP[].
  have [maxL sCXL] := mem_uniq_mmax (uniqL X E1X).
  have [x defKx] := cyclicP (cyclicS (joing_subl _ _) cycZ).
  have SMxL: L \in 'M_\sigma[x] by rewrite -defKx inE maxL.
  have ell1x: \ell_\sigma(x) == 1%N.
    by rewrite (Msigma_ell1 maxL) // !inE -cycle_eq1 -cycle_subG -defKx ntK.
  apply/eqP; rewrite eq_sym eqEcard defKx sub1set SMxL cards1 leqNgt.
  apply/negP=> ntSMx; have [_ [//|_ ntR _ _]] := FT_signalizer_context ell1x.
  case/(_ L)=> // /sdprodP[_ _ _ tiRL]; case/negP: ntR.
  rewrite -subG1 -tiRL subsetIidl -setIA setICA setISS ?pcore_sub //.
  by rewrite subsetIidr /= -cent_cycle -defKx (subset_trans (centS sXK) sCXL).
split; last 1 first.
- rewrite (trivg_kappa_compl maxM complU) => P1maxM.
  have [L _ [_ _ _ _ [_ [] [] //]]] := Ptype_embedding PmaxM hallK.
  by rewrite inE P1maxM.
- by have [L _ [_ _ _ _ [[]]]] := Ptype_embedding PmaxM hallK.
- have [L _ [_ _ _]] := Ptype_embedding PmaxM hallK; rewrite -/Zhat -/Z.
  case=> cycZ defML defCK defCKs defCZhat [[tiZhat tiZhatM _] _ _ defM] B.
  have sZM: Z \subset M by rewrite -[Z]defML subsetIl.
  have sZhM: Zhat \subset M by rewrite subDset setUC subsetU ?sZM.
  suffices defB: B = class_support Zhat M.
    split=> //; apply/normedTI_P.
    rewrite setTI normsD ?FTsupp_norm ?FTsupp0_norm //; split=> // [|g _].
      case/andP: tiZhat => /set0Pn[z Zz] _; apply/set0Pn; exists z.
      by rewrite defB mem_class_support.
    rewrite defB => /pred0Pn[_ /andP[/imset2P[z x Zz Mx ->] /= Bg_zx]].
    apply/idPn; rewrite -(groupMr g (groupVr Mx)) -in_setC.
    case/tiZhatM/pred0Pn; exists z; rewrite /= Zz conjsgM mem_conjgV.
    by apply: subsetP Bg_zx; rewrite conjSg class_support_subG.
  rewrite /B /'A0(M); set M' := M^`(_); set su := \pi(M').
  have defM': M' = M^`(1) by rewrite /M' -FTtype_Pmax ?PmaxM.
  have{hallK} hallM': su.-Hall(M) M'.
    by rewrite Hall_pi //= -/M' defM' (sdprod_Hall defM) (pHall_Hall hallK).
  have{hallM'} hallK: su^'.-Hall(M) K.
    by rewrite -(compl_pHall _ hallM') /= -/M' defM' sdprod_compl.
  have su'K: su^'.-group K := pHall_pgroup hallK.
  have suKs: su.-group Kstar.
    by rewrite (pgroupS _ (pgroup_pi _)) ///= -/M' defM' subIset ?Msigma_der1.
  apply/setP=> x; rewrite !inE; apply/andP/imset2P=> [[]| [y a]]; last first.
    case/setDP=> Zy; rewrite inE => /norP[not_Ky notKs_y] Ma ->.
    have My := subsetP sZM y Zy; have Mya := groupJ My Ma.
    have [not_suy not_su'y]: ~~ su.-elt y /\ ~~ su^'.-elt y.
      have defZ: K * Kstar = Z by rewrite -cent_joinEr ?subsetIr.
      have [hallK_Z hallKs] := coprime_mulGp_Hall defZ su'K suKs.
      have ns_Z := sub_abelian_normal _ (cyclic_abelian cycZ).
      rewrite -(mem_normal_Hall hallKs) -?ns_Z ?joing_subr // notKs_y.
      by rewrite -(mem_normal_Hall hallK_Z) -?ns_Z ?joing_subl.
    rewrite Mya !p_eltJ not_suy not_su'y orbT; split=> //.
    apply: contra not_suy => /bigcupP[_ _ /setD1P[_ /setIP[M'ya _]]].
    by rewrite -(p_eltJ _ y a) (mem_p_elt (pgroup_pi _)).
  move/negPf=> -> /and3P[Mx not_sux not_su'x]; set y := x.`_su^'.
  have syM: <[y]> \subset M by rewrite cycle_subG groupX.
  have [a Ma Kya] := Hall_Jsub (mmax_sol maxM) hallK syM (p_elt_constt _ _).
  have{Kya} K1ya: y ^ a \in K^#.
    rewrite !inE -cycle_subG cycleJ Kya andbT -consttJ.
    by apply: contraNneq not_sux; move/constt1P; rewrite p_eltNK p_eltJ.
  exists (x ^ a) a^-1; rewrite ?groupV ?conjgK // 2!inE andbC negb_or.
  rewrite -[Z](defCK _ K1ya) inE groupJ // cent1C -consttJ groupX ?cent1id //.
  by rewrite (contra (mem_p_elt su'K)) ?(contra (mem_p_elt suKs)) ?p_eltJ.
rewrite (trivg_kappa_compl maxM complU) => notP1maxM.
have P2maxM: M \in 'M_'P2 by exact/setDP.
split; first by have [_ _ _ _ []] := Ptype_structure PmaxM hallK.
  apply: contraR notP1maxM; case/nonTI_Fitting_facts=> //.
  by case/setUP=> //; case/idPn; case/setDP: PmaxM.
have [<- | neqMF_Ms] := eqVneq M`_\F M`_\sigma; first exact: Fcore_sub_Fitting.
have solMs: solvable M`_\sigma := solvableS (pcore_sub _ _) (mmax_sol maxM).
have [D hallD] := Hall_exists #|Kstar|^' solMs.
by case: (Fcore_structure maxM) notP1maxM => _ /(_ K D)[] // [[->]].
Qed.

End SingleGroupSummaries.

Theorem BGsummaryD M : M \in 'M ->
 [/\ (*1*) {in M`_\sigma &, forall x y, y \in x ^: G -> y \in x ^: M},
     (*2*) forall g (Ms := M`_\sigma), g \notin M ->
           Ms:&: M :^ g = Ms :&: Ms :^ g /\ cyclic (Ms :&: M :^ g),
     (*3*) {in M`_\sigma^#, forall x,
            [/\ Hall 'C[x] 'C_M[x], 'R[x] ><| 'C_M[x] = 'C[x]
              & let MGx := [set Mg in M :^: G | x \in Mg] in
                [transitive 'R[x], on MGx | 'Js] /\ #|'R[x]| = #|MGx| ]}
   & (*4*) {in M`_\sigma^#, forall x (N := 'N[x]), ~~ ('C[x] \subset M) ->
           [/\ 'M('C[x]) = [set N] /\ N`_\F = N`_\sigma,
               x \in 'A(N) :\: 'A1(N) /\ N \in 'M_'F :|: 'M_'P2,
               \sigma(N)^'.-Hall(N) (M :&: N)
             & N \in 'M_'P2 ->
               [/\ M \in 'M_'F,
                   exists2 E, [Frobenius M = M`_\sigma ><| gval E] & cyclic E
                 & ~~ normedTI (M`_\F)^# G M]]}].
Proof.
move=> maxM; have [[U K] /= complU] := kappa_witness maxM.
have defSM: {in M`_\sigma^#,
  forall x, [set Mg in M :^: G | x \in Mg] = val @: 'M_\sigma[x]}.
- move=> x /setD1P[ntx Ms_x].
  have SMxM: M \in 'M_\sigma[x] by rewrite inE maxM cycle_subG.
  apply/setP=> /= Mg; apply/setIdP/imsetP=> [[] | [H]].
    case/imsetP=> g _ -> Mg_x; exists (M :^ g)%G => //=.
    rewrite inE cycle_subG (mem_Hall_pcore (Msigma_Hall _)) ?mmaxJ // maxM.
    by rewrite (eq_p_elt _ (sigmaJ _ _)) (mem_p_elt (pcore_pgroup _ M)).
  case/setIdP=> maxH; rewrite cycle_subG => Hs_x ->.
  split; last exact: subsetP (pcore_sub _ _) x Hs_x.
  pose p := pdiv #[x]; have pixp: p \in \pi(#[x]) by rewrite pi_pdiv order_gt1.
  apply/idPn=> /(sigma_partition maxM maxH)/(_ p).
  rewrite inE /= (pnatPpi (mem_p_elt (pcore_pgroup _ _) Ms_x)) //.
  by rewrite (pnatPpi (mem_p_elt (pcore_pgroup _ _) Hs_x)).
split.
- have hallMs := pHall_subl (subxx _) (subsetT _) (Msigma_Hall_G maxM).
  move=> x y Ms_x Ms_y /=/imsetP[a _ def_y]; rewrite def_y in Ms_y *.
  have [b /setIP[Mb _ ->]] := sigma_Hall_tame maxM hallMs Ms_x Ms_y.
  exact: mem_imset.
- move=> g notMg; split.
    apply/eqP; rewrite eqEsubset andbC setIS ?conjSg ?pcore_sub //=.
    rewrite subsetI subsetIl -MsigmaJ.
    rewrite (sub_Hall_pcore (Msigma_Hall _)) ?mmaxJ ?subsetIr //.
    rewrite (eq_pgroup _ (sigmaJ _ _)).
    exact: pgroupS (subsetIl _ _) (pcore_pgroup _ _).
  have [E hallE] := ex_sigma_compl maxM.
  by have [_ _] := sigma_compl_embedding maxM hallE; case/(_ g).
- move=> x Ms1x /=.
  have [[ntx Ms_x] ell1x] := (setD1P Ms1x, Msigma_ell1 maxM Ms1x).
  have [[trR oR nsRC hallR] defC] := FT_signalizer_context ell1x.
  have SMxM: M \in 'M_\sigma[x] by rewrite inE maxM cycle_subG.
  suffices defCx: 'R[x] ><| 'C_M[x] = 'C[x].
    split=> //; first by rewrite -(sdprod_Hall defCx).
    rewrite defSM //; split; last by rewrite (card_imset _ val_inj).
    apply/imsetP; exists (gval M); first exact: mem_imset.
    by rewrite -(atransP trR _ SMxM) -imset_comp.
  have [| SMgt1] := leqP #|'M_\sigma[x]| 1.
    rewrite leq_eqVlt {2}(cardD1 M) SMxM orbF => eqSMxM.
    have ->: 'R[x] = 1 by apply/eqP; rewrite trivg_card1 oR.
    by rewrite sdprod1g (setIidPr _) ?cent1_sub_uniq_sigma_mmax.
  have [uniqN _ _ _ defCx] := defC SMgt1.
  have{defCx} [[defCx _ _ _] [_ sCxN]] := (defCx M SMxM, mem_uniq_mmax uniqN).
  by rewrite -setIA (setIidPr sCxN) in defCx.
move=> x Ms1x /= not_sCM.
have [[ntx Ms_x] ell1x] := (setD1P Ms1x, Msigma_ell1 maxM Ms1x).
have SMxM: M \in 'M_\sigma[x] by rewrite inE maxM cycle_subG.
have SMgt1: #|'M_\sigma[x]| > 1.
  apply: contraR not_sCM; rewrite -leqNgt leq_eqVlt {2}(cardD1 M) SMxM orbF.
  by move/cent1_sub_uniq_sigma_mmax->.
have [_ [//|uniqN ntR t2Nx notP1maxN]] := FT_signalizer_context ell1x.
have [maxN sCxN] := mem_uniq_mmax uniqN.
case/(_ M SMxM)=> _ st2NsM _ ->; split=> //.
- by rewrite (Fcore_eq_Msigma maxN (notP1type_Msigma_nil _)) // -in_setU.
- split=> //; apply/setDP; split.
    have [y Ry nty] := trivgPn _ ntR; have [Nsy cxy] := setIP Ry.
    apply/bigcupP; exists y; first by rewrite 2!inE def_FTcore ?nty.
    rewrite 3!inE ntx cent1C cxy -FTtype_Pmax //= andbT.
    have Nx: x \in 'N[x] by rewrite (subsetP sCxN) ?cent1id.
    case PmaxN: ('N[x] \in 'M_'P) => //.
    have [KN hallKN] := Hall_exists \kappa('N[x]) (mmax_sol maxN).
    have [_ _ [_ _ _ _ [_ _ _ defN]]] := Ptype_embedding PmaxN hallKN.
    have hallN': \kappa('N[x])^'.-Hall('N[x]) 'N[x]^`(1).
      exact/(sdprod_normal_pHallP (der_normal 1 _) hallKN).
    rewrite (mem_normal_Hall hallN') ?der_normal // (sub_p_elt _ t2Nx) // => p.
    by case/andP=> _; apply: contraL => /rank_kappa->.
  rewrite 2!inE ntx def_FTcore //=; apply: contra ntx => Ns_x.
  rewrite -(constt_p_elt (mem_p_elt (pcore_pgroup _ _) Ns_x)).
  by rewrite (constt1P (sub_p_elt _ t2Nx)) // => p; case/andP.
move=> P2maxN; have [PmaxN _] := setDP P2maxN; have [_ notFmaxN] := setDP PmaxN.
have [FmaxM _ [E _]] := nonFtype_signalizer_base maxM Ms1x not_sCM notFmaxN.
case=> cycE frobM; split=> //; first by exists E.
move: SMgt1; rewrite (cardsD1 M) SMxM ltnS lt0n => /pred0Pn[My /setD1P[neqMyM]].
move/(mem_imset val); rewrite -defSM //= => /setIdP[/imsetP[y _ defMy] My_x].
rewrite (Fcore_eq_Msigma maxM (notP1type_Msigma_nil _)) ?FmaxM //.
apply/normedTI_P=> [[_ _ /(_ y (in_setT y))/contraR/implyP/idPn[]]].
rewrite -{1}(norm_mmax maxM) (sameP normP eqP) -defMy neqMyM.
apply/pred0Pn; exists x; rewrite /= conjD1g !inE ntx Ms_x /= -MsigmaJ.
rewrite (mem_Hall_pcore (Msigma_Hall _)) ?mmaxJ /= -?defMy //.
by rewrite defMy (eq_p_elt _ (sigmaJ _ _)) (mem_p_elt (pcore_pgroup _ _) Ms_x).
Qed.

Lemma mmax_transversalP :
  [/\ 'M^G \subset 'M, is_transversal 'M^G (orbit 'JG G @: 'M) 'M,
      {in 'M^G &, injective (fun M => M :^: G)}
    & {in 'M, forall M, exists x, (M :^ x)%G \in 'M^G}].
Proof.
have: [acts G, on 'M | 'JG] by apply/actsP=> x _ M; rewrite mmaxJ.
case/orbit_transversalP; rewrite -/mmax_transversal => -> -> injMX memMX.
split=> // [M H MX_M MX_H /= eqMH | M /memMX[x _]]; last by exists x.
have /orbitP[x Gx defH]: val H \in M :^: G by rewrite eqMH orbit_refl.
by apply/eqP; rewrite -injMX // -(group_inj defH) (mem_orbit 'JG).
Qed.

(* We are conforming to the statement of B & G, but we defer the introduction *)
(* of 'M^G to Peterfalvi (8.17), which requires several other changes.        *)
Theorem BGsummaryE :
  [/\ (*1*) forall M, M \in 'M -> 
            #|class_support M^~~ G| = (#|M`_\sigma|.-1 * #|G : M|)%N,
      (*2*) {in \pi(G), forall p,
             exists2 M : {group gT}, M \in 'M & p \in \sigma(M)}
         /\ {in 'M &, forall M H,
             gval H \notin M :^: G -> [predI \sigma(M) & \sigma(H)] =i pred0}
    & (*3*) let PG := [set class_support M^~~ G | M : {group gT} in 'M] in
            [/\ partition PG (cover PG),
                'M_'P = set0 :> {set {group gT}} -> cover PG = G^#
              & forall M K, M \in 'M_'P -> \kappa(M).-Hall(M) K ->
                let Kstar := 'C_(M`_\sigma)(K) in
                let Zhat := (K <*> Kstar) :\: (K :|: Kstar) in
                partition [set class_support Zhat G; cover PG] G^#]].
Proof.
split=> [||PG]; first exact: card_class_support_sigma.
  by split=> [p /sigma_mmax_exists[M]|]; [exists M | apply: sigma_partition].
have [noPmax | ntPmax] := eqVneq 'M_'P (set0 : {set {group gT}}).
  rewrite noPmax; move/eqP in noPmax; have [partPG _] := mFT_partition gT.
  have /and3P[/eqP-> _ _] := partPG noPmax; rewrite partPG //.
  by split=> // M K; rewrite inE.
have [_ partZPG] := mFT_partition gT.
have partPG: partition PG (cover PG).
  have [M PmaxM] := set0Pn _ ntPmax; have [maxM _] := setDP PmaxM.
  have [K hallK] := Hall_exists \kappa(M) (mmax_sol maxM).
  have{partZPG} [/and3P[_ tiPG]] := partZPG M K PmaxM hallK.
  rewrite inE => /norP[_ notPGset0] _; apply/and3P; split=> //; apply/trivIsetP.
  by apply: sub_in2 (trivIsetP tiPG) => C; apply: setU1r.
split=> // [noPmax | M K PmaxM hallK]; first by case/eqP: ntPmax.
have [/=] := partZPG M K PmaxM hallK; rewrite -/PG; set Z := class_support _ G.
case/and3P=> /eqP defG1 tiZPG; rewrite 2!inE => /norP[nzZ _] notPGZ.
have [_ tiPG nzPG] := and3P partPG; have [maxM _] := setDP PmaxM.
rewrite /cover big_setU1 //= -/(cover PG) in defG1.
rewrite /trivIset /cover !big_setU1 //= (eqnP tiPG) -/(cover PG) in tiZPG.
have tiZ_PG: Z :&: cover PG = set0.
  by apply/eqP; rewrite setI_eq0 -leq_card_setU eq_sym.
have notUPGZ: Z \notin [set cover PG].
  by rewrite inE; apply: contraNneq nzZ => defZ; rewrite -tiZ_PG -defZ setIid.
rewrite /partition /trivIset /(cover _) !big_setU1 // !big_set1 /= -defG1.
rewrite eqxx tiZPG !inE negb_or nzZ /= eq_sym; apply: contraNneq nzPG => PG0.
apply/imsetP; exists M => //; apply/eqP; rewrite eq_sym -subset0 -PG0.
by rewrite (bigcup_max (class_support M^~~ G)) //; apply: mem_imset.
Qed.

Let typePfacts M (H := M`_\F) U W1 W2 W (defW : W1 \x W2 = W) :
     M \in 'M -> of_typeP M U defW ->
  [/\ M \in 'M_'P, \kappa(M).-Hall(M) W1, 'C_H(W1) = W2,
     (M \in 'M_'P1) = (U :==: 1) || ('N(U) \subset M)
    & let Ms := M`_\sigma in
      Ms = M^`(1) -> (H == Ms) = (U :==: 1) /\ abelian (Ms / H) = abelian U].
Proof.
move=> maxM []{defW}; move: W1 W2 => K Ks [cycK hallK ntK defM] /=.
have [[_ /= sHMs sMsM' _] _] := Fcore_structure maxM.
rewrite -/H in sHMs * => [] [nilU sUM' nUK defM'] _ [_ ntKs sKsH _ prKsK _].
have [_ sKM mulM'K _ tiM'K] := sdprod_context defM.
have defKs: 'C_H(K) = Ks.
  have [[x defK] sHM'] := (cyclicP cycK, subset_trans sHMs sMsM').
  have K1x: x \in K^# by rewrite !inE -cycle_eq1 -cycle_subG -defK subxx andbT.
  by rewrite -(setIidPl sHM') -setIA defK cent_cycle prKsK // (setIidPr _).
have{hallK} kK: \kappa(M).-group K.
  apply: sub_pgroup (pgroup_pi K) => p piKp.
  rewrite unlock 4!inE -!andb_orr orNb andbT -andbA.
  have [X EpX]: exists X, X \in 'E_p^1(K).
    by apply/p_rank_geP; rewrite p_rank_gt0.
  have [sXK abelX dimX] := pnElemP EpX; have [pX _] := andP abelX.
  have sXM := subset_trans sXK sKM.
  have ->: p \in \sigma(M)^'.
    apply: contra (nt_pnElem EpX isT) => sp.
    rewrite -subG1 -tiM'K subsetI (subset_trans _ sMsM') //.
    by rewrite (sub_Hall_pcore (Msigma_Hall maxM)) ?(pi_pgroup pX).
  have ->: 'r_p(M) == 1%N.
    rewrite -(p_rank_Hall (Hall_pi hallK)) // eqn_leq p_rank_gt0 piKp andbT.
    apply: leq_trans (p_rank_le_rank p K) _.
    by rewrite -abelian_rank1_cyclic ?cyclic_abelian.
  apply/existsP; exists X; rewrite 2!inE sXM abelX dimX /=.
  by rewrite (subG1_contra _ ntKs) // -defKs setISS ?centS.
have PmaxM : M \in 'M_'P.
  apply/PtypeP; split=> //; exists (pdiv #|K|).
  by rewrite (pnatPpi kK) // pi_pdiv cardG_gt1.
have hallK: \kappa(M).-Hall(M) K.
  rewrite pHallE sKM -(eqn_pmul2l (cardG_gt0 M^`(1))) (sdprod_card defM).
  have [K1 hallK1] := Hall_exists \kappa(M) (mmax_sol maxM).
  have [_ _ [_ _ _ _ [_ _ _ defM1]]] := Ptype_embedding PmaxM hallK1.
  by rewrite -(card_Hall hallK1) /= (sdprod_card defM1).
split=> // [|->]; first set Ms := M`_\sigma; last first.
  rewrite trivg_card_le1 -(@leq_pmul2l #|H|) ?cardG_gt0 // muln1.
  split; first by rewrite (sdprod_card defM') eqEcard (subset_trans sHMs).
  have [_ mulHU nHU tiHU] := sdprodP defM'.
  by rewrite -mulHU quotientMidl (isog_abelian (quotient_isog nHU tiHU)).
have [U1 | /= ntU] := altP eqP.
  rewrite inE PmaxM -{2}mulM'K /= -defM' U1 sdprodg1 pgroupM.
  have sH: \sigma(M).-group H := pgroupS sHMs (pcore_pgroup _ _).
  rewrite (sub_pgroup _ sH) => [|p sMp]; last by rewrite inE /= sMp.
  by rewrite (sub_pgroup _ kK) // => p kMp; rewrite inE /= kMp orbT.
have [P1maxM | notP1maxM] := boolP (M \in _).
  have defMs: Ms = M^`(1).
    have [U1 complU1] := ex_kappa_compl maxM hallK.
    have [_ [//|<- _] _ _ _] := kappa_structure maxM complU1.
    by case: (P1maxP maxM complU1 P1maxM) => _; move/eqP->; rewrite sdprodg1.
  pose p := pdiv #|U|; have piUp: p \in \pi(U) by rewrite pi_pdiv cardG_gt1.
  have hallU: \pi(H)^'.-Hall(M^`(1)) U.
    have sHM': H \subset M^`(1) by rewrite -defMs.
    have hallH := pHall_subl sHM' (der_sub 1 M) (Fcore_Hall M).
    by rewrite -(compl_pHall _ hallH) ?sdprod_compl.
  have piMs_p: p \in \pi(Ms) by rewrite defMs (piSg sUM').
  have{piMs_p} sMp: p \in \sigma(M) := pnatPpi (pcore_pgroup _ _) piMs_p.
  have sylP: p.-Sylow(M^`(1)) 'O_p(U).
    apply: (subHall_Sylow hallU (pnatPpi (pHall_pgroup hallU) piUp)).
    exact: nilpotent_pcore_Hall nilU.
  rewrite (subset_trans (char_norms (pcore_char p U))) //.
  rewrite (norm_sigma_Sylow sMp) //.
  by rewrite (subHall_Sylow (Msigma_Hall maxM)) //= -/Ms defMs.
suffices complU: kappa_complement M U K.
  by symmetry; apply/idPn; have [[[]]] := BGsummaryC maxM complU ntK.
split=> //; last by rewrite -norm_joinEr ?groupP.
rewrite pHallE (subset_trans _ (der_sub 1 M)) //=.
rewrite -(@eqn_pmul2l #|H|) ?cardG_gt0 // (sdprod_card defM').
have [U1 complU1] := ex_kappa_compl maxM hallK.
have [hallU1 _ _] := complU1; rewrite -(card_Hall hallU1).
have [_ [// | defM'1 _] _ _ _] := kappa_structure maxM complU1.
rewrite [H](Fcore_eq_Msigma maxM _) ?(sdprod_card defM'1) //.
by rewrite notP1type_Msigma_nil // in_setD notP1maxM PmaxM orbT.
Qed.

(* This is B & G, Lemma 16.1. *)
Lemma FTtypeP i M : M \in 'M -> reflect (FTtype_spec i M) (FTtype M == i).
Proof.
move=> maxM; pose Ms := M`_\sigma; pose M' := M^`(1); pose H := M`_\F.
have [[ntH sHMs sMsM' _] _] := Fcore_structure maxM.
apply: (iffP eqP) => [<- | ]; last first.
  case: i => [// | [[U [[[_ _ defM] _ [U0 [sU0U expU0 frobM]]] _]] | ]].
    apply/eqP; rewrite -FTtype_Fmax //; apply: wlog_neg => notFmaxM.
    have PmaxM: M \in 'M_'P by apply/setDP.
    apply/FtypeP; split=> // p; apply/idP=> kp.
    have [X EpX]: exists X, X \in 'E_p^1(U0).
      apply/p_rank_geP; rewrite p_rank_gt0 -pi_of_exponent expU0 pi_of_exponent.
      have: p \in \pi(M) by rewrite kappa_pi.
      rewrite /= -(sdprod_card defM) pi_ofM ?cardG_gt0 //; case/orP=> // Fk.
      have [[_ sMFMs _ _] _] := Fcore_structure maxM.
      case/negP: (kappa_sigma' kp).
      exact: pnatPpi (pcore_pgroup _ _) (piSg sMFMs Fk).
    have [[sXU0 abelX _] ntX] := (pnElemP EpX, nt_pnElem EpX isT).
    have kX := pi_pgroup (abelem_pgroup abelX) kp.
    have [_ sUM _ _ _] := sdprod_context defM.
    have sXM := subset_trans sXU0 (subset_trans sU0U sUM).
    have [K hallK sXK] := Hall_superset (mmax_sol maxM) sXM kX.
    have [ntKs _ _ sKsMF _] := Ptype_cyclics PmaxM hallK; case/negP: ntKs.
    rewrite -subG1 -(cent_semiregular (Frobenius_reg_ker frobM) sXU0 ntX).
    by rewrite subsetI sKsMF subIset // centS ?orbT.
  case=> [[U W K Ks defW [[PtypeM ntU _ _] _ not_sNUM _ _]] | ].
    apply/eqP; rewrite -FTtype_P2max // inE andbC.
    by have [-> _ _ -> _] := typePfacts maxM PtypeM; rewrite negb_or ntU.
  case=> [[U W K Ks defW [[PtypeM ntU _ _] cUU sNUM]] | ].
    have [_ _ _] := typePfacts maxM PtypeM.
    rewrite (negPf ntU) sNUM FTtype_P1max // cUU /FTtype -/Ms -/M' -/H.
    by case: ifP => // _; case: (Ms =P M') => // -> _ [//|-> ->].
  case=> [[U W K Ks defW [[PtypeM ntU _ _] not_cUU sNUM]] | ].
    have [_ _ _] := typePfacts maxM PtypeM.
    rewrite (negPf ntU) (negPf not_cUU) sNUM FTtype_P1max // /FTtype -/Ms -/M'.
    by case: ifP => // _; case: (Ms =P M') => // -> _ [//|-> ->].
  case=> // [[U K Ks W defW [[PtypeM U_1] _]]].
  have [_ _ _] := typePfacts maxM PtypeM.
  rewrite U_1 eqxx FTtype_P1max //= /FTtype -/Ms -/M' -/H.
  by case: ifP => // _; case: (Ms =P M') => // -> _ [//|-> _].
have [[U K] /= complU] := kappa_witness maxM; have [hallU hallK _] := complU.
have [K1 | ntK] := eqsVneq K 1.
  have FmaxM: M \in 'M_'F by rewrite -(trivg_kappa maxM hallK) K1.
  have ->: FTtype M = 1%N by apply/eqP; rewrite -FTtype_Fmax.
  have ntU: U :!=: 1 by case/(FmaxP maxM complU): FmaxM.
  have defH: H = Ms. 
    by apply/Fcore_eq_Msigma; rewrite // notP1type_Msigma_nil ?FmaxM.
  have defM: H ><| U = M.
    by have [_] := kappa_compl_context maxM complU; rewrite defH K1 sdprodg1.
  exists U; split.
    have [_ _ _ cU1U1 exU0] := kappa_structure maxM complU.
    split=> //; last by rewrite -/Ms -defH in exU0; exact: exU0.
    exists [group of <<\bigcup_(x in (M`_\sigma)^#) 'C_U[x]>>].
    split=> //= [|x Hx]; last by rewrite sub_gen //= -/Ms -defH (bigcup_max x).
    rewrite -big_distrr /= /normal gen_subG subsetIl.
    rewrite norms_gen ?normsI ?normG //; apply/subsetP=> u Uu.
    rewrite inE sub_conjg; apply/bigcupsP=> x Msx.
    rewrite -sub_conjg -normJ conjg_set1 (bigcup_max (x ^ u)) ?memJ_norm //.
    by rewrite normD1 (subsetP (gFnorm _ _)) // (subsetP (pHall_sub hallU)).
  have [|] := boolP [forall (y | y \notin M), 'F(M) :&: 'F(M) :^ y == 1].
    move/forall_inP=> TI_F; constructor 1; apply/normedTI_P.
    rewrite setD_eq0 subG1 mmax_Fcore_neq1 // setTI normD1 gFnorm.
    split=> // x _; apply: contraR => /TI_F/eqP tiFx.
    rewrite -setI_eq0 conjD1g -setDIl setD_eq0 -set1gE -tiFx.
    by rewrite setISS ?conjSg ?Fcore_sub_Fitting.
  rewrite negb_forall_in => /exists_inP[y notMy ntX].
  have [_ _ _ _] := nonTI_Fitting_structure maxM notMy ntX.
  case=> [[] | [_]]; first by constructor 2.
  move: #|_| => p; set P := 'O_p(H); rewrite /= -/H => not_cPP cycHp'.
  case=> [expU | [_]]; [constructor 3 | by rewrite 2!inE FmaxM].
  split=> [q /expU | ].
    have [_ <- nHU tiHU] := sdprodP defM.
    by rewrite quotientMidl -(exponent_isog (quotient_isog _ _)).
  have sylP: p.-Sylow(H) P := nilpotent_pcore_Hall _ (Fcore_nil M).
  have ntP: P != 1 by apply: contraNneq not_cPP => ->; exact: abelian1.
  by exists p; rewrite // -p_rank_gt0 -(rank_Sylow sylP) rank_gt0.
have PmaxM: M \in 'M_'P by rewrite inE -(trivg_kappa maxM hallK) ntK.
have [Mstar _ [_ _ _ [cycW _ _ _ _]]] := Ptype_embedding PmaxM hallK.
case=> [[tiV _ _] _ _ defM {Mstar}].  
have [_ [_ cycK] [_ nUK _ _ _] _] := BGsummaryA maxM complU; rewrite -/H.
case=> [[ntKs defCMK] [_ _ _ _ nilM'H] [sM''F defF /(_ ntK)sFM'] types34].
have hallK_M := pHall_Hall hallK.
have [/= [[cUU not_sNUM]]] := BGsummaryC maxM complU ntK; rewrite -/H -/M' -/Ms.
case=> cycKs _ sKsH not_cycH [defM' sKsM''] _ [_ _ type2 _].
pose Ks := 'C_H(K); pose W := K <*> Ks; pose V := W :\: (K :|: Ks).
have defKs: 'C_Ms(K) = Ks by rewrite -(setIidPr sKsH) setIA (setIidPl sHMs).
rewrite {}defKs -/W -/V in ntKs tiV cycW cycKs sKsM'' sKsH defCMK.
have{defCMK} prM'K: {in K^#, forall k, 'C_M'[k] = Ks}.
  have sKsM': Ks \subset M' := subset_trans sKsM'' (der_sub 1 _).
  move=> k; move/defCMK=> defW; have:= dprod_modr defW sKsM'.
  have [_ _ _ ->] := sdprodP defM; rewrite dprod1g.
  by rewrite setIA (setIidPl (der_sub 1 M)).
have [sHM' nsM'M] := (subset_trans sHMs sMsM', der_normal 1 M : M' <| M).
have hallM': \kappa(M)^'.-Hall(M) M' by apply/(sdprod_normal_pHallP _ hallK).
have [sM'M k'M' _] := and3P hallM'.
have hallH_M': \pi(H).-Hall(M') H := pHall_subl sHM' sM'M (Fcore_Hall M).
have nsHM' := normalS sHM' sM'M (Fcore_normal M).
have defW: K \x Ks = W.
  rewrite dprodEY ?subsetIr //= setIC; apply/trivgP.
  by have [_ _ _ <-] := sdprodP defM; rewrite setSI ?subIset ?sHM'.
have [Ueq1 | ntU] := eqsVneq U 1; last first.
  have P2maxM: M \in 'M_'P2 by rewrite inE -(trivg_kappa_compl maxM complU) ntU.
  have ->: FTtype M = 2 by apply/eqP; rewrite -FTtype_P2max.
  have defH: H = Ms.
    by apply/Fcore_eq_Msigma; rewrite // notP1type_Msigma_nil ?P2maxM ?orbT.
  have [//|pr_K tiFM _] := type2; rewrite -defH in defM'.
  have [_ sUM' _ _ _] := sdprod_context defM'.
  have MtypeP: of_typeP M U defW by split; rewrite // abelian_nil.
  have defM'F: M'`_\F = H.
    apply/eqP; rewrite eqEsubset (Fcore_max hallH_M') ?Fcore_nil // andbT.
    rewrite (Fcore_max (subHall_Hall hallM' _ (Fcore_Hall _))) ?Fcore_nil //.
      by move=> p piM'Fp; apply: pnatPpi k'M' (piSg (Fcore_sub _) piM'Fp).
    exact: char_normal_trans (Fcore_char _) nsM'M.
  exists U _ K _ defW; split=> //; split; first by rewrite defM'F.
    by exists U; split=> // x _; apply: subsetIl.
  have [_ _ _ _ /(_ ntU)] := kappa_structure maxM complU.
  by rewrite -/Ms -defH -defM'F.
have P1maxM: M \in 'M_'P1 by rewrite -(trivg_kappa_compl maxM complU) Ueq1.
have: 2 < FTtype M <= 5 by rewrite -FTtype_P1max.
rewrite /FTtype -/H -/Ms; case: ifP => // _; case: eqP => //= defMs _.
have [Y hallY nYK]: exists2 Y, \pi(H)^'.-Hall(M') (gval Y) & K \subset 'N(Y).
  apply: coprime_Hall_exists; first by case/sdprodP: defM.
    by rewrite (coprime_sdprod_Hall_l defM) (pHall_Hall hallM').
  exact: solvableS sM'M (mmax_sol maxM).
have{defM'} defM': H ><| Y = M' by apply/(sdprod_normal_p'HallP _ hallY).
have MtypeP: of_typeP M Y defW.
  have [_ sYM' mulHY nHY tiHY] := sdprod_context defM'.
  do 2!split=> //; rewrite (isog_nil (quotient_isog nHY tiHY)).
  by rewrite /= -quotientMidl mulHY.
have [_ _ _ sNYG [//| defY1 ->]] := typePfacts maxM MtypeP.
rewrite defY1; have [Y1 | ntY] := altP (Y :=P: 1); last first.
  move/esym: sNYG; rewrite (negPf ntY) P1maxM /= => sNYG.
  have [|_ tiFM prK] := types34; first by rewrite defY1.
  by case: ifPn; exists Y _ K _ defW.
exists Y _ K _ defW; split=> //=.
have [|] := boolP [forall (y | y \notin M), 'F(M) :&: 'F(M) :^ y == 1].
  move/forall_inP=> TI_F; constructor 1; apply/normedTI_P.
  rewrite setD_eq0 subG1 mmax_Fcore_neq1 // setTI normD1 gFnorm.
  split=> // x _; apply: contraR => /TI_F/eqP tiFx.
  rewrite -setI_eq0 conjD1g -setDIl setD_eq0 -set1gE -tiFx.
  by rewrite setISS ?conjSg ?Fcore_sub_Fitting.
rewrite negb_forall_in => /exists_inP[y notMy ntX].
have [_ _ _ _] := nonTI_Fitting_structure maxM notMy ntX.
case=> [[] | [_]]; first by case/idPn; case/setDP: PmaxM.
move: #|_| => p; set P := 'O_p(H); rewrite /= -/H => not_cPP cycHp'.
have sylP: p.-Sylow(H) P := nilpotent_pcore_Hall _ (Fcore_nil M).
have ntP: P != 1 by apply: contraNneq not_cPP => ->; exact: abelian1.
have piHp: p \in \pi(H) by rewrite -p_rank_gt0 -(rank_Sylow sylP) rank_gt0.
have defH: H = Ms by apply/eqP; rewrite defY1 Y1.
rewrite -defMs -defH in defM; have [_ <- nHU tiHU] := sdprodP defM.
rewrite quotientMidl -(card_isog (quotient_isog _ _)) //.
rewrite -(exponent_isog (quotient_isog _ _)) // exponent_cyclic //=.
case=> [K_dv_H1 | []]; [constructor 2 | constructor 3]; exists p => //.
by rewrite K_dv_H1.
Qed.

(* This is B & G, Theorem I. *)
(* Note that the first assertion is not used in the Perterfalvi revision of   *)
(* the character theory part of the proof.                                    *)
Theorem BGsummaryI :
  [/\ forall H x a, Hall G H -> nilpotent H -> x \in H -> x ^ a \in H ->
      exists2 y, y \in 'N(H) & x ^ a = x ^ y
    & {in 'M, forall M, FTtype M == 1%N}
    \/ exists ST : {group gT} * {group gT}, let (S, T) := ST in
      [/\ S \in 'M /\ T \in 'M,
          exists Wi : {group gT} * {group gT}, let (W1, W2) := Wi in
          let W := W1 <*> W2 in let V := W :\: (W1 :|: W2) in
         (*a*) [/\ cyclic W, normedTI V G W & W1 :!=: 1 /\ W2 :!=: 1] /\
         (*b*) [/\ S^`(1) ><| W1 = S, T^`(1) ><| W2 = T & S :&: T = W],
     (*c*) {in 'M, forall M, FTtype M != 1%N ->
            exists x, S :^ x = M \/ T :^ x = M},
     (*d*) FTtype S == 2 \/ FTtype T == 2
   & (*e*) 1 < FTtype S <= 5 /\ 1 < FTtype T <= 5]].
Proof.
split=> [H x a hallH nilH Hx|].
  have [M maxM sHMs] := nilpotent_Hall_sigma nilH hallH.
  have{hallH} hallH := pHall_subl sHMs (subsetT _) (Hall_pi hallH).
  by case/(sigma_Hall_tame maxM hallH Hx) => // y; case/setIP; exists y.
have [allFM | ] := boolP (('M : {set {group gT}}) \subset 'M_'F).
  by left=> M maxM; rewrite -FTtype_Fmax // (subsetP allFM).
case/subsetPn=> S maxS notFmaxS; right.
have PmaxS: S \in 'M_'P by exact/setDP.
have [[U W1] /= complU] := kappa_witness maxS; have [_ hallW1 _] := complU.
have ntW1: W1 :!=: 1 by rewrite (trivg_kappa maxS).
have [[_ [_]]] := BGsummaryC maxS complU ntW1; set W2 := 'C_(_)(W1) => ntW2 _.
set W := W1 <*> W2; set V := W :\: _ => _ _ [T [[PmaxT defW1 hallW2 _] _]].
case=> defST _ cycW [P2maxST PmaxST] [tiV _ _] _.
have [maxT _] := setDP PmaxT.
have [_ _ [_ _ _ _ [_ _ _ defS]]] := Ptype_embedding PmaxS hallW1.
have [_ _ [_ _ _ _ [_ _ _ defT]]] := Ptype_embedding PmaxT hallW2.
exists (S, T); split=> //; first by exists (W1, [group of W2]).
- move=> M maxM; rewrite /= -FTtype_Pmax //.
  by case/PmaxST/setUP => /imsetP[x _ ->]; exists x; by [left | right].
- by rewrite -!{1}FTtype_P2max.
rewrite !{1}(ltn_neqAle 1) -!{1}andbA !{1}FTtype_range // !{1}andbT.
by rewrite !{1}(eq_sym 1%N) -!{1}FTtype_Pmax.
Qed.

Lemma FTsupp0_type1 M : FTtype M == 1%N -> 'A0(M) = 'A(M).
Proof.
move=> typeM; apply/setUidPl/subsetP=> x; rewrite typeM !inE => /and3P[Mx].
by rewrite (mem_p_elt (pgroup_pi M)).
Qed.

Lemma FTsupp0_typeP M (H := M`_\F) U W1 W2 W (defW : W1 \x W2 = W) :
    M \in 'M -> of_typeP M U defW ->
  let V := W :\: (W1 :|: W2) in 'A0(M) :\: 'A(M) = class_support V M.
Proof.
move: W1 W2 => K Ks in defW * => maxM MtypeP /=.
have [[_ _ ntK _] _ _ _ _] := MtypeP.
have [PmaxM hallK defKs _ _] := typePfacts maxM MtypeP.
have [[_ sHMs _ _] _] := Fcore_structure maxM.
have [V complV] := ex_kappa_compl maxM hallK.
have [[_ [_ _ sKsH _] _] _ [_ [-> _] _ _]] := BGsummaryC maxM complV ntK.
by rewrite -(setIidPr sKsH) setIA (setIidPl sHMs) defKs -(dprodWY defW).
Qed.

(* This is the part of B & G, Theorem II that is relevant to the proof of     *)
(* Peterfalvi (8.7). We drop the considerations on the set of supporting      *)
(* groups, in particular (Tii)(a), but do include additional information on D *)
(* namely the fact that D is included in 'A1(M), not just 'A(M).              *)
Theorem BGsummaryII M (X : {set gT}) :
    M \in 'M -> X \in pred2 'A(M) 'A0(M) ->
    let D := [set x in X | ~~ ('C[x] \subset M)] in
 [/\       D \subset 'A1(M), (* was 'A(M) in B & G *)
     (*i*) {in X, forall x a, x ^ a \in X -> exists2 y, y \in M & x ^ a = x ^ y}
  &  {in D, forall x (L := 'N[x]),
 [/\ (*ii*) 'M('C[x]) = [set L], FTtype L \in pred2 1%N 2,
     [/\ (*b*) L`_\F ><| (M :&: L) = L,
         (*c*) {in X, forall y, coprime #|L`_\F| #|'C_M[y]| },
         (*d*) x \in 'A(L) :\: 'A1(L)
       & (*e*) 'C_(L`_\F)[x] ><| 'C_M[x] = 'C[x]]
   & (*iii*) FTtype L == 2 ->
             exists2 E, [Frobenius M = M`_\F ><| gval E] & cyclic E]}].
Proof.
move=> maxM defX.
have sA0M: 'A0(M) \subset M := subset_trans (FTsupp0_sub M) (subsetDl M 1).
have sAA0: 'A(M) \subset 'A0(M) := FTsupp_sub0 M.
have sAM: 'A(M) \subset M := subset_trans sAA0 sA0M.
without loss {defX} ->: X / X = 'A0(M).
  case/pred2P: defX => ->; move/(_ _ (erefl _))=> //.
  set D0 := finset _ => [[sD0A1 tameA0 signD0]] D.
  have sDD0: D \subset D0 by rewrite /D /D0 !setIdE setSI.
  split=> [|x Ax a Axa|x Dx]; first exact: subset_trans sDD0 sD0A1.
    by apply: tameA0; exact: (subsetP sAA0).
  have [/= -> -> [-> coA0L -> -> frobL]] := signD0 x (subsetP sDD0 x Dx).
  by do 2![split=> //] => y Ay; rewrite coA0L // (subsetP sAA0).
move=> {X} D; pose Ms := M`_\sigma.
have tiA0A x a: x \in 'A0(M) :\: 'A(M) -> x ^ a \notin 'A(M).
  rewrite 3!inE; case: (x \in _) => //= /and3P[_ notM'x _].
  apply: contra notM'x => /bigcupP[y _ /setD1P[_ /setIP[Mx _]]].
  by rewrite -(p_eltJ _ _ a) (mem_p_elt (pgroup_pi _)).
have tiA0 x a: x \in 'A0(M) :\: 'A1(M) -> x ^ a \in 'A0(M) -> a \in M. 
  case/setDP=> A0x notA1x A0xa.
  have [Mx Mxa] := (subsetP sA0M x A0x, subsetP sA0M _ A0xa).
  have [[U K] /= complU] := kappa_witness maxM.
  have [Ax | notAx] := boolP (x \in 'A(M)).
    have [_ _ _ [_]] := BGsummaryB maxM complU; set B := _ :\: _ => tiB.
    have Bx: x \in B by apply/setDP.
    have /tiB/normedTI_memJ_P: 'A(M) != 'A1(M) by apply: contraTneq Ax => ->.
    case=> _ _ /(_ x) <- //; rewrite 3?inE // conjg_eq1; apply/andP; split.
      apply: contra notA1x; rewrite !inE def_FTcore // => /andP[->].
      by rewrite !(mem_Hall_pcore (Msigma_Hall maxM)) // p_eltJ.
    by apply: contraLR Ax => notAxa; rewrite -(conjgK a x) tiA0A // inE notAxa.
  have ntK: K :!=: 1.
    rewrite -(trivgFmax maxM complU) FTtype_Fmax //.
    by apply: contra notAx => /FTsupp0_type1 <-.
  have [_ _ [_ [_ /normedTI_memJ_P[_ _ tiB]] _ _]]:= BGsummaryC maxM complU ntK.
  by rewrite -(tiB x) inE ?tiA0A ?notAx // inE notAx.
have sDA1: D \subset 'A1(M).
  apply/subsetPn=> [[x /setIdP[A0x not_sCxM] notA1x]].
  case/subsetP: not_sCxM => a cxa.
  by apply: (tiA0 x); [exact/setDP | rewrite /conjg -(cent1P cxa) mulKg].
have sDMs1: D \subset Ms^# by rewrite /Ms -def_FTcore.
have [tameMs _ signM PsignM] := BGsummaryD maxM.
split=> // [x A0x a A0xa|x Dx].
  have [A1x | notA1x] := boolP (x \in 'A1(M)); last first.
    by exists a; rewrite // (tiA0 x) // inE notA1x.
  case/setD1P: A1x => _; rewrite def_FTcore // => Ms_x.
  apply/imsetP; rewrite tameMs ?mem_imset ?inE //.
  rewrite (mem_Hall_pcore (Msigma_Hall maxM)) ?(subsetP sA0M) //.
  by rewrite p_eltJ (mem_p_elt (pcore_pgroup _ _) Ms_x).
have [Ms1x [_ not_sCxM]] := (subsetP sDMs1 x Dx, setIdP Dx).
have [[uniqN defNF] [ANx typeN hallMN] type2] := PsignM x Ms1x not_sCxM.
have [maxN _] := mem_uniq_mmax uniqN.
split=> //; last 1 first.
- rewrite -FTtype_P2max // => /type2[FmaxM].
  by rewrite (Fcore_eq_Msigma maxM _) // notP1type_Msigma_nil ?FmaxM.
- by rewrite !inE -FTtype_Fmax // -FTtype_P2max // -in_setU.
split=> // [|y A0y|]; rewrite defNF ?sdprod_sigma //=; last by case/signM: Ms1x.
rewrite coprime_pi' ?cardG_gt0 // -pgroupE.
rewrite (eq_p'group _ (pi_Msigma maxN)); apply: wlog_neg => not_sNx'CMy.
have ell1x := Msigma_ell1 maxM Ms1x.
have SMxM: M \in 'M_\sigma[x] by rewrite inE maxM cycle_subG; case/setD1P: Ms1x.
have MSx_gt1: #|'M_\sigma[x]| > 1.
  rewrite ltn_neqAle lt0n {2}(cardD1 M) SMxM andbT eq_sym.
  by apply: contra not_sCxM; move/cent1_sub_uniq_sigma_mmax->.
have [FmaxM t2'M]: M \in 'M_'F /\ \tau2(M)^'.-group M.
  apply: (non_disjoint_signalizer_Frobenius ell1x MSx_gt1 SMxM).
  by apply: contra not_sNx'CMy; exact: pgroupS (subsetIl _ _).
have defA0: 'A0(M) = Ms^#.
  rewrite FTsupp0_type1; last by rewrite -FTtype_Fmax. 
  rewrite /'A(M) /'A1(M) -FTtype_Fmax // FmaxM def_FTcore //= -/Ms.
  apply/setP => z; apply/bigcupP/idP=> [[t Ms1t] | Ms1z]; last first.
    have [ntz Ms_z] := setD1P Ms1z.
    by exists z; rewrite // 3!inE ntz cent1id (subsetP (pcore_sub _ _) z Ms_z).
  case/setD1P=> ntz; case/setIP=> Mz ctz.
  rewrite 2!inE ntz (mem_Hall_pcore (Msigma_Hall maxM)) //.
  apply: sub_in_pnat (pnat_pi (order_gt0 z)) => p _ pi_z_p.
  have szM: <[z]> \subset M by rewrite cycle_subG.
  have [piMp [_ k'M]] := (piSg szM pi_z_p, setIdP FmaxM).
  apply: contraR (pnatPpi k'M piMp) => s'p /=.
  rewrite unlock; apply/andP; split.
    have:= piMp; rewrite (partition_pi_mmax maxM) (negPf s'p) orbF.
    by rewrite orbCA [p \in _](negPf (pnatPpi t2'M piMp)).
  move: pi_z_p; rewrite -p_rank_gt0 /= -(setIidPr szM).
  case/p_rank_geP=> P; rewrite pnElemI -setIdE => /setIdP[EpP sPz].
  apply/exists_inP; exists P => //; apply/trivgPn.
  have [ntt Ms_t] := setD1P Ms1t; exists t => //.
  by rewrite inE Ms_t (subsetP (centS sPz)) // cent_cycle cent1C.
move: A0y; rewrite defA0 => /setD1P[nty Ms_y].
have sCyMs: 'C_M[y] \subset Ms.
  rewrite -[Ms](setD1K (group1 _)) -subDset /= -defA0 subsetU //.
  rewrite (bigcup_max y) //; first by rewrite 2!inE nty def_FTcore.
  by rewrite -FTtype_Fmax ?FmaxM.
have notMGN: gval 'N[x] \notin M :^: G.
  have [_ [//|_ _ t2Nx _ _]] := FT_signalizer_context ell1x.
  have [ntx Ms_x] := setD1P Ms1x; have sMx := mem_p_elt (pcore_pgroup _ _) Ms_x.
  apply: contra ntx => /imsetP[a _ defN].
  rewrite -order_eq1 (pnat_1 sMx (sub_p_elt _ t2Nx)) // => p.
  by rewrite defN tau2J // => /andP[].
apply: sub_pgroup (pgroupS sCyMs (pcore_pgroup _ _)) => p sMp.
by apply: contraFN (sigma_partition maxM maxN notMGN p) => sNp; apply/andP.
Qed.

End Section16.


