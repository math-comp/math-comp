(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require Import fintype bigop finset tuple div ssralg.
From mathcomp Require Import countalg binomial.

(******************************************************************************)
(* This file provides a library for univariate polynomials over ring          *)
(* structures; it also provides an extended theory for polynomials whose      *)
(* coefficients range over commutative rings and integral domains.            *)
(*                                                                            *)
(*           {poly R} == the type of polynomials with coefficients of type R, *)
(*                       represented as lists with a non zero last element    *)
(*                       (big endian representation); the coefficient type R  *)
(*                       must have a canonical nzRingType structure cR. In    *)
(*                       fact {poly R} denotes the concrete type polynomial   *)
(*                       cR; R is just a phantom argument that lets type      *)
(*                       inferencereconstruct the (hidden) nzRingType         *)
(*                       structure cR.                                        *)
(*          p : seq R == the big-endian sequence of coefficients of p, via    *)
(*                       the coercion polyseq : polynomial >-> seq.           *)
(*             Poly s == the polynomial with coefficient sequence s (ignoring *)
(*                       trailing zeroes).                                    *)
(* \poly_(i < n) E(i) == the polynomial of degree at most n - 1 whose         *)
(*                       coefficients are given by the general term E(i)      *)
(*  0, 1, - p, p + q, == the usual ring operations: {poly R} has a canonical  *)
(* p * q, p ^+ n, ...    nzRingType structure, which is commutative / integral*)
(*                       when R is commutative / integral, respectively.      *)
(*      polyC c, c%:P == the constant polynomial c                            *)
(*                 'X == the (unique) variable                                *)
(*               'X^n == a power of 'X; 'X^0 is 1, 'X^1 is convertible to 'X  *)
(*               p`_i == the coefficient of 'X^i in p; this is in fact just   *)
(*                       the ring_scope notation generic seq-indexing using   *)
(*                       nth 0%R, combined with the polyseq coercion.         *)
(*                   *** The multi-rule coefE simplifies p`_i                 *)
(*            coefp i == the linear function p |-> p`_i (self-exapanding).    *)
(*             size p == 1 + the degree of p, or 0 if p = 0 (this is the      *)
(*                       generic seq function combined with polyseq).         *)
(*        lead_coef p == the coefficient of the highest monomial in p, or 0   *)
(*                       if p = 0 (hence lead_coef p = 0 iff p = 0)           *)
(*        p \is monic <=> lead_coef p == 1 (0 is not monic).                  *)
(* p \is a polyOver S <=> the coefficients of p satisfy S; S should have a    *)
(*                        key that should be (at least) an addrPred.          *)
(*             p.[x]  == the evaluation of a polynomial p at a point x using  *)
(*                       the Horner scheme                                    *)
(*                   *** The multi-rule hornerE (resp., hornerE_comm) unwinds *)
(*                       horner evaluation of a polynomial expression (resp., *)
(*                       in a non commutative ring, with side conditions).    *)
(*             p^`()  == formal derivative of p                               *)
(*             p^`(n) == formal n-derivative of p                             *)
(*            p^`N(n) == formal n-derivative of p divided by n!               *)
(*            p \Po q == polynomial composition; because this is naturally a  *)
(*                       a linear morphism in the first argument, this        *)
(*                       notation is transposed (q comes before p for redex   *)
(*                       selection, etc).                                     *)
(*                      := \sum(i < size p) p`_i *: q ^+ i                    *)
(*      odd_poly p    == monomials of odd degree of p                         *)
(*      even_poly p   == monomials of even degree of p                        *)
(*      take_poly n p == polynomial p without its monomials of degree >= n    *)
(*      drop_poly n p == polynomial p divided by X^n                          *)
(*      comm_poly p x == x and p.[x] commute; this is a sufficient condition  *)
(*                       for evaluating (q * p).[x] as q.[x] * p.[x] when R   *)
(*                       is not commutative.                                  *)
(*      comm_coef p x == x commutes with all the coefficients of p (clearly,  *)
(*                       this implies comm_poly p x).                         *)
(*           root p x == x is a root of p, i.e., p.[x] = 0                    *)
(*    n.-unity_root x == x is an nth root of unity, i.e., a root of 'X^n - 1  *)
(* n.-primitive_root x == x is a primitive nth root of unity, i.e., n is the  *)
(*                       least positive integer m > 0 such that x ^+ m = 1.   *)
(*                   *** The submodule poly.UnityRootTheory can be used to    *)
(*                       import selectively the part of the theory of roots   *)
(*                       of unity that doesn't mention polynomials explicitly *)
(*       map_poly f p == the image of the polynomial by the function f (which *)
(*     (locally, p^f)    is usually a ring morphism).                         *)
(*               p^:P == p lifted to {poly {poly R}} (:= map_poly polyC p).   *)
(*   commr_rmorph f u == u commutes with the image of f (i.e., with all f x). *)
(*   horner_morph cfu == given cfu : commr_rmorph f u, the function mapping p *)
(*                       to the value of map_poly f p at u; this is a ring    *)
(*                       morphism from {poly R} to the codomain of f when f   *)
(*                       is a ring morphism.                                  *)
(*      horner_eval u == the function mapping p to p.[u]; this function can   *)
(*                       only be used for u in a commutative ring, so it is   *)
(*                       always a linear ring morphism from {poly R} to R.    *)
(*       horner_alg a == given a in some R-algebra A, the function evaluating *)
(*                       a polynomial p at a; it is always a linear ring      *)
(*                       morphism from {poly R} to A.                         *)
(*     diff_roots x y == x and y are distinct roots; if R is a field, this    *)
(*                       just means x != y, but this concept is generalized   *)
(*                       to the case where R is only a ring with units (i.e., *)
(*                       a unitRingType); in which case it means that x and y *)
(*                       commute, and that the difference x - y is a unit     *)
(*                       (i.e., has a multiplicative inverse) in R.           *)
(*                       to just x != y).                                     *)
(*       uniq_roots s == s is a sequence or pairwise distinct roots, in the   *)
(*                       sense of diff_roots p above.                         *)
(*   *** We only show that these operations and properties are transferred by *)
(*       morphisms whose domain is a field (thus ensuring injectivity).       *)
(* We prove the factor_theorem, and the max_poly_roots inequality relating    *)
(* the number of distinct roots of a polynomial and its size.                 *)
(*   The some polynomial lemmas use following suffix interpretation :         *)
(*   C - constant polynomial (as in polyseqC : a%:P = nseq (a != 0) a).       *)
(*   X - the polynomial variable 'X (as in coefX : 'X`_i = (i == 1%N)).       *)
(*   Xn - power of 'X (as in monicXn : monic 'X^n).                           *)
(*                                                                            *)
(* Pdeg2.Field (exported by the present library) : theory of the degree 2     *)
(*   polynomials.                                                             *)
(* Pdeg2.FieldMonic : theory of Pdeg2.Field specialized to monic polynomials. *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope unity_root_scope.

Import GRing.Theory.
Local Open Scope ring_scope.

Reserved Notation "{ 'poly' T }" (format "{ 'poly'  T }").
Reserved Notation "c %:P" (format "c %:P").
Reserved Notation "p ^:P" (format "p ^:P").
Reserved Notation "'X".
Reserved Notation "''X^' n" (at level 1, format "''X^' n").
Reserved Notation "\poly_ ( i < n ) E"
  (at level 34, E at level 36, i, n at level 50,
   format "\poly_ ( i  <  n )  E").
Reserved Notation "p \Po q" (at level 50).
Reserved Notation "p ^`N ( n )" (format "p ^`N ( n )").
Reserved Notation "n .-unity_root" (format "n .-unity_root").
Reserved Notation "n .-primitive_root" (format "n .-primitive_root").

Local Notation simp := Monoid.simpm.

Section Polynomial.

Variable R : nzSemiRingType.

(* Defines a polynomial as a sequence with <> 0 last element *)
Record polynomial := Polynomial {polyseq :> seq R; _ : last 1 polyseq != 0}.

HB.instance Definition _ := [isSub for polyseq].
HB.instance Definition _ := [Choice of polynomial by <:].

Lemma poly_inj : injective polyseq. Proof. exact: val_inj. Qed.

Definition coefp i (p : polynomial) := p`_i.

End Polynomial.

(* We need to break off the section here to let the Bind Scope directives     *)
(* take effect.                                                               *)
Bind Scope ring_scope with polynomial.
Arguments polynomial R%_type.
Arguments polyseq {R} p%_R.
Arguments poly_inj {R} [p1%_R p2%_R] : rename.
Arguments coefp {R} i%_N / p%_R.
Notation "{ 'poly' T }" := (polynomial T) : type_scope.

Section SemiPolynomialTheory.

Variable R : nzSemiRingType.
Implicit Types (a b c x y z : R) (p q r d : {poly R}).

Definition lead_coef p := p`_(size p).-1.
Lemma lead_coefE p : lead_coef p = p`_(size p).-1. Proof. by []. Qed.

Definition poly_nil := @Polynomial R [::] (oner_neq0 R).
Definition polyC c : {poly R} := insubd poly_nil [:: c].

Local Notation "c %:P" := (polyC c).

(* Remember the boolean (c != 0) is coerced to 1 if true and 0 if false *)
Lemma polyseqC c : c%:P = nseq (c != 0) c :> seq R.
Proof. by rewrite val_insubd /=; case: (c == 0). Qed.

Lemma size_polyC c : size c%:P = (c != 0).
Proof. by rewrite polyseqC size_nseq. Qed.

Lemma coefC c i : c%:P`_i = if i == 0 then c else 0.
Proof. by rewrite polyseqC; case: i => [|[]]; case: eqP. Qed.

Lemma polyCK : cancel polyC (coefp 0).
Proof. by move=> c; rewrite [coefp 0 _]coefC. Qed.

Lemma polyC_inj : injective polyC.
Proof. by move=> c1 c2 eqc12; have:= coefC c2 0; rewrite -eqc12 coefC. Qed.

Lemma lead_coefC c : lead_coef c%:P = c.
Proof. by rewrite /lead_coef polyseqC; case: eqP. Qed.

(* Extensional interpretation (poly <=> nat -> R) *)
Lemma polyP p q : nth 0 p =1 nth 0 q <-> p = q.
Proof.
split=> [eq_pq | -> //]; apply: poly_inj.
without loss lt_pq: p q eq_pq / size p < size q.
  move=> IH; case: (ltngtP (size p) (size q)); try by move/IH->.
  by move/(@eq_from_nth _ 0); apply.
case: q => q nz_q /= in lt_pq eq_pq *; case/eqP: nz_q.
by rewrite (last_nth 0) -(subnKC lt_pq) /= -eq_pq nth_default ?leq_addr.
Qed.

Lemma size1_polyC p : size p <= 1 -> p = (p`_0)%:P.
Proof.
move=> le_p_1; apply/polyP=> i; rewrite coefC.
by case: i => // i; rewrite nth_default // (leq_trans le_p_1).
Qed.

(* Builds a polynomial by extension. *)
Definition cons_poly c p : {poly R} :=
  if p is Polynomial ((_ :: _) as s) ns then
    @Polynomial R (c :: s) ns
  else c%:P.

Lemma polyseq_cons c p :
  cons_poly c p = (if ~~ nilp p then c :: p else c%:P) :> seq R.
Proof. by case: p => [[]]. Qed.

Lemma size_cons_poly c p :
  size (cons_poly c p) = (if nilp p && (c == 0) then 0 else (size p).+1).
Proof. by case: p => [[|c' s] _] //=; rewrite size_polyC; case: eqP. Qed.

Lemma coef_cons c p i : (cons_poly c p)`_i = if i == 0 then c else p`_i.-1.
Proof.
by case: p i => [[|c' s] _] [] //=; rewrite polyseqC; case: eqP => //= _ [].
Qed.

(* Build a polynomial directly from a list of coefficients. *)
Definition Poly := foldr cons_poly 0%:P.

Lemma PolyK c s : last c s != 0 -> Poly s = s :> seq R.
Proof.
case: s => {c}/= [_ |c s]; first by rewrite polyseqC eqxx.
elim: s c => /= [|a s IHs] c nz_c; rewrite polyseq_cons ?{}IHs //.
by rewrite !polyseqC !eqxx nz_c.
Qed.

Lemma polyseqK p : Poly p = p.
Proof. by apply: poly_inj; apply: PolyK (valP p). Qed.

Lemma size_Poly s : size (Poly s) <= size s.
Proof.
elim: s => [|c s IHs] /=; first by rewrite polyseqC eqxx.
by rewrite polyseq_cons; case: ifP => // _; rewrite size_polyC; case: (~~ _).
Qed.

Lemma coef_Poly s i : (Poly s)`_i = s`_i.
Proof.
by elim: s i => [|c s IHs] /= [|i]; rewrite !(coefC, eqxx, coef_cons) /=.
Qed.

(* Build a polynomial from an infinite sequence of coefficients and a bound. *)
Definition poly_expanded_def n E := Poly (mkseq E n).
Fact poly_key : unit. Proof. by []. Qed.
Definition poly := locked_with poly_key poly_expanded_def.
Canonical poly_unlockable := [unlockable fun poly].
Local Notation "\poly_ ( i < n ) E" := (poly n (fun i : nat => E)).

Lemma polyseq_poly n E :
  E n.-1 != 0 -> \poly_(i < n) E i = mkseq [eta E] n :> seq R.
Proof.
rewrite unlock; case: n => [|n] nzEn; first by rewrite polyseqC eqxx.
by rewrite (@PolyK 0) // -nth_last nth_mkseq size_mkseq.
Qed.

Lemma size_poly n E : size (\poly_(i < n) E i) <= n.
Proof. by rewrite unlock (leq_trans (size_Poly _)) ?size_mkseq. Qed.

Lemma size_poly_eq n E : E n.-1 != 0 -> size (\poly_(i < n) E i) = n.
Proof. by move/polyseq_poly->; apply: size_mkseq. Qed.

Lemma coef_poly n E k : (\poly_(i < n) E i)`_k = (if k < n then E k else 0).
Proof.
rewrite unlock coef_Poly.
have [lt_kn | le_nk] := ltnP k n; first by rewrite nth_mkseq.
by rewrite nth_default // size_mkseq.
Qed.

Lemma lead_coef_poly n E :
  n > 0 -> E n.-1 != 0 -> lead_coef (\poly_(i < n) E i) = E n.-1.
Proof.
by case: n => // n _ nzE; rewrite /lead_coef size_poly_eq // coef_poly leqnn.
Qed.

Lemma coefK p : \poly_(i < size p) p`_i = p.
Proof.
by apply/polyP=> i; rewrite coef_poly; case: ltnP => // /(nth_default 0)->.
Qed.

(* Nmodule structure for polynomial *)
Definition add_poly_def p q := \poly_(i < maxn (size p) (size q)) (p`_i + q`_i).
Fact add_poly_key : unit. Proof. by []. Qed.
Definition add_poly := locked_with add_poly_key add_poly_def.
Canonical add_poly_unlockable := [unlockable fun add_poly].

Fact coef_add_poly p q i : (add_poly p q)`_i = p`_i + q`_i.
Proof.
rewrite unlock coef_poly; case: leqP => //.
by rewrite geq_max => /andP[le_p_i le_q_i]; rewrite !nth_default ?add0r.
Qed.

Fact add_polyA : associative add_poly.
Proof. by move=> p q r; apply/polyP=> i; rewrite !coef_add_poly addrA. Qed.

Fact add_polyC : commutative add_poly.
Proof. by move=> p q; apply/polyP=> i; rewrite !coef_add_poly addrC. Qed.

Fact add_poly0 : left_id 0%:P add_poly.
Proof.
by move=> p; apply/polyP=> i; rewrite coef_add_poly coefC if_same add0r.
Qed.

HB.instance Definition _ := GRing.isNmodule.Build (polynomial R)
  add_polyA add_polyC add_poly0.

(* Properties of the zero polynomial *)
Lemma polyC0 : 0%:P = 0 :> {poly R}. Proof. by []. Qed.

Lemma polyseq0 : (0 : {poly R}) = [::] :> seq R.
Proof. by rewrite polyseqC eqxx. Qed.

Lemma size_poly0 : size (0 : {poly R}) = 0%N.
Proof. by rewrite polyseq0. Qed.

Lemma coef0 i : (0 : {poly R})`_i = 0.
Proof. by rewrite coefC if_same. Qed.

Lemma lead_coef0 : lead_coef 0 = 0 :> R. Proof. exact: lead_coefC. Qed.

Lemma size_poly_eq0 p : (size p == 0) = (p == 0).
Proof. by rewrite size_eq0 -polyseq0. Qed.

Lemma size_poly_leq0 p : (size p <= 0) = (p == 0).
Proof. by rewrite leqn0 size_poly_eq0. Qed.

Lemma size_poly_leq0P p : reflect (p = 0) (size p <= 0).
Proof. by apply: (iffP idP); rewrite size_poly_leq0; move/eqP. Qed.

Lemma size_poly_gt0 p : (0 < size p) = (p != 0).
Proof. by rewrite lt0n size_poly_eq0. Qed.

Lemma gt_size_poly_neq0 p n : (size p > n)%N -> p != 0.
Proof. by move=> /(leq_ltn_trans _) h; rewrite -size_poly_eq0 lt0n_neq0 ?h. Qed.

Lemma nil_poly p : nilp p = (p == 0).
Proof. exact: size_poly_eq0. Qed.

Lemma poly0Vpos p : {p = 0} + {size p > 0}.
Proof. by rewrite lt0n size_poly_eq0; case: eqVneq; [left | right]. Qed.

Lemma polySpred p : p != 0 -> size p = (size p).-1.+1.
Proof. by rewrite -size_poly_eq0 -lt0n => /prednK. Qed.

Lemma lead_coef_eq0 p : (lead_coef p == 0) = (p == 0).
Proof.
rewrite -nil_poly /lead_coef nth_last.
by case: p => [[|x s] /= /negbTE // _]; rewrite eqxx.
Qed.

Lemma polyC_eq0 (c : R) : (c%:P == 0) = (c == 0).
Proof. by rewrite -nil_poly polyseqC; case: (c == 0). Qed.

Lemma size_poly1P p : reflect (exists2 c, c != 0 & p = c%:P) (size p == 1).
Proof.
apply: (iffP eqP) => [pC | [c nz_c ->]]; last by rewrite size_polyC nz_c.
have def_p: p = (p`_0)%:P by rewrite -size1_polyC ?pC.
by exists p`_0; rewrite // -polyC_eq0 -def_p -size_poly_eq0 pC.
Qed.

Lemma size_polyC_leq1 (c : R) : (size c%:P <= 1)%N.
Proof. by rewrite size_polyC; case: (c == 0). Qed.

Lemma leq_sizeP p i : reflect (forall j, i <= j -> p`_j = 0) (size p <= i).
Proof.
apply: (iffP idP) => [hp j hij| hp].
  by apply: nth_default; apply: leq_trans hij.
case: (eqVneq p) (lead_coef_eq0 p) => [->|p0]; first by rewrite size_poly0.
rewrite leqNgt; apply/contraFN => hs.
by apply/eqP/hp; rewrite -ltnS (ltn_predK hs).
Qed.

(* Size, leading coef, morphism properties of coef *)

Lemma coefD p q i : (p + q)`_i = p`_i + q`_i.
Proof. exact: coef_add_poly. Qed.

Lemma polyCD : {morph polyC : a b / a + b}.
Proof. by move=> a b; apply/polyP=> [[|i]]; rewrite coefD !coefC ?addr0. Qed.

Lemma size_polyD p q : size (p + q) <= maxn (size p) (size q).
Proof. by rewrite -[+%R]/add_poly unlock; exact: size_poly. Qed.

Lemma size_polyDl p q : size p > size q -> size (p + q) = size p.
Proof.
move=> ltqp; rewrite -[+%R]/add_poly unlock size_poly_eq (maxn_idPl (ltnW _))//.
by rewrite addrC nth_default ?simp ?nth_last //; case: p ltqp => [[]].
Qed.

Lemma size_sum I (r : seq I) (P : pred I) (F : I -> {poly R}) :
  size (\sum_(i <- r | P i) F i) <= \max_(i <- r | P i) size (F i).
Proof.
elim/big_rec2: _ => [|i p q _ IHp]; first by rewrite size_poly0.
by rewrite -(maxn_idPr IHp) maxnA leq_max size_polyD.
Qed.

Lemma lead_coefDl p q : size p > size q -> lead_coef (p + q) = lead_coef p.
Proof.
move=> ltqp; rewrite /lead_coef coefD size_polyDl //.
by rewrite addrC nth_default ?simp // -ltnS (ltn_predK ltqp).
Qed.

Lemma lead_coefDr p q : size q > size p -> lead_coef (p + q) = lead_coef q.
Proof. by move/lead_coefDl<-; rewrite addrC. Qed.

(* Polynomial semiring structure. *)

Definition mul_poly_def p q :=
  \poly_(i < (size p + size q).-1) (\sum_(j < i.+1) p`_j * q`_(i - j)).
Fact mul_poly_key : unit. Proof. by []. Qed.
Definition mul_poly := locked_with mul_poly_key mul_poly_def.
Canonical mul_poly_unlockable := [unlockable fun mul_poly].

Fact coef_mul_poly p q i :
  (mul_poly p q)`_i = \sum_(j < i.+1) p`_j * q`_(i - j)%N.
Proof.
rewrite unlock coef_poly -subn1 ltn_subRL add1n; case: leqP => // le_pq_i1.
rewrite big1 // => j _; have [lq_q_ij | gt_q_ij] := leqP (size q) (i - j).
  by rewrite [q`__]nth_default ?mulr0.
rewrite nth_default ?mul0r // -(leq_add2r (size q)) (leq_trans le_pq_i1) //.
by rewrite -leq_subLR -subnSK.
Qed.

Fact coef_mul_poly_rev p q i :
  (mul_poly p q)`_i = \sum_(j < i.+1) p`_(i - j)%N * q`_j.
Proof.
rewrite coef_mul_poly (reindex_inj rev_ord_inj) /=.
by apply: eq_bigr => j _; rewrite (sub_ordK j).
Qed.

Fact mul_polyA : associative mul_poly.
Proof.
move=> p q r; apply/polyP=> i; rewrite coef_mul_poly coef_mul_poly_rev.
pose coef3 j k := p`_j * (q`_(i - j - k)%N * r`_k).
transitivity (\sum_(j < i.+1) \sum_(k < i.+1 | k <= i - j) coef3 j k).
  apply: eq_bigr => /= j _; rewrite coef_mul_poly_rev big_distrr /=.
  by rewrite (big_ord_narrow_leq (leq_subr _ _)).
rewrite (exchange_big_dep predT) //=; apply: eq_bigr => k _.
transitivity (\sum_(j < i.+1 | j <= i - k) coef3 j k).
  apply: eq_bigl => j; rewrite -ltnS -(ltnS j) -!subSn ?leq_ord //.
  by rewrite -subn_gt0 -(subn_gt0 j) -!subnDA addnC.
rewrite (big_ord_narrow_leq (leq_subr _ _)) coef_mul_poly big_distrl /=.
by apply: eq_bigr => j _; rewrite /coef3 -!subnDA addnC mulrA.
Qed.

Fact mul_1poly : left_id 1%:P mul_poly.
Proof.
move=> p; apply/polyP => i; rewrite coef_mul_poly big_ord_recl subn0.
by rewrite big1 => [|j _]; rewrite coefC !simp.
Qed.

Fact mul_poly1 : right_id 1%:P mul_poly.
Proof.
move=> p; apply/polyP => i; rewrite coef_mul_poly_rev big_ord_recl subn0.
by rewrite big1 => [|j _]; rewrite coefC !simp.
Qed.

Fact mul_polyDl : left_distributive mul_poly +%R.
Proof.
move=> p q r; apply/polyP=> i; rewrite coefD !coef_mul_poly -big_split.
by apply: eq_bigr => j _; rewrite coefD mulrDl.
Qed.

Fact mul_polyDr : right_distributive mul_poly +%R.
Proof.
move=> p q r; apply/polyP=> i; rewrite coefD !coef_mul_poly -big_split.
by apply: eq_bigr => j _; rewrite coefD mulrDr.
Qed.

Fact mul_0poly : left_zero 0%:P mul_poly.
Proof.
move=> p; apply/polyP => i; rewrite coef_mul_poly big_ord_recl subn0.
by rewrite big1 => [|j _]; rewrite coefC !simp // coefC; case: ifP.
Qed.

Fact mul_poly0 : right_zero 0%:P mul_poly.
Proof.
move=> p; apply/polyP => i; rewrite coef_mul_poly_rev big_ord_recl subn0.
by rewrite big1 => [|j _]; rewrite coefC !simp // coefC; case: ifP.
Qed.

Fact poly1_neq0 : 1%:P != 0 :> {poly R}.
Proof. by rewrite polyC_eq0 oner_neq0. Qed.

HB.instance Definition _ := GRing.Nmodule_isNzSemiRing.Build (polynomial R)
  mul_polyA mul_1poly mul_poly1 mul_polyDl mul_polyDr mul_0poly mul_poly0
  poly1_neq0.

Lemma polyC1 : 1%:P = 1 :> {poly R}. Proof. by []. Qed.

Lemma polyseq1 : (1 : {poly R}) = [:: 1] :> seq R.
Proof. by rewrite polyseqC oner_neq0. Qed.

Lemma size_poly1 : size (1 : {poly R}) = 1.
Proof. by rewrite polyseq1. Qed.

Lemma coef1 i : (1 : {poly R})`_i = (i == 0)%:R.
Proof. by case: i => [|i]; rewrite polyseq1 /= ?nth_nil. Qed.

Lemma lead_coef1 : lead_coef 1 = 1 :> R. Proof. exact: lead_coefC. Qed.

Lemma coefM p q i : (p * q)`_i = \sum_(j < i.+1) p`_j * q`_(i - j)%N.
Proof. exact: coef_mul_poly. Qed.

Lemma coefMr p q i : (p * q)`_i = \sum_(j < i.+1) p`_(i - j)%N * q`_j.
Proof. exact: coef_mul_poly_rev. Qed.

Lemma coef0M p q : (p * q)`_0 = p`_0 * q`_0.
Proof. by rewrite coefM big_ord1. Qed.

Lemma coef0_prod I rI (F : I -> {poly R}) P :
  (\prod_(i <- rI| P i) F i)`_0 = \prod_(i <- rI | P i) (F i)`_0.
Proof. by apply: (big_morph _ coef0M); rewrite coef1 eqxx. Qed.

Lemma size_polyMleq p q : size (p * q) <= (size p + size q).-1.
Proof. by rewrite -[*%R]/mul_poly unlock size_poly. Qed.

Lemma mul_lead_coef p q :
  lead_coef p * lead_coef q = (p * q)`_(size p + size q).-2.
Proof.
pose dp := (size p).-1; pose dq := (size q).-1.
have [-> | nz_p] := eqVneq p 0; first by rewrite lead_coef0 !mul0r coef0.
have [-> | nz_q] := eqVneq q 0; first by rewrite lead_coef0 !mulr0 coef0.
have ->: (size p + size q).-2 = (dp + dq)%N.
  by do 2!rewrite polySpred // addSn addnC.
have lt_p_pq: dp < (dp + dq).+1 by rewrite ltnS leq_addr.
rewrite coefM (bigD1 (Ordinal lt_p_pq)) ?big1 ?simp ?addKn //= => i.
rewrite -val_eqE neq_ltn /= => /orP[lt_i_p | gt_i_p]; last first.
  by rewrite nth_default ?mul0r //; rewrite -polySpred in gt_i_p.
rewrite [q`__]nth_default ?mulr0 //= -subSS -{1}addnS -polySpred //.
by rewrite addnC -addnBA ?leq_addr.
Qed.

Lemma size_proper_mul p q :
  lead_coef p * lead_coef q != 0 -> size (p * q) = (size p + size q).-1.
Proof.
apply: contraNeq; rewrite mul_lead_coef eqn_leq size_polyMleq -ltnNge => lt_pq.
by rewrite nth_default // -subn1 -(leq_add2l 1) -leq_subLR leq_sub2r.
Qed.

Lemma lead_coef_proper_mul p q :
  let c := lead_coef p * lead_coef q in c != 0 -> lead_coef (p * q) = c.
Proof. by move=> /= nz_c; rewrite mul_lead_coef -size_proper_mul. Qed.

Lemma size_poly_prod_leq (I : finType) (P : pred I) (F : I -> {poly R}) :
  size (\prod_(i | P i) F i) <= (\sum_(i | P i) size (F i)).+1 - #|P|.
Proof.
rewrite -sum1_card.
elim/big_rec3: _ => [|i n m p _ IHp]; first by rewrite size_poly1.
have [-> | nz_p] := eqVneq p 0; first by rewrite mulr0 size_poly0.
rewrite (leq_trans (size_polyMleq _ _)) // subnS -!subn1 leq_sub2r //.
rewrite -addnS -addnBA ?leq_add2l // ltnW // -subn_gt0 (leq_trans _ IHp) //.
by rewrite polySpred.
Qed.

Lemma coefCM c p i : (c%:P * p)`_i = c * p`_i.
Proof.
rewrite coefM big_ord_recl subn0.
by rewrite big1 => [|j _]; rewrite coefC !simp.
Qed.

Lemma coefMC c p i : (p * c%:P)`_i = p`_i * c.
Proof.
rewrite coefMr big_ord_recl subn0.
by rewrite big1 => [|j _]; rewrite coefC !simp.
Qed.

Lemma polyCM : {morph polyC : a b / a * b}.
Proof. by move=> a b; apply/polyP=> [[|i]]; rewrite coefCM !coefC ?simp. Qed.

Lemma size_poly_exp_leq p n : size (p ^+ n) <= ((size p).-1 * n).+1.
Proof.
elim: n => [|n IHn]; first by rewrite size_poly1.
have [-> | nzp] := poly0Vpos p; first by rewrite exprS mul0r size_poly0.
rewrite exprS (leq_trans (size_polyMleq _ _)) //.
by rewrite -{1}(prednK nzp) mulnS -addnS leq_add2l.
Qed.

End SemiPolynomialTheory.
#[deprecated(since="mathcomp 2.4.0", note="renamed to `size_polyD`")]
Notation size_add := size_polyD (only parsing).
#[deprecated(since="mathcomp 2.4.0", note="renamed to `size_polyDl`")]
Notation size_addl := size_polyDl (only parsing).
#[deprecated(since="mathcomp 2.4.0", note="renamed to `size_polyMleq`")]
Notation size_mul_leq := size_polyMleq (only parsing).
#[deprecated(since="mathcomp 2.4.0", note="renamed to `size_poly_prod_leq`")]
Notation size_prod_leq := size_poly_prod_leq (only parsing).
#[deprecated(since="mathcomp 2.4.0", note="renamed to `size_poly_exp_leq`")]
Notation size_exp_leq := size_poly_exp_leq (only parsing).

Section PolynomialTheory.

Variable R : nzRingType.
Implicit Types (a b c x y z : R) (p q r d : {poly R}).

Local Notation "c %:P" := (polyC c).

Local Notation "\poly_ ( i < n ) E" := (poly n (fun i : nat => E)).

(* Zmodule structure for polynomial *)
Definition opp_poly_def p := \poly_(i < size p) - p`_i.
Fact opp_poly_key : unit. Proof. by []. Qed.
Definition opp_poly := locked_with opp_poly_key opp_poly_def.
Canonical opp_poly_unlockable := [unlockable fun opp_poly].

Fact coef_opp_poly p i : (opp_poly p)`_i = - p`_i.
Proof.
rewrite unlock coef_poly /=.
by case: leqP => // le_p_i; rewrite nth_default ?oppr0.
Qed.

Fact add_polyN : left_inverse 0%:P opp_poly (@add_poly _).
Proof.
move=> p; apply/polyP=> i.
by rewrite coef_add_poly coef_opp_poly coefC if_same addNr.
Qed.

HB.instance Definition _ := GRing.Nmodule_isZmodule.Build (polynomial R)
  add_polyN.

(* Size, leading coef, morphism properties of coef *)

Lemma coefN p i : (- p)`_i = - p`_i.
Proof. exact: coef_opp_poly. Qed.

Lemma coefB p q i : (p - q)`_i = p`_i - q`_i.
Proof. by rewrite coefD coefN. Qed.

HB.instance Definition _ i := GRing.isZmodMorphism.Build {poly R} R (coefp i)
  (fun p => (coefB p)^~ i).

Lemma coefMn p n i : (p *+ n)`_i = p`_i *+ n.
Proof. exact: (raddfMn (coefp i)). Qed.

Lemma coefMNn p n i : (p *- n)`_i = p`_i *- n.
Proof. by rewrite coefN coefMn. Qed.

Lemma coef_sum I (r : seq I) (P : pred I) (F : I -> {poly R}) k :
  (\sum_(i <- r | P i) F i)`_k = \sum_(i <- r | P i) (F i)`_k.
Proof. exact: (raddf_sum (coefp k)). Qed.

Lemma polyCN : {morph (@polyC R) : c / - c}.
Proof. by move=> c; apply/polyP=> [[|i]]; rewrite coefN !coefC ?oppr0. Qed.

Lemma polyCB : {morph (@polyC R) : a b / a - b}.
Proof. by move=> a b; rewrite polyCD polyCN. Qed.

HB.instance Definition _ := GRing.isZmodMorphism.Build R {poly R} (@polyC _) polyCB.

Lemma polyCMn n : {morph (@polyC R) : c / c *+ n}. Proof. exact: raddfMn. Qed.

Lemma size_polyN p : size (- p) = size p.
Proof.
by apply/eqP; rewrite eqn_leq -{3}(opprK p) -[-%R]/opp_poly unlock !size_poly.
Qed.

Lemma lead_coefN p : lead_coef (- p) = - lead_coef p.
Proof. by rewrite /lead_coef size_polyN coefN. Qed.

(* Polynomial ring structure. *)

Fact polyC_is_monoid_morphism : monoid_morphism (@polyC R).
Proof. by split; last apply: polyCM. Qed.
#[deprecated(since="mathcomp 2.5.0",
      note="use `polyC_is_monoid_morphism` instead")]
Definition polyC_multiplicative :=
  (fun g => (g.2, g.1)) polyC_is_monoid_morphism.
HB.instance Definition _ := GRing.isMonoidMorphism.Build R {poly R} (@polyC R)
  polyC_is_monoid_morphism.

Lemma polyC_exp n : {morph (@polyC R) : c / c ^+ n}. Proof. exact: rmorphXn. Qed.

Lemma polyC_natr n : n%:R%:P = n%:R :> {poly R}.
Proof. by rewrite rmorph_nat. Qed.

Lemma pchar_poly : [pchar {poly R}] =i [pchar R].
Proof.
move=> p; rewrite !inE; congr (_ && _).
apply/eqP/eqP=> [/(congr1 val) /=|]; last by rewrite -polyC_natr => ->.
by rewrite polyseq0 -polyC_natr polyseqC; case: eqP.
Qed.

Lemma size_Msign p n : size ((-1) ^+ n * p) = size p.
Proof.
by rewrite -signr_odd; case: (odd n); rewrite ?mul1r// mulN1r size_polyN.
Qed.

Fact coefp0_is_monoid_morphism : monoid_morphism (coefp 0 : {poly R} -> R).
Proof.
split=> [|p q]; first by rewrite polyCK.
by rewrite [coefp 0 _]coefM big_ord_recl big_ord0 addr0.
Qed.
#[deprecated(since="mathcomp 2.5.0",
      note="use `coefp0_is_monoid_morphism` instead")]
Definition coefp0_multiplicative :=
  (fun g => (g.2, g.1)) coefp0_is_monoid_morphism.
HB.instance Definition _ := GRing.isMonoidMorphism.Build {poly R} R (coefp 0)
  coefp0_is_monoid_morphism.

(* Algebra structure of polynomials. *)
Definition scale_poly_def a (p : {poly R}) := \poly_(i < size p) (a * p`_i).
Fact scale_poly_key : unit. Proof. by []. Qed.
Definition scale_poly := locked_with scale_poly_key scale_poly_def.
Canonical scale_poly_unlockable := [unlockable fun scale_poly].

Fact scale_polyE a p : scale_poly a p = a%:P * p.
Proof.
apply/polyP=> n; rewrite unlock coef_poly coefCM.
by case: leqP => // le_p_n; rewrite nth_default ?mulr0.
Qed.

Fact scale_polyA a b p : scale_poly a (scale_poly b p) = scale_poly (a * b) p.
Proof. by rewrite !scale_polyE mulrA polyCM. Qed.

Fact scale_1poly : left_id 1 scale_poly.
Proof. by move=> p; rewrite scale_polyE mul1r. Qed.

Fact scale_polyDr a : {morph scale_poly a : p q / p + q}.
Proof. by move=> p q; rewrite !scale_polyE mulrDr. Qed.

Fact scale_polyDl p : {morph scale_poly^~ p : a b / a + b}.
Proof. by move=> a b /=; rewrite !scale_polyE raddfD mulrDl. Qed.

Fact scale_polyAl a p q : scale_poly a (p * q) = scale_poly a p * q.
Proof. by rewrite !scale_polyE mulrA. Qed.

HB.instance Definition _ := GRing.Zmodule_isLmodule.Build R (polynomial R)
  scale_polyA scale_1poly scale_polyDr scale_polyDl.
HB.instance Definition _ := GRing.Lmodule_isLalgebra.Build R (polynomial R)
  scale_polyAl.

Lemma mul_polyC a p : a%:P * p = a *: p.
Proof. by rewrite -scale_polyE. Qed.

Lemma scale_polyC a b : a *: b%:P = (a * b)%:P.
Proof. by rewrite -mul_polyC polyCM. Qed.

Lemma alg_polyC a : a%:A = a%:P :> {poly R}.
Proof. by rewrite -mul_polyC mulr1. Qed.

Lemma coefZ a p i : (a *: p)`_i = a * p`_i.
Proof.
rewrite -[*:%R]/scale_poly unlock coef_poly.
by case: leqP => // le_p_n; rewrite nth_default ?mulr0.
Qed.

Lemma size_scale_leq a p : size (a *: p) <= size p.
Proof. by rewrite -[*:%R]/scale_poly unlock size_poly. Qed.

HB.instance Definition _ i := GRing.isScalable.Build R {poly R} R *%R (coefp i)
  (fun a => (coefZ a) ^~ i).
HB.instance Definition _ := GRing.Linear.on (coefp 0).

(* The indeterminate, at last! *)
Definition polyX_def := @Poly R [:: 0; 1].
Fact polyX_key : unit. Proof. by []. Qed.
Definition polyX : {poly R} := locked_with polyX_key polyX_def.
Canonical polyX_unlockable := [unlockable of polyX].
Local Notation "'X" := polyX.

Lemma polyseqX : 'X = [:: 0; 1] :> seq R.
Proof. by rewrite unlock !polyseq_cons nil_poly eqxx /= polyseq1. Qed.

Lemma size_polyX : size 'X = 2. Proof. by rewrite polyseqX. Qed.

Lemma polyX_eq0 : ('X == 0) = false.
Proof. by rewrite -size_poly_eq0 size_polyX. Qed.

Lemma coefX i : 'X`_i = (i == 1)%:R.
Proof. by case: i => [|[|i]]; rewrite polyseqX //= nth_nil. Qed.

Lemma lead_coefX : lead_coef 'X = 1.
Proof. by rewrite /lead_coef polyseqX. Qed.

Lemma commr_polyX p : GRing.comm p 'X.
Proof.
apply/polyP=> i; rewrite coefMr coefM.
by apply: eq_bigr => j _; rewrite coefX commr_nat.
Qed.

Lemma coefMX p i : (p * 'X)`_i = (if (i == 0)%N then 0 else p`_i.-1).
Proof.
rewrite coefMr big_ord_recl coefX ?simp.
case: i => [|i]; rewrite ?big_ord0 //= big_ord_recl polyseqX subn1 /=.
by rewrite big1 ?simp // => j _; rewrite nth_nil !simp.
Qed.

Lemma coefXM p i : ('X * p)`_i = (if (i == 0)%N then 0 else p`_i.-1).
Proof. by rewrite -commr_polyX coefMX. Qed.

Lemma cons_poly_def p a : cons_poly a p = p * 'X + a%:P.
Proof.
apply/polyP=> i; rewrite coef_cons coefD coefMX coefC.
by case: ifP; rewrite !simp.
Qed.

Lemma poly_ind (K : {poly R} -> Type) :
  K 0 -> (forall p c, K p -> K (p * 'X + c%:P)) -> (forall p, K p).
Proof.
move=> K0 Kcons p; rewrite -[p]polyseqK.
by elim: {p}(p : seq R) => //= p c IHp; rewrite cons_poly_def; apply: Kcons.
Qed.

Lemma polyseqXaddC a : 'X + a%:P = [:: a; 1] :> seq R.
Proof. by rewrite -['X]mul1r -cons_poly_def polyseq_cons polyseq1. Qed.

Lemma polyseqXsubC a : 'X - a%:P = [:: - a; 1] :> seq R.
Proof. by rewrite -polyCN polyseqXaddC. Qed.

Lemma size_XsubC a : size ('X - a%:P) = 2.
Proof. by rewrite polyseqXsubC. Qed.

Lemma size_XaddC b : size ('X + b%:P) = 2.
Proof. by rewrite -[b]opprK rmorphN size_XsubC. Qed.

Lemma lead_coefXaddC a : lead_coef ('X + a%:P) = 1.
Proof. by rewrite lead_coefE polyseqXaddC. Qed.

Lemma lead_coefXsubC a : lead_coef ('X - a%:P) = 1.
Proof. by rewrite lead_coefE polyseqXsubC. Qed.

Lemma polyXsubC_eq0 a : ('X - a%:P == 0) = false.
Proof. by rewrite -nil_poly polyseqXsubC. Qed.

Lemma size_MXaddC p c :
  size (p * 'X + c%:P) = (if (p == 0) && (c == 0) then 0 else (size p).+1).
Proof. by rewrite -cons_poly_def size_cons_poly nil_poly. Qed.

Lemma polyseqMX p : p != 0 -> p * 'X = 0 :: p :> seq R.
Proof.
by move=> nz_p; rewrite -[p * _]addr0 -cons_poly_def polyseq_cons nil_poly nz_p.
Qed.

Lemma size_mulX p : p != 0 -> size (p * 'X) = (size p).+1.
Proof. by move/polyseqMX->. Qed.

Lemma lead_coefMX p : lead_coef (p * 'X) = lead_coef p.
Proof.
have [-> | nzp] := eqVneq p 0; first by rewrite mul0r.
by rewrite /lead_coef !nth_last polyseqMX.
Qed.

Lemma size_XmulC a : a != 0 -> size ('X * a%:P) = 2.
Proof.
by move=> nz_a; rewrite -commr_polyX size_mulX ?polyC_eq0 ?size_polyC nz_a.
Qed.

Local Notation "''X^' n" := ('X ^+ n).

Lemma coefXn n i : 'X^n`_i = (i == n)%:R.
Proof.
by elim: n i => [|n IHn] [|i]; rewrite ?coef1 // exprS coefXM ?IHn.
Qed.

Lemma polyseqXn n : 'X^n = rcons (nseq n 0) 1 :> seq R.
Proof.
elim: n => [|n IHn]; rewrite ?polyseq1 // exprSr.
by rewrite polyseqMX -?size_poly_eq0 IHn ?size_rcons.
Qed.

Lemma size_polyXn n : size 'X^n = n.+1.
Proof. by rewrite polyseqXn size_rcons size_nseq. Qed.

Lemma commr_polyXn p n : GRing.comm p 'X^n.
Proof. exact/commrX/commr_polyX. Qed.

Lemma lead_coefXn n : lead_coef 'X^n = 1.
Proof. by rewrite /lead_coef nth_last polyseqXn last_rcons. Qed.

Lemma lead_coefXnaddC n c : 0 < n -> lead_coef ('X^n + c%:P) = 1.
Proof.
move=> n_gt0; rewrite lead_coefDl ?lead_coefXn//.
by rewrite size_polyC size_polyXn ltnS (leq_trans (leq_b1 _)).
Qed.

Lemma lead_coefXnsubC n c : 0 < n -> lead_coef ('X^n - c%:P) = 1.
Proof. by move=> n_gt0; rewrite -polyCN lead_coefXnaddC. Qed.

Lemma size_XnaddC n c : 0 < n -> size ('X^n + c%:P) = n.+1.
Proof.
by move=> *; rewrite size_polyDl ?size_polyXn// size_polyC; case: eqP.
Qed.

Lemma size_XnsubC n c : 0 < n -> size ('X^n - c%:P) = n.+1.
Proof. by move=> *; rewrite -polyCN size_XnaddC. Qed.

Lemma polyseqMXn n p : p != 0 -> p * 'X^n = ncons n 0 p :> seq R.
Proof.
case: n => [|n] nz_p; first by rewrite mulr1.
elim: n => [|n IHn]; first exact: polyseqMX.
by rewrite exprSr mulrA polyseqMX -?nil_poly IHn.
Qed.

Lemma coefMXn n p i : (p * 'X^n)`_i = if i < n then 0 else p`_(i - n).
Proof.
have [-> | /polyseqMXn->] := eqVneq p 0; last exact: nth_ncons.
by rewrite mul0r !coef0 if_same.
Qed.

Lemma size_mulXn n p : p != 0 -> size (p * 'X^n) = (n + size p)%N.
Proof.
elim: n p => [p p_neq0| n IH p p_neq0]; first by rewrite mulr1.
by rewrite exprS mulrA IH -?size_poly_eq0 size_mulX // addnS.
Qed.

Lemma coefXnM n p i : ('X^n * p)`_i = if i < n then 0 else p`_(i - n).
Proof. by rewrite -commr_polyXn coefMXn. Qed.

Lemma coef_sumMXn I (r : seq I) (P : pred I) (p : I -> R) (n : I -> nat) k :
  (\sum_(i <- r | P i) p i *: 'X^(n i))`_k =
    \sum_(i <- r | P i && (n i == k)) p i.
Proof.
rewrite coef_sum big_mkcondr; apply: eq_bigr => i Pi.
by rewrite coefZ coefXn mulr_natr mulrb eq_sym.
Qed.

(* Expansion of a polynomial as an indexed sum *)
Lemma poly_def n E : \poly_(i < n) E i = \sum_(i < n) E i *: 'X^i.
Proof. by apply/polyP => i; rewrite coef_sumMXn coef_poly big_ord1_eq. Qed.

(* Monic predicate *)
Definition monic_pred := fun p => lead_coef p == 1.
Arguments monic_pred _ /.
Definition monic := [qualify p | monic_pred p].

Lemma monicE p : (p \is monic) = (lead_coef p == 1). Proof. by []. Qed.
Lemma monicP p : reflect (lead_coef p = 1) (p \is monic).
Proof. exact: eqP. Qed.

Lemma monic1 : 1 \is monic. Proof. exact/eqP/lead_coef1. Qed.
Lemma monicX : 'X \is monic. Proof. exact/eqP/lead_coefX. Qed.
Lemma monicXn n : 'X^n \is monic. Proof. exact/eqP/lead_coefXn. Qed.

Lemma monic_neq0 p : p \is monic -> p != 0.
Proof. by rewrite -lead_coef_eq0 => /eqP->; apply: oner_neq0. Qed.

Lemma lead_coef_monicM p q : p \is monic -> lead_coef (p * q) = lead_coef q.
Proof.
have [-> | nz_q] := eqVneq q 0; first by rewrite mulr0.
by move/monicP=> mon_p; rewrite lead_coef_proper_mul mon_p mul1r ?lead_coef_eq0.
Qed.

Lemma lead_coef_Mmonic p q : q \is monic -> lead_coef (p * q) = lead_coef p.
Proof.
have [-> | nz_p] := eqVneq p 0; first by rewrite mul0r.
by move/monicP=> mon_q; rewrite lead_coef_proper_mul mon_q mulr1 ?lead_coef_eq0.
Qed.

Lemma size_monicM p q :
  p \is monic -> q != 0 -> size (p * q) = (size p + size q).-1.
Proof.
move/monicP=> mon_p nz_q.
by rewrite size_proper_mul // mon_p mul1r lead_coef_eq0.
Qed.

Lemma size_Mmonic p q :
  p != 0 -> q \is monic -> size (p * q) = (size p + size q).-1.
Proof.
move=> nz_p /monicP mon_q.
by rewrite size_proper_mul // mon_q mulr1 lead_coef_eq0.
Qed.

Lemma monicMl p q : p \is monic -> (p * q \is monic) = (q \is monic).
Proof. by move=> mon_p; rewrite !monicE lead_coef_monicM. Qed.

Lemma monicMr p q : q \is monic -> (p * q \is monic) = (p \is monic).
Proof. by move=> mon_q; rewrite !monicE lead_coef_Mmonic. Qed.

Fact monic_mulr_closed : mulr_closed monic.
Proof. by split=> [|p q mon_p]; rewrite (monic1, monicMl). Qed.
HB.instance Definition _ := GRing.isMulClosed.Build {poly R} monic_pred
  monic_mulr_closed.

Lemma monic_exp p n : p \is monic -> p ^+ n \is monic.
Proof. exact: rpredX. Qed.

Lemma monic_prod I rI (P : pred I) (F : I -> {poly R}):
  (forall i, P i -> F i \is monic) -> \prod_(i <- rI | P i) F i \is monic.
Proof. exact: rpred_prod. Qed.

Lemma monicXaddC c : 'X + c%:P \is monic.
Proof. exact/eqP/lead_coefXaddC. Qed.

Lemma monicXsubC c : 'X - c%:P \is monic.
Proof. exact/eqP/lead_coefXsubC. Qed.

Lemma monic_prod_XsubC I rI (P : pred I) (F : I -> R) :
  \prod_(i <- rI | P i) ('X - (F i)%:P) \is monic.
Proof. by apply: monic_prod => i _; apply: monicXsubC. Qed.

Lemma lead_coef_prod_XsubC I rI (P : pred I) (F : I -> R) :
  lead_coef (\prod_(i <- rI | P i) ('X - (F i)%:P)) = 1.
Proof. exact/eqP/monic_prod_XsubC. Qed.

Lemma size_prod_XsubC I rI (F : I -> R) :
  size (\prod_(i <- rI) ('X - (F i)%:P)) = (size rI).+1.
Proof.
elim: rI => [|i r /= <-]; rewrite ?big_nil ?size_poly1 // big_cons.
rewrite size_monicM ?monicXsubC ?monic_neq0 ?monic_prod_XsubC //.
by rewrite size_XsubC.
Qed.

Lemma size_exp_XsubC n a : size (('X - a%:P) ^+ n) = n.+1.
Proof.
rewrite -[n]card_ord -prodr_const -big_filter size_prod_XsubC.
by have [e _ _ [_ ->]] := big_enumP.
Qed.

Lemma monicXnaddC n c : 0 < n -> 'X^n + c%:P \is monic.
Proof. by move=> n_gt0; rewrite monicE lead_coefXnaddC. Qed.

Lemma monicXnsubC n c : 0 < n -> 'X^n - c%:P \is monic.
Proof. by move=> n_gt0; rewrite monicE lead_coefXnsubC. Qed.

(* Some facts about regular elements. *)

Lemma lreg_lead p : GRing.lreg (lead_coef p) -> GRing.lreg p.
Proof.
move/mulrI_eq0=> reg_p; apply: mulrI0_lreg => q /eqP; apply: contraTeq => nz_q.
by rewrite -lead_coef_eq0 lead_coef_proper_mul reg_p lead_coef_eq0.
Qed.

Lemma rreg_lead p : GRing.rreg (lead_coef p) -> GRing.rreg p.
Proof.
move/mulIr_eq0=> reg_p; apply: mulIr0_rreg => q /eqP; apply: contraTeq => nz_q.
by rewrite -lead_coef_eq0 lead_coef_proper_mul reg_p lead_coef_eq0.
Qed.

Lemma lreg_lead0 p : GRing.lreg (lead_coef p) -> p != 0.
Proof. by move/lreg_neq0; rewrite lead_coef_eq0. Qed.

Lemma rreg_lead0 p : GRing.rreg (lead_coef p) -> p != 0.
Proof. by move/rreg_neq0; rewrite lead_coef_eq0. Qed.

Lemma lreg_size c p : GRing.lreg c -> size (c *: p) = size p.
Proof.
move=> reg_c; have [-> | nz_p] := eqVneq p 0; first by rewrite scaler0.
rewrite -mul_polyC size_proper_mul; first by rewrite size_polyC lreg_neq0.
by rewrite lead_coefC mulrI_eq0 ?lead_coef_eq0.
Qed.

Lemma lreg_polyZ_eq0 c p : GRing.lreg c -> (c *: p == 0) = (p == 0).
Proof. by rewrite -!size_poly_eq0 => /lreg_size->. Qed.

Lemma lead_coef_lreg c p :
  GRing.lreg c -> lead_coef (c *: p) = c * lead_coef p.
Proof. by move=> reg_c; rewrite !lead_coefE coefZ lreg_size. Qed.

Lemma rreg_size c p : GRing.rreg c -> size (p * c%:P) =  size p.
Proof.
move=> reg_c; have [-> | nz_p] := eqVneq p 0; first by rewrite mul0r.
rewrite size_proper_mul; first by rewrite size_polyC rreg_neq0 ?addn1.
by rewrite lead_coefC mulIr_eq0 ?lead_coef_eq0.
Qed.

Lemma rreg_polyMC_eq0 c p : GRing.rreg c -> (p * c%:P == 0) = (p == 0).
Proof. by rewrite -!size_poly_eq0 => /rreg_size->. Qed.

Lemma rreg_div0 q r d :
    GRing.rreg (lead_coef d) -> size r < size d ->
  (q * d + r == 0) = (q == 0) && (r == 0).
Proof.
move=> reg_d lt_r_d; rewrite addrC addr_eq0.
have [-> | nz_q] := eqVneq q 0; first by rewrite mul0r oppr0.
apply: contraTF lt_r_d => /eqP->; rewrite -leqNgt size_polyN.
rewrite size_proper_mul ?mulIr_eq0 ?lead_coef_eq0 //.
by rewrite (polySpred nz_q) leq_addl.
Qed.

Lemma monic_comreg p :
  p \is monic -> GRing.comm p (lead_coef p)%:P /\ GRing.rreg (lead_coef p).
Proof. by move/monicP->; split; [apply: commr1 | apply: rreg1]. Qed.

Lemma monic_lreg p : p \is monic -> GRing.lreg p.
Proof. by move=> /eqP lp1; apply/lreg_lead; rewrite lp1; apply/lreg1. Qed.

Lemma monic_rreg p : p \is monic -> GRing.rreg p.
Proof. by move=> /eqP lp1; apply/rreg_lead; rewrite lp1; apply/rreg1. Qed.

(* Horner evaluation of polynomials *)
Implicit Types s rs : seq R.
Fixpoint horner_rec s x := if s is a :: s' then horner_rec s' x * x + a else 0.
Definition horner p := horner_rec p.

Local Notation "p .[ x ]" := (horner p x) : ring_scope.

Lemma horner0 x : (0 : {poly R}).[x] = 0.
Proof. by rewrite /horner polyseq0. Qed.

Lemma hornerC c x : (c%:P).[x] = c.
Proof. by rewrite /horner polyseqC; case: eqP; rewrite /= ?simp. Qed.

Lemma hornerX x : 'X.[x] = x.
Proof. by rewrite /horner polyseqX /= !simp. Qed.

Lemma horner_cons p c x : (cons_poly c p).[x] = p.[x] * x + c.
Proof.
rewrite /horner polyseq_cons; case: nilP => //= ->.
by rewrite !simp -/(_.[x]) hornerC.
Qed.

Lemma horner_coef0 p : p.[0] = p`_0.
Proof. by rewrite /horner; case: (p : seq R) => //= c p'; rewrite !simp. Qed.

Lemma hornerMXaddC p c x : (p * 'X + c%:P).[x] = p.[x] * x + c.
Proof. by rewrite -cons_poly_def horner_cons. Qed.

Lemma hornerMX p x : (p * 'X).[x] = p.[x] * x.
Proof. by rewrite -[p * 'X]addr0 hornerMXaddC addr0. Qed.

Lemma horner_Poly s x : (Poly s).[x] = horner_rec s x.
Proof. by elim: s => [|a s /= <-]; rewrite (horner0, horner_cons). Qed.

Lemma horner_coef p x : p.[x] = \sum_(i < size p) p`_i * x ^+ i.
Proof.
rewrite /horner.
elim: {p}(p : seq R) => /= [|a s ->]; first by rewrite big_ord0.
rewrite big_ord_recl simp addrC big_distrl /=.
by congr (_ + _); apply: eq_bigr => i _; rewrite -mulrA exprSr.
Qed.

Lemma horner_coef_wide n p x :
  size p <= n -> p.[x] = \sum_(i < n) p`_i * x ^+ i.
Proof.
move=> le_p_n.
rewrite horner_coef (big_ord_widen n (fun i => p`_i * x ^+ i)) // big_mkcond.
by apply: eq_bigr => i _; case: ltnP => // le_p_i; rewrite nth_default ?simp.
Qed.

Lemma horner_poly n E x : (\poly_(i < n) E i).[x] = \sum_(i < n) E i * x ^+ i.
Proof.
rewrite (@horner_coef_wide n) ?size_poly //.
by apply: eq_bigr => i _; rewrite coef_poly ltn_ord.
Qed.

Lemma hornerN p x : (- p).[x] = - p.[x].
Proof.
rewrite -[-%R]/opp_poly unlock horner_poly horner_coef -sumrN /=.
by apply: eq_bigr => i _; rewrite mulNr.
Qed.

Lemma hornerD p q x : (p + q).[x] = p.[x] + q.[x].
Proof.
rewrite -[+%R]/(@add_poly R) unlock horner_poly; set m := maxn _ _.
rewrite !(@horner_coef_wide m) ?leq_max ?leqnn ?orbT // -big_split /=.
by apply: eq_bigr => i _; rewrite -mulrDl.
Qed.

Lemma hornerXsubC a x : ('X - a%:P).[x] = x - a.
Proof. by rewrite hornerD hornerN hornerC hornerX. Qed.

Lemma horner_sum I (r : seq I) (P : pred I) F x :
  (\sum_(i <- r | P i) F i).[x] = \sum_(i <- r | P i) (F i).[x].
Proof. by elim/big_rec2: _ => [|i _ p _ <-]; rewrite (horner0, hornerD). Qed.

Lemma hornerCM a p x : (a%:P * p).[x] = a * p.[x].
Proof.
elim/poly_ind: p => [|p c IHp]; first by rewrite !(mulr0, horner0).
by rewrite mulrDr mulrA -polyCM !hornerMXaddC IHp mulrDr mulrA.
Qed.

Lemma hornerZ c p x : (c *: p).[x] = c * p.[x].
Proof. by rewrite -mul_polyC hornerCM. Qed.

Lemma hornerMn n p x : (p *+ n).[x] = p.[x] *+ n.
Proof. by elim: n => [| n IHn]; rewrite ?horner0 // !mulrS hornerD IHn. Qed.

Definition comm_coef p x := forall i, p`_i * x = x * p`_i.

Definition comm_poly p x := x * p.[x] = p.[x] * x.

Lemma comm_coef_poly p x : comm_coef p x -> comm_poly p x.
Proof.
move=> cpx; rewrite /comm_poly !horner_coef big_distrl big_distrr /=.
by apply: eq_bigr => i _; rewrite /= mulrA -cpx -!mulrA commrX.
Qed.

Lemma comm_poly0 x : comm_poly 0 x.
Proof. by rewrite /comm_poly !horner0 !simp. Qed.

Lemma comm_poly1 x : comm_poly 1 x.
Proof. by rewrite /comm_poly !hornerC !simp. Qed.

Lemma comm_polyX x : comm_poly 'X x.
Proof. by rewrite /comm_poly !hornerX. Qed.

Lemma comm_polyD p q x: comm_poly p x -> comm_poly q x -> comm_poly (p + q) x.
Proof. by rewrite /comm_poly hornerD mulrDr mulrDl => -> ->. Qed.

Lemma commr_horner a b p : GRing.comm a b -> comm_coef p a -> GRing.comm a p.[b].
Proof.
move=> cab cpa; rewrite horner_coef; apply: commr_sum => i _.
by apply: commrM => //; apply: commrX.
Qed.

Lemma hornerM_comm p q x : comm_poly q x -> (p * q).[x] = p.[x] * q.[x].
Proof.
move=> comm_qx.
elim/poly_ind: p => [|p c IHp]; first by rewrite !(simp, horner0).
rewrite mulrDl hornerD hornerCM -mulrA -commr_polyX mulrA hornerMX.
by rewrite {}IHp -mulrA -comm_qx mulrA -mulrDl hornerMXaddC.
Qed.

Lemma comm_polyM p q x: comm_poly p x -> comm_poly q x -> comm_poly (p * q) x.
Proof.
by move=> px qx; rewrite /comm_poly hornerM_comm// mulrA px -mulrA qx mulrA.
Qed.

Lemma horner_exp_comm p x n : comm_poly p x -> (p ^+ n).[x] = p.[x] ^+ n.
Proof.
move=> comm_px; elim: n => [|n IHn]; first by rewrite hornerC.
by rewrite !exprSr -IHn hornerM_comm.
Qed.

Lemma comm_poly_exp p n x: comm_poly p x -> comm_poly (p ^+ n) x.
Proof. by move=> px; rewrite /comm_poly !horner_exp_comm// commrX. Qed.

Lemma hornerXn x n : ('X^n).[x] = x ^+ n.
Proof. by rewrite horner_exp_comm /comm_poly hornerX. Qed.

Definition hornerE_comm :=
  (hornerD, hornerN, hornerX, hornerC, horner_cons,
   simp, hornerCM, hornerZ,
   (fun p x => hornerM_comm p (comm_polyX x))).

Definition root p : pred R := fun x => p.[x] == 0.

Lemma mem_root p x : x \in root p = (p.[x] == 0).
Proof. by []. Qed.

Lemma rootE p x : (root p x = (p.[x] == 0)) * ((x \in root p) = (p.[x] == 0)).
Proof. by []. Qed.

Lemma rootP p x : reflect (p.[x] = 0) (root p x).
Proof. exact: eqP. Qed.

Lemma rootPt p x : reflect (p.[x] == 0) (root p x).
Proof. exact: idP. Qed.

Lemma rootPf p x : reflect ((p.[x] == 0) = false) (~~ root p x).
Proof. exact: negPf. Qed.

Lemma rootC a x : root a%:P x = (a == 0).
Proof. by rewrite rootE hornerC. Qed.

Lemma root0 x : root 0 x.
Proof. by rewrite rootC. Qed.

Lemma root1 x : ~~ root 1 x.
Proof. by rewrite rootC oner_eq0. Qed.

Lemma rootX x : root 'X x = (x == 0).
Proof. by rewrite rootE hornerX. Qed.

Lemma rootN p x : root (- p) x = root p x.
Proof. by rewrite rootE hornerN oppr_eq0. Qed.

Lemma root_size_gt1 a p : p != 0 -> root p a -> 1 < size p.
Proof.
rewrite ltnNge => nz_p; apply: contraL => /size1_polyC Dp.
by rewrite Dp rootC -polyC_eq0 -Dp.
Qed.

Lemma root_XsubC a x : root ('X - a%:P) x = (x == a).
Proof. by rewrite rootE hornerXsubC subr_eq0. Qed.

Lemma root_XaddC a x : root ('X + a%:P) x = (x == - a).
Proof. by rewrite -root_XsubC rmorphN opprK. Qed.

Theorem factor_theorem p a : reflect (exists q, p = q * ('X - a%:P)) (root p a).
Proof.
apply: (iffP eqP) => [pa0 | [q ->]]; last first.
  by rewrite hornerM_comm /comm_poly hornerXsubC subrr ?simp.
exists (\poly_(i < size p) horner_rec (drop i.+1 p) a).
apply/polyP=> i; rewrite mulrBr coefB coefMX coefMC !coef_poly.
apply: canRL (addrK _) _; rewrite addrC; have [le_p_i | lt_i_p] := leqP.
  rewrite nth_default // !simp drop_oversize ?if_same //.
  exact: leq_trans (leqSpred _).
case: i => [|i] in lt_i_p *; last by rewrite ltnW // (drop_nth 0 lt_i_p).
by rewrite drop1 /= -{}pa0 /horner; case: (p : seq R) lt_i_p.
Qed.

Lemma multiplicity_XsubC p a :
  {m | exists2 q, (p != 0) ==> ~~ root q a & p = q * ('X - a%:P) ^+ m}.
Proof.
have [n le_p_n] := ubnP (size p); elim: n => // n IHn in p le_p_n *.
have [-> | nz_p /=] := eqVneq p 0; first by exists 0, 0; rewrite ?mul0r.
have [/sig_eqW[p1 Dp] | nz_pa] := altP (factor_theorem p a); last first.
  by exists 0%N, p; rewrite ?mulr1.
have nz_p1: p1 != 0 by apply: contraNneq nz_p => p1_0; rewrite Dp p1_0 mul0r.
have /IHn[m /sig2_eqW[q nz_qa Dp1]]: size p1 < n.
  by rewrite Dp size_Mmonic ?monicXsubC // size_XsubC addn2 in le_p_n.
by exists m.+1, q; [rewrite nz_p1 in nz_qa | rewrite exprSr mulrA -Dp1].
Qed.

(* Roots of unity. *)

#[deprecated(since="mathcomp 2.3.0",note="Use size_XnsubC instead.")]
Lemma size_Xn_sub_1 n : n > 0 -> size ('X^n - 1 : {poly R}) = n.+1.
Proof. exact/size_XnsubC. Qed.

#[deprecated(since="mathcomp 2.3.0'",note="Use monicXnsubC instead.")]
Lemma monic_Xn_sub_1 n : n > 0 -> 'X^n - 1 \is monic.
Proof. exact/monicXnsubC. Qed.

Definition root_of_unity n : pred R := root ('X^n - 1).
Local Notation "n .-unity_root" := (root_of_unity n) : ring_scope.

Lemma unity_rootE n z : n.-unity_root z = (z ^+ n == 1).
Proof.
by rewrite /root_of_unity rootE hornerD hornerN hornerXn hornerC subr_eq0.
Qed.

Lemma unity_rootP n z : reflect (z ^+ n = 1) (n.-unity_root z).
Proof. by rewrite unity_rootE; apply: eqP. Qed.

Definition primitive_root_of_unity n z :=
  (n > 0) && [forall i : 'I_n, i.+1.-unity_root z == (i.+1 == n)].
Local Notation "n .-primitive_root" := (primitive_root_of_unity n) : ring_scope.

Lemma prim_order_exists n z :
  n > 0 -> z ^+ n = 1 -> {m | m.-primitive_root z & (m %| n)}.
Proof.
move=> n_gt0 zn1.
have: exists m, (m > 0) && (z ^+ m == 1) by exists n; rewrite n_gt0 /= zn1.
case/ex_minnP=> m /andP[m_gt0 /eqP zm1] m_min.
exists m.
  apply/andP; split=> //; apply/eqfunP=> [[i]] /=.
  rewrite leq_eqVlt unity_rootE.
  case: eqP => [-> _ | _]; first by rewrite zm1 eqxx.
  by apply: contraTF => zi1; rewrite -leqNgt m_min.
have: n %% m < m by rewrite ltn_mod.
apply: contraLR; rewrite -lt0n -leqNgt => nm_gt0; apply: m_min.
by rewrite nm_gt0 /= expr_mod ?zn1.
Qed.

Section OnePrimitive.

Variables (n : nat) (z : R).
Hypothesis prim_z : n.-primitive_root z.

Lemma prim_order_gt0 : n > 0. Proof. by case/andP: prim_z. Qed.
Let n_gt0 := prim_order_gt0.

Lemma prim_expr_order : z ^+ n = 1.
Proof.
case/andP: prim_z => _; rewrite -(prednK n_gt0) => /forallP/(_ ord_max).
by rewrite unity_rootE eqxx eqb_id => /eqP.
Qed.

Lemma prim_expr_mod i : z ^+ (i %% n) = z ^+ i.
Proof. exact: expr_mod prim_expr_order. Qed.

Lemma prim_order_dvd i : (n %| i) = (z ^+ i == 1).
Proof.
move: n_gt0; rewrite -prim_expr_mod /dvdn -(ltn_mod i).
case: {i}(i %% n)%N => [|i] lt_i; first by rewrite !eqxx.
case/andP: prim_z => _ /forallP/(_ (Ordinal (ltnW lt_i)))/eqP.
by rewrite unity_rootE eqn_leq andbC leqNgt lt_i.
Qed.

Lemma eq_prim_root_expr i j : (z ^+ i == z ^+ j) = (i == j %[mod n]).
Proof.
wlog le_ji: i j / j <= i.
  move=> IH; case: (leqP j i) => [|/ltnW] /IH //.
  by rewrite eq_sym (eq_sym (j %% n)%N).
rewrite -{1}(subnKC le_ji) exprD -prim_expr_mod eqn_mod_dvd //.
rewrite prim_order_dvd; apply/eqP/eqP=> [|->]; last by rewrite mulr1.
move/(congr1 ( *%R (z ^+ (n - j %% n)))); rewrite mulrA -exprD.
by rewrite subnK ?prim_expr_order ?mul1r // ltnW ?ltn_mod.
Qed.

Lemma exp_prim_root k : (n %/ gcdn k n).-primitive_root (z ^+ k).
Proof.
set d := gcdn k n; have d_gt0: (0 < d)%N by rewrite gcdn_gt0 orbC n_gt0.
have [d_dv_k d_dv_n]: (d %| k /\ d %| n)%N by rewrite dvdn_gcdl dvdn_gcdr.
set q := (n %/ d)%N; rewrite /q.-primitive_root ltn_divRL // n_gt0.
apply/forallP=> i; rewrite unity_rootE -exprM -prim_order_dvd.
rewrite -(divnK d_dv_n) -/q -(divnK d_dv_k) mulnAC dvdn_pmul2r //.
apply/eqP; apply/idP/idP=> [|/eqP->]; last by rewrite dvdn_mull.
rewrite Gauss_dvdr; first by rewrite eqn_leq ltn_ord; apply: dvdn_leq.
by rewrite /coprime gcdnC -(eqn_pmul2r d_gt0) mul1n muln_gcdl !divnK.
Qed.

Lemma dvdn_prim_root m : (m %| n)%N -> m.-primitive_root (z ^+ (n %/ m)).
Proof.
set k := (n %/ m)%N => m_dv_n; rewrite -{1}(mulKn m n_gt0) -divnA // -/k.
by rewrite -{1}(@gcdn_idPl k n _) ?exp_prim_root // -(divnK m_dv_n) dvdn_mulr.
Qed.

Lemma prim_root_eq0 : (z == 0) = (n == 0%N).
Proof.
rewrite gtn_eqF//; apply/eqP => z0; have /esym/eqP := prim_expr_order.
by rewrite z0 expr0n gtn_eqF//= oner_eq0.
Qed.

End OnePrimitive.

Lemma prim_root_exp_coprime n z k :
  n.-primitive_root z -> n.-primitive_root (z ^+ k) = coprime k n.
Proof.
move=> prim_z; have n_gt0 := prim_order_gt0 prim_z.
apply/idP/idP=> [prim_zk | co_k_n].
  set d := gcdn k n; have dv_d_n: (d %| n)%N := dvdn_gcdr _ _.
  rewrite /coprime -/d -(eqn_pmul2r n_gt0) mul1n -{2}(gcdnMl n d).
  rewrite -{2}(divnK dv_d_n) (mulnC _ d) -muln_gcdr (gcdn_idPr _) //.
  rewrite (prim_order_dvd prim_zk) -exprM -(prim_order_dvd prim_z).
  by rewrite muln_divCA_gcd dvdn_mulr.
have zkn_1: z ^+ k ^+ n = 1 by rewrite exprAC (prim_expr_order prim_z) expr1n.
have{zkn_1} [m prim_zk dv_m_n]:= prim_order_exists n_gt0 zkn_1.
suffices /eqP <-: m == n by [].
rewrite eqn_dvd dv_m_n -(@Gauss_dvdr n k m) 1?coprime_sym //=.
by rewrite (prim_order_dvd prim_z) exprM (prim_expr_order prim_zk).
Qed.

(* Lifting a ring predicate to polynomials. *)

Implicit Type S : {pred R}.

Definition polyOver_pred S := fun p : {poly R} => all (mem S) p.
Arguments polyOver_pred _ _ /.
Definition polyOver S := [qualify a p | polyOver_pred S p].

Lemma polyOverS (S1 S2 : {pred R}) :
  {subset S1 <= S2} -> {subset polyOver S1 <= polyOver S2}.
Proof.
by move=> sS12 p /(all_nthP 0)S1p; apply/(all_nthP 0)=> i /S1p; apply: sS12.
Qed.

Lemma polyOver0 S : 0 \is a polyOver S.
Proof. by rewrite qualifE /= polyseq0. Qed.

Lemma polyOver_poly S n E :
  (forall i, i < n -> E i \in S) -> \poly_(i < n) E i \is a polyOver S.
Proof.
move=> S_E; apply/(all_nthP 0)=> i lt_i_p /=; rewrite coef_poly.
by case: ifP => [/S_E// | /idP[]]; apply: leq_trans lt_i_p (size_poly n E).
Qed.

Section PolyOverAdd.

Variable S : addrClosed R.

Lemma polyOverP {p} : reflect (forall i, p`_i \in S) (p \in polyOver S).
Proof.
apply: (iffP (all_nthP 0)) => [Sp i | Sp i _]; last exact: Sp.
by have [/Sp // | /(nth_default 0)->] := ltnP i (size p); apply: rpred0.
Qed.

Lemma polyOverC c : (c%:P \in polyOver S) = (c \in S).
Proof.
by rewrite [LHS]qualifE /= polyseqC; case: eqP => [->|] /=; rewrite ?andbT ?rpred0.
Qed.

Fact polyOver_addr_closed : addr_closed (polyOver S).
Proof.
split=> [|p q Sp Sq]; first exact: polyOver0.
by apply/polyOverP=> i; rewrite coefD rpredD ?(polyOverP _).
Qed.
HB.instance Definition _ := GRing.isAddClosed.Build {poly R} (polyOver_pred S)
  polyOver_addr_closed.

End PolyOverAdd.

Section PolyOverSemiRing2.

Variable S : semiring2Closed R.

Lemma polyOver_mulr_2closed : GRing.mulr_2closed (polyOver S).
Proof.
move=> p q /polyOverP Sp /polyOverP Sq; apply/polyOverP=> i.
by rewrite coefM rpred_sum // => j _; rewrite rpredM.
Qed.
HB.instance Definition _ := GRing.isMul2Closed.Build {poly R} (polyOver_pred S)
  polyOver_mulr_2closed.

End PolyOverSemiRing2.

Fact polyOverNr (zmodS : zmodClosed R) : oppr_closed (polyOver zmodS).
Proof.
by move=> p /polyOverP Sp; apply/polyOverP=> i; rewrite coefN rpredN.
Qed.
HB.instance Definition _ (zmodS : zmodClosed R) :=
  GRing.isOppClosed.Build {poly R} (polyOver_pred zmodS) (@polyOverNr _).

Section PolyOverSemiring.

Variable S : semiringClosed R.

Fact polyOver_mul1_closed : 1 \in (polyOver S).
Proof. by rewrite polyOverC rpred1. Qed.
HB.instance Definition _ := GRing.isMul1Closed.Build {poly R} (polyOver_pred S)
  polyOver_mul1_closed.

Lemma polyOverZ : {in S & polyOver S, forall c p, c *: p \is a polyOver S}.
Proof.
by move=> c p Sc /polyOverP Sp; apply/polyOverP=> i; rewrite coefZ rpredM ?Sp.
Qed.

Lemma polyOverX : 'X \in polyOver S.
Proof. by rewrite qualifE /= polyseqX /= rpred0 rpred1. Qed.

Lemma polyOverXn n : 'X^n \in polyOver S.
Proof. by rewrite rpredX// polyOverX. Qed.

Lemma rpred_horner : {in polyOver S & S, forall p x, p.[x] \in S}.
Proof.
move=> p x /polyOverP Sp Sx; rewrite horner_coef rpred_sum // => i _.
by rewrite rpredM ?rpredX.
Qed.

End PolyOverSemiring.

Section PolyOverRing.

Variable S : subringClosed R.

HB.instance Definition _ := GRing.MulClosed.on (polyOver_pred S).

Lemma polyOverXaddC c : ('X + c%:P \in polyOver S) = (c \in S).
Proof. by rewrite rpredDl ?polyOverX ?polyOverC. Qed.

Lemma polyOverXnaddC n c : ('X^n + c%:P \is a polyOver S) = (c \in S).
Proof. by rewrite rpredDl ?polyOverXn// ?polyOverC. Qed.

Lemma polyOverXsubC c : ('X - c%:P \in polyOver S) = (c \in S).
Proof. by rewrite rpredBl ?polyOverX ?polyOverC. Qed.

Lemma polyOverXnsubC n c : ('X^n - c%:P \is a polyOver S) = (c \in S).
Proof. by rewrite rpredBl ?polyOverXn// ?polyOverC. Qed.

End PolyOverRing.

(* Single derivative. *)

Definition deriv p := \poly_(i < (size p).-1) (p`_i.+1 *+ i.+1).

Local Notation "a ^` ()" := (deriv a).

Lemma coef_deriv p i : p^`()`_i = p`_i.+1 *+ i.+1.
Proof.
rewrite coef_poly -subn1 ltn_subRL.
by case: leqP => // /(nth_default 0) ->; rewrite mul0rn.
Qed.

Lemma polyOver_deriv (ringS : semiringClosed R) :
  {in polyOver ringS, forall p, p^`() \is a polyOver ringS}.
Proof.
by move=> p /polyOverP Kp; apply/polyOverP=> i; rewrite coef_deriv rpredMn ?Kp.
Qed.

Lemma derivC c : c%:P^`() = 0.
Proof. by apply/polyP=> i; rewrite coef_deriv coef0 coefC mul0rn. Qed.

Lemma derivX : ('X)^`() = 1.
Proof. by apply/polyP=> [[|i]]; rewrite coef_deriv coef1 coefX ?mul0rn. Qed.

Lemma derivXn n : ('X^n)^`() = 'X^(n.-1) *+ n.
Proof.
case: n => [|n]; first exact: derivC.
apply/polyP=> i; rewrite coef_deriv coefMn !coefXn eqSS.
by case: eqP => [-> // | _]; rewrite !mul0rn.
Qed.

Fact deriv_is_linear : linear deriv.
Proof.
move=> k p q; apply/polyP=> i.
by rewrite !(coef_deriv, coefD, coefZ) mulrnDl mulrnAr.
Qed.
HB.instance Definition _ := GRing.isSemilinear.Build R {poly R} {poly R} _ deriv
  (GRing.semilinear_linear deriv_is_linear).

Lemma deriv0 : 0^`() = 0.
Proof. exact: linear0. Qed.

Lemma derivD : {morph deriv : p q / p + q}.
Proof. exact: linearD. Qed.

Lemma derivN : {morph deriv : p / - p}.
Proof. exact: linearN. Qed.

Lemma derivB : {morph deriv : p q / p - q}.
Proof. exact: linearB. Qed.

Lemma derivXsubC (a : R) : ('X - a%:P)^`() = 1.
Proof. by rewrite derivB derivX derivC subr0. Qed.

Lemma derivMn n p : (p *+ n)^`() = p^`() *+ n.
Proof. exact: linearMn. Qed.

Lemma derivMNn n p : (p *- n)^`() = p^`() *- n.
Proof. exact: linearMNn. Qed.

Lemma derivZ c p : (c *: p)^`() = c *: p^`().
Proof. exact: linearZ. Qed.

Lemma deriv_mulC c p : (c%:P * p)^`() = c%:P * p^`().
Proof. by rewrite !mul_polyC derivZ. Qed.

Lemma derivMXaddC p c : (p * 'X + c%:P)^`() = p + p^`() * 'X.
Proof.
apply/polyP=> i; rewrite raddfD /= derivC addr0 coefD !(coefMX, coef_deriv).
by case: i; rewrite ?addr0.
Qed.

Lemma derivM p q : (p * q)^`() = p^`() * q + p * q^`().
Proof.
elim/poly_ind: p => [|p b IHp]; first by rewrite !(mul0r, add0r, derivC).
rewrite mulrDl -mulrA -commr_polyX mulrA -[_ * 'X]addr0 raddfD /= !derivMXaddC.
by rewrite deriv_mulC IHp !mulrDl -!mulrA !commr_polyX !addrA.
Qed.

Definition derivE := Eval lazy beta delta [morphism_2 morphism_1] in
  (derivZ, deriv_mulC, derivC, derivX, derivMXaddC, derivXsubC, derivM, derivB,
   derivD, derivN, derivXn, derivM, derivMn).

(* Iterated derivative. *)
Definition derivn n p := iter n deriv p.

Local Notation "a ^` ( n )" := (derivn n a) : ring_scope.

Lemma derivn0 p : p^`(0) = p.
Proof. by []. Qed.

Lemma derivn1 p : p^`(1) = p^`().
Proof. by []. Qed.

Lemma derivnS p n : p^`(n.+1) = p^`(n)^`().
Proof. by []. Qed.

Lemma derivSn p n : p^`(n.+1) = p^`()^`(n).
Proof. exact: iterSr. Qed.

Lemma coef_derivn n p i : p^`(n)`_i = p`_(n + i) *+ (n + i) ^_ n.
Proof.
elim: n i => [|n IHn] i; first by rewrite ffactn0 mulr1n.
by rewrite derivnS coef_deriv IHn -mulrnA ffactnSr addSnnS addKn.
Qed.

Lemma polyOver_derivn (ringS : semiringClosed R) :
  {in polyOver ringS, forall p n, p^`(n) \is a polyOver ringS}.
Proof.
move=> p /polyOverP Kp /= n; apply/polyOverP=> i.
by rewrite coef_derivn rpredMn.
Qed.

Fact derivn_is_linear n : linear (derivn n).
Proof. by elim: n => // n IHn a p q; rewrite derivnS IHn linearP. Qed.
HB.instance Definition _ n :=
  GRing.isSemilinear.Build R {poly R} {poly R} _ (derivn n)
    (GRing.semilinear_linear (derivn_is_linear n)).

Lemma derivnC c n : c%:P^`(n) = if n == 0 then c%:P else 0.
Proof. by case: n => // n; rewrite derivSn derivC linear0. Qed.

Lemma derivnD n : {morph derivn n : p q / p + q}.
Proof. exact: linearD. Qed.

Lemma derivnB n : {morph derivn n : p q / p - q}.
Proof. exact: linearB. Qed.

Lemma derivnMn n m p : (p *+ m)^`(n) = p^`(n) *+ m.
Proof. exact: linearMn. Qed.

Lemma derivnMNn n m p : (p *- m)^`(n) = p^`(n) *- m.
Proof. exact: linearMNn. Qed.

Lemma derivnN n : {morph derivn n : p / - p}.
Proof. exact: linearN. Qed.

Lemma derivnZ n : scalable (derivn n).
Proof. exact: linearZZ. Qed.

Lemma derivnXn m n : ('X^m)^`(n) = 'X^(m - n) *+ m ^_ n.
Proof.
apply/polyP=>i; rewrite coef_derivn coefMn !coefXn.
case: (ltnP m n) => [lt_m_n | le_m_n].
  by rewrite eqn_leq leqNgt ltn_addr // mul0rn ffact_small.
by rewrite -{1 3}(subnKC le_m_n) eqn_add2l; case: eqP => [->|]; rewrite ?mul0rn.
Qed.

Lemma derivnMXaddC n p c :
  (p * 'X + c%:P)^`(n.+1) = p^`(n) *+ n.+1 + p^`(n.+1) * 'X.
Proof.
elim: n => [|n IHn]; first by rewrite derivn1 derivMXaddC.
rewrite derivnS IHn derivD derivM derivX mulr1 derivMn -!derivnS.
by rewrite addrA addrAC -mulrSr.
Qed.

Lemma derivn_poly0 p n : size p <= n -> p^`(n) = 0.
Proof.
move=> le_p_n; apply/polyP=> i; rewrite coef_derivn.
rewrite nth_default; first by rewrite mul0rn coef0.
exact/(leq_trans le_p_n)/leq_addr.
Qed.

Lemma lt_size_deriv (p : {poly R}) : p != 0 -> size p^`() < size p.
Proof. by move=> /polySpred->; apply: size_poly. Qed.

(* A normalising version of derivation to get the division by n! in Taylor *)

Definition nderivn n p := \poly_(i < size p - n) (p`_(n + i) *+ 'C(n + i, n)).

Local Notation "a ^`N ( n )" := (nderivn n a) : ring_scope.

Lemma coef_nderivn n p i : p^`N(n)`_i = p`_(n + i) *+  'C(n + i, n).
Proof.
rewrite coef_poly ltn_subRL; case: leqP => // le_p_ni.
by rewrite nth_default ?mul0rn.
Qed.

(* Here is the division by n! *)
Lemma nderivn_def n p : p^`(n) = p^`N(n) *+ n`!.
Proof.
by apply/polyP=> i; rewrite coefMn coef_nderivn coef_derivn -mulrnA bin_ffact.
Qed.

Lemma polyOver_nderivn (ringS : semiringClosed R) :
  {in polyOver ringS, forall p n, p^`N(n) \in polyOver ringS}.
Proof.
move=> p /polyOverP Sp /= n; apply/polyOverP=> i.
by rewrite coef_nderivn rpredMn.
Qed.

Lemma nderivn0 p : p^`N(0) = p.
Proof. by rewrite -[p^`N(0)](nderivn_def 0). Qed.

Lemma nderivn1 p : p^`N(1) = p^`().
Proof. by rewrite -[p^`N(1)](nderivn_def 1). Qed.

Lemma nderivnC c n : (c%:P)^`N(n) = if n == 0 then c%:P else 0.
Proof.
apply/polyP=> i; rewrite coef_nderivn.
by case: n => [|n]; rewrite ?bin0 // coef0 coefC mul0rn.
Qed.

Lemma nderivnXn m n : ('X^m)^`N(n) = 'X^(m - n) *+ 'C(m, n).
Proof.
apply/polyP=> i; rewrite coef_nderivn coefMn !coefXn.
have [lt_m_n | le_n_m] := ltnP m n.
  by rewrite eqn_leq leqNgt ltn_addr // mul0rn bin_small.
by rewrite -{1 3}(subnKC le_n_m) eqn_add2l; case: eqP => [->|]; rewrite ?mul0rn.
Qed.

Fact nderivn_is_linear n : linear (nderivn n).
Proof.
move=> k p q; apply/polyP=> i.
by rewrite !(coef_nderivn, coefD, coefZ) mulrnDl mulrnAr.
Qed.
HB.instance Definition _ n :=
  GRing.isSemilinear.Build R {poly R} {poly R} _ (nderivn n)
    (GRing.semilinear_linear (nderivn_is_linear n)).

Lemma nderivnD n : {morph nderivn n : p q / p + q}.
Proof. exact: linearD. Qed.

Lemma nderivnB n : {morph nderivn n : p q / p - q}.
Proof. exact: linearB. Qed.

Lemma nderivnMn n m p : (p *+ m)^`N(n) = p^`N(n) *+ m.
Proof. exact: linearMn. Qed.

Lemma nderivnMNn n m p : (p *- m)^`N(n) = p^`N(n) *- m.
Proof. exact: linearMNn. Qed.

Lemma nderivnN n : {morph nderivn n : p / - p}.
Proof. exact: linearN. Qed.

Lemma nderivnZ n : scalable (nderivn n).
Proof. exact: linearZZ. Qed.

Lemma nderivnMXaddC n p c :
  (p * 'X + c%:P)^`N(n.+1) = p^`N(n) + p^`N(n.+1) * 'X.
Proof.
apply/polyP=> i; rewrite coef_nderivn !coefD !coefMX coefC.
rewrite !addSn /= !coef_nderivn addr0 binS mulrnDr addrC; congr (_ + _).
by rewrite addSnnS; case: i; rewrite // addn0 bin_small.
Qed.

Lemma nderivn_poly0 p n : size p <= n -> p^`N(n) = 0.
Proof.
move=> le_p_n; apply/polyP=> i; rewrite coef_nderivn.
rewrite nth_default; first by rewrite mul0rn coef0.
exact/(leq_trans le_p_n)/leq_addr.
Qed.

Lemma nderiv_taylor p x h :
  GRing.comm x h -> p.[x + h] = \sum_(i < size p) p^`N(i).[x] * h ^+ i.
Proof.
move/commrX=> cxh; elim/poly_ind: p => [|p c IHp].
  by rewrite size_poly0 big_ord0 horner0.
rewrite hornerMXaddC size_MXaddC.
have [-> | nz_p] := eqVneq p 0.
  rewrite horner0 !simp; have [-> | _] := c =P 0; first by rewrite big_ord0.
  by rewrite size_poly0 big_ord_recl big_ord0 nderivn0 hornerC !simp.
rewrite big_ord_recl nderivn0 !simp hornerMXaddC addrAC; congr (_ + _).
rewrite mulrDr {}IHp !big_distrl polySpred //= big_ord_recl /= mulr1 -addrA.
rewrite nderivn0 /bump /(addn 1) /=; congr (_ + _).
rewrite !big_ord_recr /= nderivnMXaddC -mulrA -exprSr -polySpred // !addrA.
congr (_ + _); last by rewrite (nderivn_poly0 (leqnn _)) !simp.
rewrite addrC -big_split /=; apply: eq_bigr => i _.
by rewrite nderivnMXaddC !hornerE_comm /= mulrDl -!mulrA -exprSr cxh.
Qed.

Lemma nderiv_taylor_wide n p x h :
    GRing.comm x h -> size p <= n ->
  p.[x + h] = \sum_(i < n) p^`N(i).[x] * h ^+ i.
Proof.
move/nderiv_taylor=> -> le_p_n.
rewrite (big_ord_widen n (fun i => p^`N(i).[x] * h ^+ i)) // big_mkcond.
apply: eq_bigr => i _; case: leqP => // /nderivn_poly0->.
by rewrite horner0 simp.
Qed.

Lemma eq_poly n E1 E2 : (forall i, i < n -> E1 i = E2 i) ->
  poly n E1 = poly n E2 :> {poly R}.
Proof. by move=> E; rewrite !poly_def; apply: eq_bigr => i _; rewrite E. Qed.

End PolynomialTheory.
#[deprecated(since="mathcomp 2.4.0", note="renamed to `size_polyN`")]
Notation size_opp := size_polyN (only parsing).

#[deprecated(since="mathcomp 2.4.0", note="Use pchar_poly instead.")]
Notation char_poly := pchar_poly (only parsing).

Prenex Implicits polyC polyCK Poly polyseqK lead_coef root horner polyOver.
Arguments monic {R}.
Notation "\poly_ ( i < n ) E" := (poly n (fun i => E)) : ring_scope.
Notation "c %:P" := (polyC c) : ring_scope.
Notation "'X" := (polyX _) : ring_scope.
Notation "''X^' n" := ('X ^+ n) : ring_scope.
Notation "p .[ x ]" := (horner p x) : ring_scope.
Notation "n .-unity_root" := (root_of_unity n) : ring_scope.
Notation "n .-primitive_root" := (primitive_root_of_unity n) : ring_scope.
Notation "a ^` ()" := (deriv a) : ring_scope.
Notation "a ^` ( n )" := (derivn n a) : ring_scope.
Notation "a ^`N ( n )" := (nderivn n a) : ring_scope.

Arguments monic_pred _ _ /.
Arguments monicP {R p}.
Arguments rootP {R p x}.
Arguments rootPf {R p x}.
Arguments rootPt {R p x}.
Arguments unity_rootP {R n z}.
Arguments polyOver_pred _ _ _ /.
Arguments polyOverP {R S p}.
Arguments polyC_inj {R} [x1 x2] eq_x12P.
Arguments eq_poly {R n} [E1] E2 eq_E12.

Section IdomainPrimRoot.
Variables (R : idomainType) (n : nat) (z : R).
Hypothesis prim_z : n.-primitive_root z.
Import prime.
Let n_gt0 := prim_order_gt0 prim_z.

Lemma prim_root_pcharF p : (p %| n)%N -> p \in [pchar R] = false.
Proof.
move=> pn; apply: contraTF isT => pchar_p; have p_prime := pcharf_prime pchar_p.
have /dvdnP[[|k] n_eq_kp] := pn; first by rewrite n_eq_kp in (n_gt0).
have /eqP := prim_expr_order prim_z; rewrite n_eq_kp exprM.
rewrite -pFrobenius_autE -(pFrobenius_aut1 pchar_p) -subr_eq0 -rmorphB/=.
rewrite pFrobenius_autE expf_eq0// prime_gt0//= subr_eq0 => /eqP.
move=> /eqP; rewrite -(prim_order_dvd prim_z) n_eq_kp.
rewrite -[X in _ %| X]muln1 dvdn_pmul2l ?dvdn1// => /eqP peq1.
by rewrite peq1 in p_prime.
Qed.

Lemma pchar_prim_root : [pchar R]^'.-nat n.
Proof. by apply/pnatP=> // p pp pn; rewrite inE/= prim_root_pcharF. Qed.

Lemma prim_root_pi_eq0 m : \pi(n).-nat m -> m%:R != 0 :> R.
Proof.
by rewrite natf_neq0_pchar; apply: sub_in_pnat => p _; apply: pnatPpi pchar_prim_root.
Qed.

Lemma prim_root_dvd_eq0 m : (m %| n)%N -> m%:R != 0 :> R.
Proof.
case: m => [|m mn]; first by rewrite dvd0n gtn_eqF.
by rewrite prim_root_pi_eq0 ?(sub_in_pnat (in1W (pi_of_dvd mn _))) ?pnat_pi.
Qed.

Lemma prim_root_natf_neq0 : n%:R != 0 :> R.
Proof. by rewrite prim_root_dvd_eq0. Qed.

End IdomainPrimRoot.

#[deprecated(since="mathcomp 2.4.0", note="Use prim_root_pcharF instead.")]
Notation prim_root_charF := prim_root_pcharF (only parsing).
#[deprecated(since="mathcomp 2.4.0", note="Use pchar_prim_root instead.")]
Notation char_prim_root := pchar_prim_root (only parsing).

(* Container morphism. *)
Section MapPoly.

Section Definitions.

Variables (aR rR : nzRingType) (f : aR -> rR).

Definition map_poly (p : {poly aR}) := \poly_(i < size p) f p`_i.

(* Alternative definition; the one above is more convenient because it lets *)
(* us use the lemmas on \poly, e.g., size (map_poly p) <= size p is an      *)
(* instance of size_poly.                                                   *)
Lemma map_polyE p : map_poly p = Poly (map f p).
Proof.
rewrite /map_poly unlock; congr Poly.
apply: (@eq_from_nth _ 0); rewrite size_mkseq ?size_map // => i lt_i_p.
by rewrite [RHS](nth_map 0) ?nth_mkseq.
Qed.

Definition commr_rmorph u := forall x, GRing.comm u (f x).

Definition horner_morph u of commr_rmorph u := fun p => (map_poly p).[u].

End Definitions.

Variables aR rR : nzRingType.

Section Combinatorial.

Variables (iR : nzRingType) (f : aR -> rR).
Local Notation "p ^f" := (map_poly f p) : ring_scope.

Lemma map_poly0 : 0^f = 0.
Proof. by rewrite map_polyE polyseq0. Qed.

Lemma eq_map_poly (g : aR -> rR) : f =1 g -> map_poly f =1 map_poly g.
Proof. by move=> eq_fg p; rewrite !map_polyE (eq_map eq_fg). Qed.

Lemma map_poly_id g (p : {poly iR}) :
  {in (p : seq iR), g =1 id} -> map_poly g p = p.
Proof. by move=> g_id; rewrite map_polyE map_id_in ?polyseqK. Qed.

Lemma coef_map_id0 p i : f 0 = 0 -> (p^f)`_i = f p`_i.
Proof.
by move=> f0; rewrite coef_poly; case: ltnP => // le_p_i; rewrite nth_default.
Qed.

Lemma map_Poly_id0 s : f 0 = 0 -> (Poly s)^f = Poly (map f s).
Proof.
move=> f0; apply/polyP=> j; rewrite coef_map_id0 ?coef_Poly //.
have [/(nth_map 0 0)->// | le_s_j] := ltnP j (size s).
by rewrite !nth_default ?size_map.
Qed.

Lemma map_poly_comp_id0 (g : iR -> aR) p :
  f 0 = 0 -> map_poly (f \o g) p = (map_poly g p)^f.
Proof. by move=> f0; rewrite map_polyE map_comp -map_Poly_id0 -?map_polyE. Qed.

Lemma size_map_poly_id0 p : f (lead_coef p) != 0 -> size p^f = size p.
Proof. by move=> nz_fp; apply: size_poly_eq. Qed.

Lemma map_poly_eq0_id0 p : f (lead_coef p) != 0 -> (p^f == 0) = (p == 0).
Proof. by rewrite -!size_poly_eq0 => /size_map_poly_id0->. Qed.

Lemma lead_coef_map_id0 p :
  f 0 = 0 -> f (lead_coef p) != 0 -> lead_coef p^f = f (lead_coef p).
Proof.
by move=> f0 nz_fp; rewrite lead_coefE coef_map_id0 ?size_map_poly_id0.
Qed.

Hypotheses (inj_f : injective f) (f_0 : f 0 = 0).

Lemma size_map_inj_poly p : size p^f = size p.
Proof.
have [-> | nz_p] := eqVneq p 0; first by rewrite map_poly0 !size_poly0.
by rewrite size_map_poly_id0 // -f_0 (inj_eq inj_f) lead_coef_eq0.
Qed.

Lemma map_inj_poly : injective (map_poly f).
Proof.
move=> p q /polyP eq_pq; apply/polyP=> i; apply: inj_f.
by rewrite -!coef_map_id0 ?eq_pq.
Qed.

Lemma lead_coef_map_inj p : lead_coef p^f = f (lead_coef p).
Proof. by rewrite !lead_coefE size_map_inj_poly coef_map_id0. Qed.

End Combinatorial.

Lemma map_polyK (f : aR -> rR) g :
  cancel g f -> f 0 = 0 -> cancel (map_poly g) (map_poly f).
Proof.
by move=> gK f_0 p; rewrite /= -map_poly_comp_id0 ?map_poly_id // => x _ //=.
Qed.

Lemma eq_in_map_poly_id0 (f g : aR -> rR) (S : addrClosed aR) :
    f 0 = 0 -> g 0 = 0 -> {in S, f =1 g} ->
  {in polyOver S, map_poly f =1 map_poly g}.
Proof.
move=> f0 g0 eq_fg p pP; apply/polyP => i.
by rewrite !coef_map_id0// eq_fg// (polyOverP _).
Qed.

Lemma eq_in_map_poly (f g : {additive aR -> rR}) (S : addrClosed aR) :
  {in S, f =1 g} -> {in polyOver S, map_poly f =1 map_poly g}.
Proof. by move=> /eq_in_map_poly_id0; apply; rewrite //?raddf0. Qed.

Section Additive.

Variables (iR : nzRingType) (f : {additive aR -> rR}).

Local Notation "p ^f" := (map_poly (GRing.Additive.sort f) p) : ring_scope.

Lemma coef_map p i : p^f`_i = f p`_i.
Proof. exact: coef_map_id0 (raddf0 f). Qed.

Lemma map_Poly s : (Poly s)^f = Poly (map f s).
Proof. exact: map_Poly_id0 (raddf0 f). Qed.

Lemma map_poly_comp (g : iR -> aR) p :
  map_poly (f \o g) p = map_poly f (map_poly g p).
Proof. exact: map_poly_comp_id0 (raddf0 f). Qed.

Fact map_poly_is_zmod_morphism : zmod_morphism (map_poly f).
Proof. by move=> p q; apply/polyP=> i; rewrite !(coef_map, coefB) raddfB. Qed.
#[deprecated(since="mathcomp 2.5.0",
      note="use `map_poly_is_zmod_morphism` instead")]
Definition map_poly_is_additive := map_poly_is_zmod_morphism.
HB.instance Definition _ :=
  GRing.isZmodMorphism.Build {poly aR} {poly rR} (map_poly f)
    map_poly_is_zmod_morphism.

Lemma map_polyC a : (a%:P)^f = (f a)%:P.
Proof. by apply/polyP=> i; rewrite !(coef_map, coefC) -!mulrb raddfMn. Qed.

Lemma lead_coef_map_eq p :
  f (lead_coef p) != 0 -> lead_coef p^f = f (lead_coef p).
Proof. exact: lead_coef_map_id0 (raddf0 f). Qed.

End Additive.

Variable f : {rmorphism aR -> rR}.
Implicit Types p : {poly aR}.

Local Notation "p ^f" := (map_poly (GRing.RMorphism.sort f) p) : ring_scope.

Fact map_poly_is_monoid_morphism : monoid_morphism (map_poly f).
Proof.
split=> [|p q]; apply/polyP=> i.
  by rewrite !(coef_map, coef1) /= rmorph_nat.
rewrite coef_map /= !coefM /= !rmorph_sum; apply: eq_bigr => j _.
by rewrite !coef_map rmorphM.
Qed.
#[deprecated(since="mathcomp 2.5.0",
      note="use `map_poly_is_monoid_morphism` instead")]
Definition map_poly_is_multiplicative :=
  (fun g => (g.2, g.1)) map_poly_is_monoid_morphism.
HB.instance Definition _ :=
  GRing.isMonoidMorphism.Build {poly aR} {poly rR} (map_poly f)
    map_poly_is_monoid_morphism.

Lemma map_polyZ c p : (c *: p)^f = f c *: p^f.
Proof. by apply/polyP=> i; rewrite !(coef_map, coefZ) /= rmorphM. Qed.
HB.instance Definition _ :=
  GRing.isScalable.Build aR {poly aR} {poly rR} (f \; *:%R) (map_poly f)
    map_polyZ.

Lemma map_polyX : ('X)^f = 'X.
Proof. by apply/polyP=> i; rewrite coef_map !coefX /= rmorph_nat. Qed.

Lemma map_polyXn n : ('X^n)^f = 'X^n.
Proof. by rewrite rmorphXn /= map_polyX. Qed.

Lemma map_polyXaddC x :  ('X + x%:P)^f = 'X + (f x)%:P.
Proof. by rewrite raddfD/= map_polyX map_polyC. Qed.

Lemma map_polyXsubC x : ('X - x%:P)^f = 'X - (f x)%:P.
Proof. by rewrite raddfB/= map_polyX map_polyC. Qed.

Lemma map_prod_XsubC I (rI : seq I) P F :
  (\prod_(i <- rI | P i) ('X - (F i)%:P))^f =
    \prod_(i <- rI | P i) ('X - (f (F i))%:P).
Proof.
by rewrite rmorph_prod//; apply/eq_bigr => x /=; rewrite map_polyXsubC.
Qed.

Lemma prod_map_poly (ar : seq aR) P :
  \prod_(x <- map f ar | P x) ('X - x%:P) =
    (\prod_(x <- ar | P (f x)) ('X - x%:P))^f.
Proof. by rewrite big_map map_prod_XsubC. Qed.

Lemma monic_map p : p \is monic -> p^f \is monic.
Proof.
move/monicP=> mon_p; rewrite monicE.
by rewrite lead_coef_map_eq mon_p /= rmorph1 ?oner_neq0.
Qed.

Lemma horner_map p x : p^f.[f x] = f p.[x].
Proof.
elim/poly_ind: p => [|p c IHp]; first by rewrite !(rmorph0, horner0).
rewrite hornerMXaddC !rmorphD !rmorphM /=.
by rewrite map_polyX map_polyC hornerMXaddC IHp.
Qed.

Lemma map_comm_poly p x : comm_poly p x -> comm_poly p^f (f x).
Proof. by rewrite /comm_poly horner_map -!rmorphM // => ->. Qed.

Lemma map_comm_coef p x : comm_coef p x -> comm_coef p^f (f x).
Proof. by move=> cpx i; rewrite coef_map -!rmorphM ?cpx. Qed.

Lemma rmorph_root p x : root p x -> root p^f (f x).
Proof. by move/eqP=> px0; rewrite rootE horner_map px0 rmorph0. Qed.

Lemma rmorph_unity_root n z : n.-unity_root z -> n.-unity_root (f z).
Proof.
move/rmorph_root; rewrite rootE rmorphB hornerD hornerN.
by rewrite /= map_polyXn rmorph1 hornerC hornerXn subr_eq0 unity_rootE.
Qed.

Section HornerMorph.

Variable u : rR.
Hypothesis cfu : commr_rmorph f u.

Lemma horner_morphC a : horner_morph cfu a%:P = f a.
Proof. by rewrite /horner_morph map_polyC hornerC. Qed.

Lemma horner_morphX : horner_morph cfu 'X = u.
Proof. by rewrite /horner_morph map_polyX hornerX. Qed.

Fact horner_is_linear : linear_for (f \; *%R) (horner_morph cfu).
Proof. by move=> c p q; rewrite /horner_morph linearP /= hornerD hornerZ. Qed.

Fact horner_is_monoid_morphism : monoid_morphism (horner_morph cfu).
Proof.
split=> [|p q]; first by rewrite /horner_morph rmorph1 hornerC.
rewrite /horner_morph rmorphM /= hornerM_comm //.
by apply: comm_coef_poly => i; rewrite coef_map cfu.
Qed.
#[deprecated(since="mathcomp 2.5.0",
      note="use `horner_is_monoid_morphism` instead")]
Definition horner_is_multiplicative :=
  (fun g => (g.2, g.1)) horner_is_monoid_morphism.
HB.instance Definition _ :=
  GRing.isSemilinear.Build aR {poly aR} rR _ (horner_morph cfu)
    (GRing.semilinear_linear horner_is_linear).

HB.instance Definition _ :=
  GRing.isMonoidMorphism.Build {poly aR} rR (horner_morph cfu)
    horner_is_monoid_morphism.

End HornerMorph.

Lemma deriv_map p : p^f^`() = (p^`())^f.
Proof. by apply/polyP => i; rewrite !(coef_map, coef_deriv) //= rmorphMn. Qed.

Lemma derivn_map p n : p^f^`(n) = (p^`(n))^f.
Proof. by apply/polyP => i; rewrite !(coef_map, coef_derivn) //= rmorphMn. Qed.

Lemma nderivn_map p n : p^f^`N(n) = (p^`N(n))^f.
Proof. by apply/polyP => i; rewrite !(coef_map, coef_nderivn) //= rmorphMn. Qed.

End MapPoly.

Lemma mapf_root (F : fieldType) (R : nzRingType) (f : {rmorphism F -> R})
  (p : {poly F}) (x : F) : root (map_poly f p) (f x) = root p x.
Proof. by rewrite !rootE horner_map fmorph_eq0. Qed.

(* Morphisms from the polynomial ring, and the initiality of polynomials  *)
(* with respect to these.                                                 *)
Section MorphPoly.

Variable (aR rR : nzRingType) (pf : {rmorphism {poly aR} -> rR}).

Lemma poly_morphX_comm : commr_rmorph (pf \o polyC) (pf 'X).
Proof. by move=> a; rewrite /GRing.comm /= -!rmorphM // commr_polyX. Qed.

Lemma poly_initial : pf =1 horner_morph poly_morphX_comm.
Proof.
apply: poly_ind => [|p a IHp]; first by rewrite !rmorph0.
by rewrite !rmorphD !rmorphM /= -{}IHp horner_morphC ?horner_morphX.
Qed.

End MorphPoly.

Notation "p ^:P" := (map_poly polyC p) : ring_scope.

Section PolyCompose.

Variable R : nzRingType.
Implicit Types p q : {poly R}.

Definition comp_poly q p := p^:P.[q].

Local Notation "p \Po q" := (comp_poly q p) : ring_scope.

Lemma size_map_polyC p : size p^:P = size p.
Proof. exact/(size_map_inj_poly polyC_inj). Qed.

Lemma map_polyC_eq0 p : (p^:P == 0) = (p == 0).
Proof. by rewrite -!size_poly_eq0 size_map_polyC. Qed.

Lemma root_polyC p x : root p^:P x%:P = root p x.
Proof. by rewrite rootE horner_map polyC_eq0. Qed.

Lemma comp_polyE p q : p \Po q = \sum_(i < size p) p`_i *: q^+i.
Proof.
by rewrite [p \Po q]horner_poly; apply: eq_bigr => i _; rewrite mul_polyC.
Qed.

Lemma coef_comp_poly p q n :
  (p \Po q)`_n = \sum_(i < size p) p`_i * (q ^+ i)`_n.
Proof. by rewrite comp_polyE coef_sum; apply: eq_bigr => i; rewrite coefZ. Qed.

Lemma polyOver_comp (ringS : semiringClosed R) :
  {in polyOver ringS &, forall p q, p \Po q \in polyOver ringS}.
Proof.
move=> p q /polyOverP Sp Sq; rewrite comp_polyE rpred_sum // => i _.
by rewrite polyOverZ ?rpredX.
Qed.

Lemma comp_polyCr p c : p \Po c%:P = p.[c]%:P.
Proof. exact: horner_map. Qed.

Lemma comp_poly0r p : p \Po 0 = (p`_0)%:P.
Proof. by rewrite comp_polyCr horner_coef0. Qed.

Lemma comp_polyC c p : c%:P \Po p = c%:P.
Proof. by rewrite /(_ \Po p) map_polyC hornerC. Qed.

Fact comp_poly_is_linear p : linear (comp_poly p).
Proof.
move=> a q r.
by rewrite /comp_poly rmorphD /= map_polyZ !hornerE_comm mul_polyC.
Qed.
HB.instance Definition _ p :=
  GRing.isSemilinear.Build R {poly R} {poly R} _ (comp_poly p)
    (GRing.semilinear_linear (comp_poly_is_linear p)).

Lemma comp_poly0 p : 0 \Po p = 0.
Proof. exact: raddf0. Qed.

Lemma comp_polyD p q r : (p + q) \Po r = (p \Po r) + (q \Po r).
Proof. exact: raddfD. Qed.

Lemma comp_polyB p q r : (p - q) \Po r = (p \Po r) - (q \Po r).
Proof. exact: raddfB. Qed.

Lemma comp_polyZ c p q : (c *: p) \Po q = c *: (p \Po q).
Proof. exact: linearZZ. Qed.

Lemma comp_polyXr p : p \Po 'X = p.
Proof. by rewrite -{2}/(idfun p) poly_initial. Qed.

Lemma comp_polyX p : 'X \Po p = p.
Proof. by rewrite /(_ \Po p) map_polyX hornerX. Qed.

Lemma comp_poly_MXaddC c p q : (p * 'X + c%:P) \Po q = (p \Po q) * q + c%:P.
Proof.
by rewrite /(_ \Po q) rmorphD rmorphM /= map_polyX map_polyC hornerMXaddC.
Qed.

Lemma comp_polyXaddC_K p z : (p \Po ('X + z%:P)) \Po ('X - z%:P) = p.
Proof.
have addzK: ('X + z%:P) \Po ('X - z%:P) = 'X.
  by rewrite raddfD /= comp_polyC comp_polyX subrK.
elim/poly_ind: p => [|p c IHp]; first by rewrite !comp_poly0.
rewrite comp_poly_MXaddC linearD /= comp_polyC {1}/comp_poly rmorphM /=.
by rewrite hornerM_comm /comm_poly -!/(_ \Po _) ?IHp ?addzK ?commr_polyX.
Qed.

Lemma size_comp_poly_leq p q :
  size (p \Po q) <= ((size p).-1 * (size q).-1).+1.
Proof.
rewrite comp_polyE (leq_trans (size_sum _ _ _)) //; apply/bigmax_leqP => i _.
rewrite (leq_trans (size_scale_leq _ _))//.
rewrite (leq_trans (size_poly_exp_leq _ _))//.
by rewrite ltnS mulnC leq_mul // -{2}(subnKC (valP i)) leq_addr.
Qed.

Lemma comp_Xn_poly p n : 'X^n \Po p = p ^+ n.
Proof. by rewrite /(_ \Po p) map_polyXn hornerXn. Qed.

Lemma coef_comp_poly_Xn p n i : 0 < n ->
  (p \Po 'X^n)`_i = if n %| i then p`_(i %/ n) else 0.
Proof.
move=> n_gt0; rewrite comp_polyE; under eq_bigr do rewrite -exprM mulnC.
rewrite coef_sumMXn/=; case: dvdnP => [[j ->]|nD]; last first.
   by rewrite big1// => j /eqP ?; case: nD; exists j.
under eq_bigl do rewrite eqn_mul2r gtn_eqF//.
by rewrite big_ord1_eq if_nth ?leqVgt ?mulnK.
Qed.

Lemma comp_poly_Xn p n : 0 < n ->
  p \Po 'X^n = \poly_(i < size p * n) if n %| i then p`_(i %/ n) else 0.
Proof.
move=> n_gt0; apply/polyP => i; rewrite coef_comp_poly_Xn // coef_poly.
case: dvdnP => [[k ->]|]; last by rewrite if_same.
by rewrite mulnK // ltn_mul2r n_gt0 if_nth ?leqVgt.
Qed.

End PolyCompose.

Notation "p \Po q" := (comp_poly q p) : ring_scope.

Lemma map_comp_poly (aR rR : nzRingType) (f : {rmorphism aR -> rR}) p q :
  map_poly f (p \Po q) = map_poly f p \Po map_poly f q.
Proof.
elim/poly_ind: p => [|p a IHp]; first by rewrite !raddf0.
rewrite comp_poly_MXaddC !rmorphD !rmorphM /= !map_polyC map_polyX.
by rewrite comp_poly_MXaddC -IHp.
Qed.

Section Surgery.

Variable R : nzRingType.

Implicit Type p q : {poly R}.

(* Even part of a polynomial                                                  *)

Definition even_poly p : {poly R} := \poly_(i < uphalf (size p)) p`_i.*2.

Lemma size_even_poly p : size (even_poly p) <= uphalf (size p).
Proof. exact: size_poly. Qed.

Lemma coef_even_poly p i : (even_poly p)`_i = p`_i.*2.
Proof. by rewrite coef_poly gtn_uphalf_double if_nth ?leqVgt. Qed.

Lemma even_polyE s p : size p <= s.*2 -> even_poly p = \poly_(i < s) p`_i.*2.
Proof.
move=> pLs2; apply/polyP => i; rewrite coef_even_poly !coef_poly if_nth //.
by case: ltnP => //= ?; rewrite (leq_trans pLs2) ?leq_double.
Qed.

Lemma size_even_poly_eq p : odd (size p) ->
  size (even_poly p) = uphalf (size p).
Proof.
move=> p_even; rewrite size_poly_eq// double_pred odd_uphalfK//=.
by rewrite lead_coef_eq0 -size_poly_eq0; case: size p_even.
Qed.

Lemma even_polyD p q : even_poly (p + q) = even_poly p + even_poly q.
Proof. by apply/polyP => i; rewrite !(coef_even_poly, coefD). Qed.

Lemma even_polyZ k p : even_poly (k *: p) = k *: even_poly p.
Proof. by apply/polyP => i; rewrite !(coefZ, coef_even_poly). Qed.

Fact even_poly_is_linear : linear even_poly.
Proof. by move=> k p q; rewrite even_polyD even_polyZ. Qed.

HB.instance Definition _ :=
  GRing.isSemilinear.Build R {poly R} {poly R} _ even_poly
    (GRing.semilinear_linear even_poly_is_linear).

Lemma even_polyC (c : R) : even_poly c%:P = c%:P.
Proof. by apply/polyP => i; rewrite coef_even_poly !coefC; case: i. Qed.

(* Odd part of a polynomial                                                   *)

Definition odd_poly p : {poly R} := \poly_(i < (size p)./2) p`_i.*2.+1.

Lemma size_odd_poly p : size (odd_poly p) <= (size p)./2.
Proof. exact: size_poly. Qed.

Lemma coef_odd_poly p i : (odd_poly p)`_i = p`_i.*2.+1.
Proof. by rewrite coef_poly gtn_half_double if_nth ?leqVgt. Qed.

Lemma odd_polyE s p :
  size p <= s.*2.+1 -> odd_poly p = \poly_(i < s) p`_i.*2.+1.
Proof.
move=> pLs2; apply/polyP => i; rewrite coef_odd_poly !coef_poly if_nth //.
by case: ltnP => //= ?; rewrite (leq_trans pLs2) ?ltnS ?leq_double.
Qed.

Lemma odd_polyC (c : R) : odd_poly c%:P = 0.
Proof. by apply/polyP => i; rewrite coef_odd_poly !coefC; case: i. Qed.

Lemma odd_polyD p q : odd_poly (p + q) = odd_poly p + odd_poly q.
Proof. by apply/polyP => i; rewrite !(coef_odd_poly, coefD). Qed.

Lemma odd_polyZ k p : odd_poly (k *: p) = k *: odd_poly p.
Proof. by apply/polyP => i; rewrite !(coefZ, coef_odd_poly). Qed.

Fact odd_poly_is_linear : linear odd_poly.
Proof. by move=> k p q; rewrite odd_polyD odd_polyZ. Qed.

HB.instance Definition _ :=
  GRing.isSemilinear.Build R {poly R} {poly R} _ odd_poly
    (GRing.semilinear_linear odd_poly_is_linear).

Lemma size_odd_poly_eq p : ~~ odd (size p) -> size (odd_poly p) = (size p)./2.
Proof.
have [->|p_neq0] := eqVneq p 0; first by rewrite odd_polyC size_poly0.
move=> p_odd; rewrite size_poly_eq// -subn1 doubleB subn2 even_halfK//.
rewrite prednK ?lead_coef_eq0// ltn_predRL.
by move: p_neq0 p_odd; rewrite -size_poly_eq0; case: (size p) => [|[]].
Qed.

Lemma odd_polyMX p : odd_poly (p * 'X) = even_poly p.
Proof.
have [->|pN0] := eqVneq p 0; first by rewrite mul0r even_polyC odd_polyC.
by apply/polyP => i; rewrite !coef_poly size_mulX // coefMX.
Qed.

Lemma even_polyMX p : even_poly (p * 'X) = odd_poly p * 'X.
Proof.
have [->|pN0] := eqVneq p 0; first by rewrite mul0r even_polyC odd_polyC mul0r.
by apply/polyP => -[|i]; rewrite !(coefMX, coef_poly, if_same, size_mulX).
Qed.

Lemma sum_even_poly p :
  \sum_(i < size p | ~~ odd i) p`_i *: 'X^i = even_poly p \Po 'X^2.
Proof.
apply/polyP => i; rewrite coef_comp_poly_Xn// coef_sumMXn coef_even_poly.
rewrite (big_ord1_cond_eq _ _ (negb \o _))/= -dvdn2 andbC -muln2.
by case: dvdnP => //= -[k ->]; rewrite mulnK// if_nth ?leqVgt.
Qed.

Lemma sum_odd_poly p :
  \sum_(i < size p | odd i) p`_i *: 'X^i = (odd_poly p \Po 'X^2) * 'X.
Proof.
apply/polyP => i; rewrite coefMX coef_comp_poly_Xn// coef_sumMXn coef_odd_poly/=.
case: i => [|i]//=; first by rewrite big_andbC big1// => -[[|j]//].
rewrite big_ord1_cond_eq/= -dvdn2 andbC -muln2.
by case: dvdnP => //= -[k ->]; rewrite mulnK// if_nth ?leqVgt.
Qed.

(* Decomposition in odd and even part                                         *)
Lemma poly_even_odd p : even_poly p \Po 'X^2 + (odd_poly p \Po 'X^2) * 'X = p.
Proof.
rewrite -sum_even_poly -sum_odd_poly addrC -(bigID _ xpredT).
by rewrite -[RHS]coefK poly_def.
Qed.

(* take and drop for polynomials                                              *)

Definition take_poly m p := \poly_(i < m) p`_i.

Lemma size_take_poly m p : size (take_poly m p) <= m.
Proof. exact: size_poly. Qed.

Lemma coef_take_poly m p i : (take_poly m p)`_i = if i < m then p`_i else 0.
Proof. exact: coef_poly. Qed.

Lemma take_poly_id m p : size p <= m -> take_poly m p = p.
Proof.
move=> /leq_trans gep; apply/polyP => i; rewrite coef_poly if_nth//=.
by case: ltnP => // /gep->.
Qed.

Lemma take_polyD m p q : take_poly m (p + q) = take_poly m p + take_poly m q.
Proof.
by apply/polyP => i; rewrite !(coefD, coef_poly); case: leqP; rewrite ?add0r.
Qed.

Lemma take_polyZ k m p : take_poly m (k *: p) = k *: take_poly m p.
Proof.
apply/polyP => i; rewrite !(coefZ, coef_take_poly); case: leqP => //.
by rewrite mulr0.
Qed.

Fact take_poly_is_linear m : linear (take_poly m).
Proof. by move=> k p q; rewrite take_polyD take_polyZ. Qed.

HB.instance Definition _ m :=
  GRing.isSemilinear.Build R {poly R} {poly R} _ (take_poly m)
    (GRing.semilinear_linear (take_poly_is_linear m)).

Lemma take_poly_sum m I r P (p : I -> {poly R}) :
  take_poly m (\sum_(i <- r | P i) p i) = \sum_(i <- r| P i) take_poly m (p i).
Proof. exact: linear_sum. Qed.

Lemma take_poly0l p : take_poly 0 p = 0.
Proof. exact/size_poly_leq0P/size_take_poly. Qed.

Lemma take_poly0r m : take_poly m 0 = 0.
Proof. exact: linear0. Qed.

Lemma take_polyMXn m n p :
  take_poly m (p * 'X^n) = take_poly (m - n) p * 'X^n.
Proof.
have [->|/eqP p_neq0] := p =P 0; first by rewrite !(mul0r, take_poly0r).
apply/polyP => i; rewrite !(coef_take_poly, coefMXn).
by have [iLn|nLi] := leqP n i; rewrite ?if_same// ltn_sub2rE.
Qed.

Lemma take_polyMXn_0 n p : take_poly n (p * 'X^n) = 0.
Proof. by rewrite take_polyMXn subnn take_poly0l mul0r. Qed.

Lemma take_polyDMXn n p q : size p <= n -> take_poly n (p + q * 'X^n) = p.
Proof. by move=> ?; rewrite take_polyD take_poly_id// take_polyMXn_0 addr0. Qed.

Definition drop_poly m p := \poly_(i < size p - m) p`_(i + m).

Lemma coef_drop_poly m p i : (drop_poly m p)`_i = p`_(i + m).
Proof. by rewrite coef_poly ltn_subRL addnC if_nth ?leqVgt. Qed.

Lemma drop_poly_eq0 m p : size p <= m -> drop_poly m p = 0.
Proof.
move=> sLm; apply/polyP => i; rewrite coef_poly coef0 ltn_subRL addnC.
by rewrite if_nth ?leqVgt// nth_default// (leq_trans _ (leq_addl _ _)).
Qed.

Lemma size_drop_poly n p : size (drop_poly n p) = (size p - n)%N.
Proof.
have [pLn|nLp] := leqP (size p) n.
  by rewrite (eqP pLn) drop_poly_eq0 ?size_poly0.
have p_neq0 : p != 0 by rewrite -size_poly_gt0 (leq_trans _ nLp).
by rewrite size_poly_eq// predn_sub subnK ?lead_coef_eq0// -ltnS -polySpred.
Qed.

Lemma sum_drop_poly n p :
  \sum_(n <= i < size p) p`_i *: 'X^i = drop_poly n p * 'X^n.
Proof.
rewrite (big_addn 0) big_mkord /drop_poly poly_def mulr_suml.
by apply: eq_bigr => i _; rewrite exprD scalerAl.
Qed.

Lemma drop_polyD m p q : drop_poly m (p + q) = drop_poly m p + drop_poly m q.
Proof. by apply/polyP => i; rewrite coefD !coef_drop_poly coefD. Qed.

Lemma drop_polyZ k m p : drop_poly m (k *: p) = k *: drop_poly m p.
Proof. by apply/polyP => i; rewrite coefZ !coef_drop_poly coefZ. Qed.

Fact drop_poly_is_linear m : linear (drop_poly m).
Proof. by move=> k p q; rewrite drop_polyD drop_polyZ. Qed.

HB.instance Definition _ m :=
  GRing.isSemilinear.Build R {poly R} {poly R} _ (drop_poly m)
    (GRing.semilinear_linear (drop_poly_is_linear m)).

Lemma drop_poly_sum m I r P (p : I -> {poly R}) :
  drop_poly m (\sum_(i <- r | P i) p i) = \sum_(i <- r | P i) drop_poly m (p i).
Proof. exact: linear_sum. Qed.

Lemma drop_poly0l p : drop_poly 0 p = p.
Proof. by apply/polyP => i; rewrite coef_poly subn0 addn0 if_nth ?leqVgt. Qed.

Lemma drop_poly0r m : drop_poly m 0 = 0. Proof. exact: linear0. Qed.

Lemma drop_polyMXn m n p :
  drop_poly m (p * 'X^n) = drop_poly (m - n) p * 'X^(n - m).
Proof.
have [->|p_neq0] := eqVneq p 0; first by rewrite mul0r !drop_poly0r mul0r.
apply/polyP => i; rewrite !(coefMXn, coef_drop_poly) ltn_subRL [(m + i)%N]addnC.
have [i_small|i_big]// := ltnP; congr nth.
by have [mn|/ltnW mn] := leqP m n;
   rewrite (eqP mn) (addn0, subn0) (subnBA, addnBA).
Qed.

Lemma drop_polyMXn_id n p : drop_poly n (p * 'X^ n) = p.
Proof. by rewrite drop_polyMXn subnn drop_poly0l expr0 mulr1. Qed.

Lemma drop_polyDMXn n p q : size p <= n -> drop_poly n (p + q * 'X^n) = q.
Proof. by move=> ?; rewrite drop_polyD drop_poly_eq0// drop_polyMXn_id add0r. Qed.

Lemma poly_take_drop n p : take_poly n p + drop_poly n p * 'X^n = p.
Proof.
apply/polyP => i; rewrite coefD coefMXn coef_take_poly coef_drop_poly.
by case: ltnP => ni; rewrite ?addr0 ?add0r//= subnK.
Qed.

Lemma eqp_take_drop n p q :
  take_poly n p = take_poly n q -> drop_poly n p = drop_poly n q -> p = q.
Proof.
by move=> tpq dpq; rewrite -[p](poly_take_drop n) -[q](poly_take_drop n) tpq dpq.
Qed.

End Surgery.

Definition coefE :=
  (coef0, coef1, coefC, coefX, coefXn, coef_sumMXn,
   coefZ, coefMC, coefCM, coefXnM, coefMXn, coefXM, coefMX, coefMNn, coefMn,
   coefN, coefB, coefD, coef_even_poly, coef_odd_poly,
   coef_take_poly, coef_drop_poly, coef_cons, coef_Poly, coef_poly,
   coef_deriv, coef_nderivn, coef_derivn, coef_map, coef_sum,
   coef_comp_poly_Xn, coef_comp_poly).

Section PolynomialComNzRing.

Variable R : comNzRingType.
Implicit Types p q : {poly R}.

Fact poly_mul_comm p q : p * q = q * p.
Proof.
apply/polyP=> i; rewrite coefM coefMr.
by apply: eq_bigr => j _; rewrite mulrC.
Qed.

HB.instance Definition _ := GRing.PzRing_hasCommutativeMul.Build (polynomial R)
  poly_mul_comm.
HB.instance Definition _ := GRing.Lalgebra_isComAlgebra.Build R (polynomial R).

Lemma coef_prod_XsubC (ps : seq R) (n : nat) :
  (n <= size ps)%N ->
  (\prod_(p <- ps) ('X - p%:P))`_n =
  (-1) ^+ (size ps - n)%N *
    \sum_(I in {set 'I_(size ps)} | #|I| == (size ps - n)%N)
        \prod_(i in I) ps`_i.
Proof.
move=> nle.
under eq_bigr => i _ do rewrite addrC -raddfN/=.
rewrite -{1}(in_tupleE ps) -(map_tnth_enum (_ ps)) big_map.
rewrite enumT bigA_distr /= coef_sum.
transitivity (\sum_(I in {set 'I_(size ps)}) if #|I| == (size ps - n)%N then
                  \prod_(i < size ps | i \in I) - ps`_i else 0).
  apply eq_bigr => I _.
  rewrite big_if/= big_const iter_mulr_1 -rmorph_prod/= coefCM coefXn.
  under eq_bigr => i _ do rewrite (tnth_nth 0)/=.
  rewrite -[#|I| == _](eqn_add2r n) subnK//.
  rewrite -[X in (_ + _)%N == X]card_ord -(cardC I) eqn_add2l.
  by case: ifP; rewrite ?mulr1 ?mulr0.
by rewrite -big_mkcond mulr_sumr/=; apply: eq_bigr => I /eqP <-; rewrite prodrN.
Qed.

Lemma coefPn_prod_XsubC (ps : seq R) : size ps != 0 ->
  (\prod_(p <- ps) ('X - p%:P))`_(size ps).-1 =
  - \sum_(p <- ps) p.
Proof.
rewrite coef_prod_XsubC ?leq_pred// => ps0.
have -> : (size ps - (size ps).-1 = 1)%N.
  by move: ps0; case: (size ps) => // n _; exact: subSnn.
rewrite expr1 mulN1r; congr GRing.opp.
set f : 'I_(size ps) -> {set 'I_(size ps)} := fun a => [set a].
transitivity (\sum_(I in imset f (mem setT)) \prod_(i in I) ps`_i).
  apply: congr_big => // I /=.
  by apply/cards1P/imsetP => [[a ->] | [a _ ->]]; exists a.
rewrite big_imset/=; last first.
  by move=> i j _ _ ij; apply/set1P; rewrite -/(f j) -ij set11.
rewrite -[in RHS](in_tupleE ps) -(map_tnth_enum (_ ps)) big_map enumT.
apply: congr_big => // i; first exact: in_setT.
by rewrite big_set1 (tnth_nth 0).
Qed.

Lemma coef0_prod_XsubC (ps : seq R) :
  (\prod_(p <- ps) ('X - p%:P))`_0 =
  (-1) ^+ (size ps) * \prod_(p <- ps) p.
Proof.
rewrite coef_prod_XsubC// subn0; congr GRing.mul.
transitivity (\sum_(I in [set setT : {set 'I_(size ps)}]) \prod_(i in I) ps`_i).
  apply: congr_big =>// i/=.
  apply/idP/set1P => [/eqP cardE | ->]; last by rewrite cardsT card_ord.
  by apply/eqP; rewrite eqEcard subsetT cardsT card_ord cardE leqnn.
rewrite big_set1 -[in RHS](in_tupleE ps) -(map_tnth_enum (_ ps)) big_map enumT.
apply: congr_big => // i; first exact: in_setT.
by rewrite (tnth_nth 0).
Qed.

Lemma hornerM p q x : (p * q).[x] = p.[x] * q.[x].
Proof. by rewrite hornerM_comm //; apply: mulrC. Qed.

Lemma horner_exp p x n : (p ^+ n).[x] = p.[x] ^+ n.
Proof. by rewrite horner_exp_comm //; apply: mulrC. Qed.

Lemma horner_prod I r (P : pred I) (F : I -> {poly R}) x :
  (\prod_(i <- r | P i) F i).[x] = \prod_(i <- r | P i) (F i).[x].
Proof. by elim/big_rec2: _ => [|i _ p _ <-]; rewrite (hornerM, hornerC). Qed.

Definition hornerE :=
  (hornerD, hornerN, hornerX, hornerC, horner_exp,
   simp, hornerCM, hornerZ, hornerM, horner_cons).

Definition horner_eval (x : R) := horner^~ x.
Lemma horner_evalE x p : horner_eval x p = p.[x]. Proof. by []. Qed.

Fact horner_eval_is_linear x : linear_for *%R (horner_eval x).
Proof.
have cxid: commr_rmorph idfun x by apply: mulrC.
have evalE : horner_eval x =1 horner_morph cxid.
  by move=> p; congr _.[x]; rewrite map_poly_id.
by move=> c p q; rewrite !evalE linearP.
Qed.

Fact horner_eval_is_monoid_morphism x : monoid_morphism (horner_eval x).
Proof.
have cxid: commr_rmorph idfun x by apply: mulrC.
have evalE : horner_eval x =1 horner_morph cxid.
  by move=> p; congr _.[x]; rewrite map_poly_id.
by split=> [|p q]; rewrite !evalE ?rmorph1// rmorphM.
Qed.
#[deprecated(since="mathcomp 2.5.0",
      note="use `horner_eval_is_monoid_morphism` instead")]
Definition horner_eval_is_multiplicative x :=
  (fun g => (g.2, g.1)) (horner_eval_is_monoid_morphism x).
HB.instance Definition _ x :=
  GRing.isSemilinear.Build R {poly R} R _ (horner_eval x)
    (GRing.semilinear_linear (horner_eval_is_linear x)).

HB.instance Definition _ x :=
  GRing.isMonoidMorphism.Build {poly R} R (horner_eval x)
    (horner_eval_is_monoid_morphism x).

Section HornerAlg.

Variable A : algType R. (* For univariate polys, commutativity is not needed *)

Section Defs.

Variable a : A.

Lemma in_alg_comm : commr_rmorph (in_alg A) a.
Proof. move=> r /=; by rewrite /GRing.comm comm_alg. Qed.

Definition horner_alg := horner_morph in_alg_comm.

Lemma horner_algC c : horner_alg c%:P = c%:A.
Proof. exact: horner_morphC. Qed.

Lemma horner_algX : horner_alg 'X = a.
Proof. exact:  horner_morphX. Qed.

HB.instance Definition _ := GRing.LRMorphism.on horner_alg.

End Defs.

Variable (pf : {lrmorphism {poly R} -> A}).

Lemma poly_alg_initial : pf =1 horner_alg (pf 'X).
Proof.
apply: poly_ind => [|p a IHp]; first by rewrite !rmorph0.
rewrite !rmorphD !rmorphM /= -{}IHp horner_algC ?horner_algX.
by rewrite -alg_polyC rmorph_alg.
Qed.

End HornerAlg.

Fact comp_poly_is_monoid_morphism q : monoid_morphism (comp_poly q).
Proof.
split=> [|p1 p2]; first by rewrite comp_polyC.
by rewrite /comp_poly rmorphM hornerM_comm //; apply: mulrC.
Qed.
#[deprecated(since="mathcomp 2.5.0",
      note="use `comp_poly_is_monoid_morphism` instead")]
Definition comp_poly_multiplicative q :=
  (fun g => (g.2, g.1)) (comp_poly_is_monoid_morphism q).
HB.instance Definition _ q := GRing.isMonoidMorphism.Build _ _ (comp_poly q)
  (comp_poly_is_monoid_morphism q).

Lemma comp_polyM p q r : (p * q) \Po r = (p \Po r) * (q \Po r).
Proof. exact: rmorphM. Qed.

Lemma comp_polyA p q r : p \Po (q \Po r) = (p \Po q) \Po r.
Proof.
elim/poly_ind: p => [|p c IHp]; first by rewrite !comp_polyC.
by rewrite !comp_polyD !comp_polyM !comp_polyX IHp !comp_polyC.
Qed.

Lemma horner_comp p q x : (p \Po q).[x] = p.[q.[x]].
Proof. by apply: polyC_inj; rewrite -!comp_polyCr comp_polyA. Qed.

Lemma root_comp p q x : root (p \Po q) x = root p (q.[x]).
Proof. by rewrite !rootE horner_comp. Qed.

Lemma deriv_comp p q : (p \Po q) ^`() = (p ^`() \Po q) * q^`().
Proof.
elim/poly_ind: p => [|p c IHp]; first by rewrite !(deriv0, comp_poly0) mul0r.
rewrite comp_poly_MXaddC derivD derivC derivM IHp derivMXaddC comp_polyD.
by rewrite comp_polyM comp_polyX addr0 addrC mulrAC -mulrDl.
Qed.

Lemma deriv_exp p n : (p ^+ n)^`() = p^`() * p ^+ n.-1 *+ n.
Proof.
elim: n => [|n IHn]; first by rewrite expr0 mulr0n derivC.
by rewrite exprS derivM {}IHn (mulrC p) mulrnAl -mulrA -exprSr mulrS; case n.
Qed.

Definition derivCE := (derivE, deriv_exp).

End PolynomialComNzRing.

Section PolynomialIdomain.

(* Integral domain structure on poly *)
Variable R : idomainType.

Implicit Types (a b x y : R) (p q r m : {poly R}).

Lemma size_mul p q : p != 0 -> q != 0 -> size (p * q) = (size p + size q).-1.
Proof.
by move=> nz_p nz_q; rewrite -size_proper_mul ?mulf_neq0 ?lead_coef_eq0.
Qed.

Fact poly_idomainAxiom p q : p * q = 0 -> (p == 0) || (q == 0).
Proof.
move=> pq0; apply/norP=> [[p_nz q_nz]]; move/eqP: (size_mul p_nz q_nz).
by rewrite eq_sym pq0 size_poly0 (polySpred p_nz) (polySpred q_nz) addnS.
Qed.

Definition poly_unit : pred {poly R} :=
  fun p => (size p == 1) && (p`_0 \in GRing.unit).

Definition poly_inv p := if p \in poly_unit then (p`_0)^-1%:P else p.

Fact poly_mulVp : {in poly_unit, left_inverse 1 poly_inv *%R}.
Proof.
move=> p Up; rewrite /poly_inv Up.
by case/andP: Up => /size_poly1P[c _ ->]; rewrite coefC -polyCM => /mulVr->.
Qed.

Fact poly_intro_unit p q : q * p = 1 -> p \in poly_unit.
Proof.
move=> pq1; apply/andP; split; last first.
  apply/unitrP; exists q`_0.
  by rewrite 2!mulrC -!/(coefp 0 _) -rmorphM pq1 rmorph1.
have: size (q * p) == 1 by rewrite pq1 size_poly1.
have [-> | nz_p] := eqVneq p 0; first by rewrite mulr0 size_poly0.
have [-> | nz_q] := eqVneq q 0; first by rewrite mul0r size_poly0.
rewrite size_mul // (polySpred nz_p) (polySpred nz_q) addnS addSn !eqSS.
by rewrite addn_eq0 => /andP[].
Qed.

Fact poly_inv_out : {in [predC poly_unit], poly_inv =1 id}.
Proof. by rewrite /poly_inv => p /negbTE/= ->. Qed.

HB.instance Definition _ := GRing.ComNzRing_hasMulInverse.Build (polynomial R)
  poly_mulVp poly_intro_unit poly_inv_out.

HB.instance Definition _ := GRing.ComUnitRing_isIntegral.Build (polynomial R)
  poly_idomainAxiom.

Lemma poly_unitE p :
  (p \in GRing.unit) = (size p == 1) && (p`_0 \in GRing.unit).
Proof. by []. Qed.

Lemma poly_invE p : p ^-1 = if p \in GRing.unit then (p`_0)^-1%:P else p.
Proof. by []. Qed.

Lemma polyCV c : c%:P^-1 = (c^-1)%:P.
Proof.
have [/rmorphV-> // | nUc] := boolP (c \in GRing.unit).
by rewrite !invr_out // poly_unitE coefC (negbTE nUc) andbF.
Qed.

Lemma rootM p q x : root (p * q) x = root p x || root q x.
Proof. by rewrite !rootE hornerM mulf_eq0. Qed.

Lemma rootZ x a p : a != 0 -> root (a *: p) x = root p x.
Proof. by move=> nz_a; rewrite -mul_polyC rootM rootC (negPf nz_a). Qed.

Lemma root_exp p n a: comm_poly p a -> (0 < n)%N -> root (p ^+ n) a = root p a.
Proof. by move=> ? n0; rewrite !rootE horner_exp_comm// expf_eq0 n0. Qed.

Lemma size_scale a p : a != 0 -> size (a *: p) = size p.
Proof. by move/lregP/lreg_size->. Qed.

Lemma size_Cmul a p : a != 0 -> size (a%:P * p) = size p.
Proof. by rewrite mul_polyC => /size_scale->. Qed.

Lemma lead_coefM p q : lead_coef (p * q) = lead_coef p * lead_coef q.
Proof.
have [-> | nz_p] := eqVneq p 0; first by rewrite !(mul0r, lead_coef0).
have [-> | nz_q] := eqVneq q 0; first by rewrite !(mulr0, lead_coef0).
by rewrite lead_coef_proper_mul // mulf_neq0 ?lead_coef_eq0.
Qed.

Lemma lead_coef_prod I rI (P : {pred I}) (p : I -> {poly R}) :
  lead_coef (\prod_(i <- rI | P i) p i) = \prod_(i <- rI | P i) lead_coef (p i).
Proof. by apply/big_morph/lead_coef1; apply: lead_coefM. Qed.

Lemma lead_coefZ a p : lead_coef (a *: p) = a * lead_coef p.
Proof. by rewrite -mul_polyC lead_coefM lead_coefC. Qed.

Lemma scale_poly_eq0 a p : (a *: p == 0) = (a == 0) || (p == 0).
Proof. by rewrite -mul_polyC mulf_eq0 polyC_eq0. Qed.

Lemma size_prod (I : finType) (P : pred I) (F : I -> {poly R}) :
    (forall i, P i -> F i != 0) ->
  size (\prod_(i | P i) F i) = ((\sum_(i | P i) size (F i)).+1 - #|P|)%N.
Proof.
move=> nzF; transitivity (\sum_(i | P i) (size (F i)).-1).+1; last first.
  apply: canRL (addKn _) _; rewrite addnS -sum1_card -big_split /=.
  by congr _.+1; apply: eq_bigr => i /nzF/polySpred.
elim/big_rec2: _ => [|i d p /nzF nzFi IHp]; first by rewrite size_poly1.
by rewrite size_mul // -?size_poly_eq0 IHp // addnS polySpred.
Qed.

Lemma size_prod_seq (I : eqType)  (s : seq I) (F : I -> {poly R}) :
    (forall i, i \in s -> F i != 0) ->
  size (\prod_(i <- s) F i) = ((\sum_(i <- s) size (F i)).+1 - size s)%N.
Proof.
move=> nzF; rewrite big_tnth size_prod; last by move=> i; rewrite nzF ?mem_tnth.
by rewrite cardT /= size_enum_ord [in RHS]big_tnth.
Qed.

Lemma size_mul_eq1 p q : (size (p * q) == 1) = ((size p == 1) && (size q == 1)).
Proof.
have [->|pNZ] := eqVneq p 0; first by rewrite mul0r size_poly0.
have [->|qNZ] := eqVneq q 0; first by rewrite mulr0 size_poly0 andbF.
rewrite size_mul //.
by move: pNZ qNZ; rewrite -!size_poly_gt0; (do 2 case: size) => //= n [|[|]].
Qed.

Lemma size_prod_seq_eq1 (I : eqType) (s : seq I) (P : pred I) (F : I -> {poly R}) :
  reflect (forall i, P i && (i \in s) -> size (F i) = 1)
          (size (\prod_(i <- s | P i) F i) == 1%N).
Proof.
rewrite (big_morph _ (id1:=true) size_mul_eq1) ?size_polyC ?oner_neq0//.
rewrite big_all_cond; apply/(iffP allP).
  by move=> h i /andP[Pi ins]; apply/eqP/(implyP (h i ins) Pi).
by move=> h i ins; apply/implyP => Pi; rewrite h ?Pi.
Qed.

Lemma size_prod_eq1 (I : finType) (P : pred I) (F : I -> {poly R}) :
  reflect (forall i, P i -> size (F i) = 1)
          (size (\prod_(i | P i) F i) == 1).
Proof.
apply: (iffP (size_prod_seq_eq1 _ _ _)) => Hi i.
  by move=> Pi; apply: Hi; rewrite Pi /= mem_index_enum.
by rewrite mem_index_enum andbT; apply: Hi.
Qed.

Lemma size_exp p n : (size (p ^+ n)).-1 = ((size p).-1 * n)%N.
Proof.
elim: n => [|n IHn]; first by rewrite size_poly1 muln0.
have [-> | nz_p] := eqVneq p 0; first by rewrite exprS mul0r size_poly0.
rewrite exprS size_mul ?expf_neq0 // mulnS -{}IHn.
by rewrite polySpred // [size (p ^+ n)]polySpred ?expf_neq0 ?addnS.
Qed.

Lemma lead_coef_exp p n : lead_coef (p ^+ n) = lead_coef p ^+ n.
Proof.
elim: n => [|n IHn]; first by rewrite !expr0 lead_coef1.
by rewrite !exprS lead_coefM IHn.
Qed.

Lemma root_prod_XsubC rs x :
  root (\prod_(a <- rs) ('X - a%:P)) x = (x \in rs).
Proof.
elim: rs => [|a rs IHrs]; first by rewrite rootE big_nil hornerC oner_eq0.
by rewrite big_cons rootM IHrs root_XsubC.
Qed.

Lemma root_exp_XsubC n a x : root (('X - a%:P) ^+ n.+1) x = (x == a).
Proof. by rewrite rootE horner_exp expf_eq0 [_ == 0]root_XsubC. Qed.

Lemma size_comp_poly p q :
  (size (p \Po q)).-1 = ((size p).-1 * (size q).-1)%N.
Proof.
have [-> | nz_p] := eqVneq p 0; first by rewrite comp_poly0 size_poly0.
have [/size1_polyC-> | nc_q] := leqP (size q) 1.
  by rewrite comp_polyCr !size_polyC -!sub1b -!subnS muln0.
have nz_q: q != 0 by rewrite -size_poly_eq0 -(subnKC nc_q).
rewrite mulnC comp_polyE (polySpred nz_p) /= big_ord_recr /= addrC.
rewrite size_polyDl size_scale ?lead_coef_eq0 ?size_exp //=.
rewrite [ltnRHS]polySpred ?expf_neq0 // ltnS size_exp.
rewrite (leq_trans (size_sum _ _ _)) //; apply/bigmax_leqP => i _.
rewrite (leq_trans (size_scale_leq _ _)) // polySpred ?expf_neq0 //.
by rewrite size_exp -(subnKC nc_q) ltn_pmul2l.
Qed.

Lemma lead_coef_comp p q : size q > 1 ->
  lead_coef (p \Po q) = (lead_coef p) * lead_coef q ^+ (size p).-1.
Proof.
move=> q_gt1; rewrite !lead_coefE coef_comp_poly size_comp_poly.
have [->|nz_p] := eqVneq p 0; first by rewrite size_poly0 big_ord0 coef0 mul0r.
rewrite polySpred //= big_ord_recr /= big1 ?add0r => [|i _].
  by rewrite -!lead_coefE -lead_coef_exp !lead_coefE size_exp mulnC.
rewrite [X in _ * X]nth_default ?mulr0 ?(leq_trans (size_poly_exp_leq _ _)) //.
by rewrite mulnC ltn_mul2r -subn1 subn_gt0 q_gt1 /=.
Qed.

Lemma comp_poly_eq0 p q : size q > 1 -> (p \Po q == 0) = (p == 0).
Proof.
move=> sq_gt1; rewrite -!lead_coef_eq0 lead_coef_comp //.
rewrite mulf_eq0 expf_eq0 !lead_coef_eq0 -[q == 0]size_poly_leq0.
by rewrite [_ <= 0]leqNgt (leq_ltn_trans _ sq_gt1) ?andbF ?orbF.
Qed.

Lemma size_comp_poly2 p q : size q = 2 -> size (p \Po q) = size p.
Proof.
move=> sq2; have [->|pN0] := eqVneq p 0; first by rewrite comp_polyC.
by rewrite polySpred ?size_comp_poly ?comp_poly_eq0 ?sq2 // muln1 polySpred.
Qed.

Lemma comp_poly2_eq0 p q : size q = 2 -> (p \Po q == 0) = (p == 0).
Proof. by rewrite -!size_poly_eq0 => /size_comp_poly2->. Qed.

Theorem max_poly_roots p rs :
  p != 0 -> all (root p) rs -> uniq rs -> size rs < size p.
Proof.
elim: rs p => [p pn0 _ _ | r rs ihrs p pn0] /=; first by rewrite size_poly_gt0.
case/andP => rpr arrs /andP [rnrs urs]; case/factor_theorem: rpr => q epq.
have [q0 | ?] := eqVneq q 0; first by move: pn0; rewrite epq q0 mul0r eqxx.
have -> : size p = (size q).+1.
   by rewrite epq size_Mmonic ?monicXsubC // size_XsubC addnC.
suff /eq_in_all h : {in rs, root q =1 root p} by apply: ihrs => //; rewrite h.
move=> x xrs; rewrite epq rootM root_XsubC orbC; case: (eqVneq x r) => // exr.
by move: rnrs; rewrite -exr xrs.
Qed.

Lemma roots_geq_poly_eq0 p (rs : seq R) : all (root p) rs -> uniq rs ->
  (size rs >= size p)%N -> p = 0.
Proof. by move=> ??; apply: contraTeq => ?; rewrite leqNgt max_poly_roots. Qed.

End PolynomialIdomain.

(* FIXME: these are seamingly artificial ways to close the inheritance graph *)
(*    We make parameters more and more precise to trigger completion by HB   *)
HB.instance Definition _ (R : countNzRingType) :=
  [Countable of polynomial R by <:].
HB.instance Definition _ (R : countComNzRingType) :=
  [Countable of polynomial R by <:].
HB.instance Definition _ (R : countIdomainType) :=
  [Countable of polynomial R by <:].

Section MapFieldPoly.

Variables (F : fieldType) (R : nzRingType) (f : {rmorphism F -> R}).

Local Notation "p ^f" := (map_poly f p) : ring_scope.

Lemma size_map_poly p : size p^f = size p.
Proof.
have [-> | nz_p] := eqVneq p 0; first by rewrite rmorph0 !size_poly0.
by rewrite size_poly_eq // fmorph_eq0 // lead_coef_eq0.
Qed.

Lemma lead_coef_map p : lead_coef p^f = f (lead_coef p).
Proof.
have [-> | nz_p] := eqVneq p 0; first by rewrite !(rmorph0, lead_coef0).
by rewrite lead_coef_map_eq // fmorph_eq0 // lead_coef_eq0.
Qed.

Lemma map_poly_eq0 p : (p^f == 0) = (p == 0).
Proof. by rewrite -!size_poly_eq0 size_map_poly. Qed.

Lemma map_poly_inj : injective (map_poly f).
Proof.
move=> p q eqfpq; apply/eqP; rewrite -subr_eq0 -map_poly_eq0.
by rewrite rmorphB /= eqfpq subrr.
Qed.

Lemma map_monic p : (p^f \is monic) = (p \is monic).
Proof. by rewrite [in LHS]monicE lead_coef_map fmorph_eq1. Qed.

Lemma map_poly_com p x : comm_poly p^f (f x).
Proof. exact: map_comm_poly (mulrC x _). Qed.

Lemma fmorph_root p x : root p^f (f x) = root p x.
Proof. by rewrite rootE horner_map // fmorph_eq0. Qed.

Lemma fmorph_unity_root n z : n.-unity_root (f z) = n.-unity_root z.
Proof. by rewrite !unity_rootE -(inj_eq (fmorph_inj f)) rmorphXn ?rmorph1. Qed.

Lemma fmorph_primitive_root n z :
  n.-primitive_root (f z) = n.-primitive_root z.
Proof.
by congr (_ && _); apply: eq_forallb => i; rewrite fmorph_unity_root.
Qed.

End MapFieldPoly.

Arguments map_poly_inj {F R} f [p1 p2] : rename.

Section MaxRoots.

Variable R : unitRingType.
Implicit Types (x y : R) (rs : seq R) (p : {poly R}).

Definition diff_roots (x y : R) := (x * y == y * x) && (y - x \in GRing.unit).

Fixpoint uniq_roots rs :=
  if rs is x :: rs' then all (diff_roots x) rs' && uniq_roots rs' else true.

Lemma uniq_roots_prod_XsubC p rs :
    all (root p) rs -> uniq_roots rs ->
  exists q, p = q * \prod_(z <- rs) ('X - z%:P).
Proof.
elim: rs => [|z rs IHrs] /=; first by rewrite big_nil; exists p; rewrite mulr1.
case/andP=> rpz rprs /andP[drs urs]; case: IHrs => {urs rprs}// q def_p.
have [|q' def_q] := factor_theorem q z _; last first.
  by exists q'; rewrite big_cons mulrA -def_q.
rewrite {p}def_p in rpz.
elim/last_ind: rs drs rpz => [|rs t IHrs] /=; first by rewrite big_nil mulr1.
rewrite all_rcons => /andP[/andP[/eqP czt Uzt] /IHrs{}IHrs].
rewrite -cats1 big_cat big_seq1 /= mulrA rootE hornerM_comm; last first.
  by rewrite /comm_poly hornerXsubC mulrBl mulrBr czt.
rewrite hornerXsubC -opprB mulrN oppr_eq0 -(mul0r (t - z)).
by rewrite (inj_eq (mulIr Uzt)) => /IHrs.
Qed.

Theorem max_ring_poly_roots p rs :
  p != 0 -> all (root p) rs -> uniq_roots rs -> size rs < size p.
Proof.
move=> nz_p _ /(@uniq_roots_prod_XsubC p)[// | q def_p]; rewrite def_p in nz_p *.
have nz_q: q != 0 by apply: contraNneq nz_p => ->; rewrite mul0r.
rewrite size_Mmonic ?monic_prod_XsubC // (polySpred nz_q) addSn /=.
by rewrite size_prod_XsubC leq_addl.
Qed.

Lemma all_roots_prod_XsubC p rs :
    size p = (size rs).+1 -> all (root p) rs -> uniq_roots rs ->
  p = lead_coef p *: \prod_(z <- rs) ('X - z%:P).
Proof.
move=> size_p /uniq_roots_prod_XsubC def_p Urs.
case/def_p: Urs => q -> {p def_p} in size_p *.
have [q0 | nz_q] := eqVneq q 0; first by rewrite q0 mul0r size_poly0 in size_p.
have{q nz_q size_p} /size_poly1P[c _ ->]: size q == 1.
  rewrite -(eqn_add2r (size rs)) add1n -size_p.
  by rewrite size_Mmonic ?monic_prod_XsubC // size_prod_XsubC addnS.
by rewrite lead_coef_Mmonic ?monic_prod_XsubC // lead_coefC mul_polyC.
Qed.

End MaxRoots.

Section FieldRoots.

Variable F : fieldType.
Implicit Types (p : {poly F}) (rs : seq F).

Lemma poly2_root p : size p = 2 -> {r | root p r}.
Proof.
case: p => [[|p0 [|p1 []]] //= nz_p1]; exists (- p0 / p1).
by rewrite /root addr_eq0 /= mul0r add0r mulrC divfK ?opprK.
Qed.

Lemma uniq_rootsE rs : uniq_roots rs = uniq rs.
Proof.
elim: rs => //= r rs ->; congr (_ && _); rewrite -has_pred1 -all_predC.
by apply: eq_all => t; rewrite /diff_roots mulrC eqxx unitfE subr_eq0.
Qed.

Lemma root_ZXsubC (a b r : F) : a != 0 ->
  root (a *: 'X - b%:P) r = (r == b / a).
Proof.
move=> a0; rewrite rootE !hornerE.
by rewrite -[r in RHS]divr1 eqr_div ?oner_neq0// mulr1 mulrC subr_eq0.
Qed.

Section UnityRoots.

Variable n : nat.

Lemma max_unity_roots rs :
  n > 0 -> all n.-unity_root rs -> uniq rs -> size rs <= n.
Proof.
move=> n_gt0 rs_n_1 Urs; have szPn := size_XnsubC (1 : F) n_gt0.
by rewrite -ltnS -szPn max_poly_roots -?size_poly_eq0 ?szPn.
Qed.

Lemma mem_unity_roots rs :
    n > 0 -> all n.-unity_root rs -> uniq rs -> size rs = n ->
  n.-unity_root =i rs.
Proof.
move=> n_gt0 rs_n_1 Urs sz_rs_n x; rewrite -topredE /=.
apply/idP/idP=> xn1; last exact: (allP rs_n_1).
apply: contraFT (ltnn n) => not_rs_x.
by rewrite -{1}sz_rs_n (@max_unity_roots (x :: rs)) //= ?xn1 ?not_rs_x.
Qed.

(* Showing the existence of a primitive root requires the theory in cyclic. *)

Variable z : F.
Hypothesis prim_z : n.-primitive_root z.

Let zn := [seq z ^+ i | i <- index_iota 0 n].

Lemma factor_Xn_sub_1 : \prod_(0 <= i < n) ('X - (z ^+ i)%:P) = 'X^n - 1.
Proof.
transitivity (\prod_(w <- zn) ('X - w%:P)); first by rewrite big_map.
have n_gt0: n > 0 := prim_order_gt0 prim_z.
rewrite (@all_roots_prod_XsubC _ ('X^n - 1) zn); first 1 last.
- by rewrite size_XnsubC // size_map size_iota subn0.
- apply/allP=> _ /mapP[i _ ->] /=; rewrite rootE !hornerE.
  by rewrite exprAC (prim_expr_order prim_z) expr1n subrr.
- rewrite uniq_rootsE map_inj_in_uniq ?iota_uniq // => i j.
  rewrite !mem_index_iota => ltin ltjn /eqP.
  by rewrite (eq_prim_root_expr prim_z) !modn_small // => /eqP.
by rewrite (monicP (monicXnsubC 1 n_gt0)) scale1r.
Qed.

Lemma prim_rootP x : x ^+ n = 1 -> {i : 'I_n | x = z ^+ i}.
Proof.
move=> xn1; pose logx := [pred i : 'I_n | x == z ^+ i].
case: (pickP logx) => [i /eqP-> | no_i]; first by exists i.
case: notF; suffices{no_i}: x \in zn.
  case/mapP=> i; rewrite mem_index_iota => lt_i_n def_x.
  by rewrite -(no_i (Ordinal lt_i_n)) /= -def_x.
rewrite -root_prod_XsubC big_map factor_Xn_sub_1.
by rewrite [root _ x]unity_rootE xn1.
Qed.

End UnityRoots.

End FieldRoots.

Section MapPolyRoots.

Variables (F : fieldType) (R : unitRingType) (f : {rmorphism F -> R}).

Lemma map_diff_roots x y : diff_roots (f x) (f y) = (x != y).
Proof.
rewrite /diff_roots -rmorphB // fmorph_unit // subr_eq0 //.
by rewrite rmorph_comm // eqxx eq_sym.
Qed.

Lemma map_uniq_roots s : uniq_roots (map f s) = uniq s.
Proof.
elim: s => //= x s ->; congr (_ && _); elim: s => //= y s ->.
by rewrite map_diff_roots -negb_or.
Qed.

End MapPolyRoots.

Section AutPolyRoot.
(* The action of automorphisms on roots of unity. *)

Variable F : fieldType.
Implicit Types u v : {rmorphism F -> F}.

Lemma aut_prim_rootP u z n :
  n.-primitive_root z -> {k | coprime k n & u z = z ^+ k}.
Proof.
move=> prim_z; have:= prim_z; rewrite -(fmorph_primitive_root u) => prim_uz.
have [[k _] /= def_uz] := prim_rootP prim_z (prim_expr_order prim_uz).
by exists k; rewrite // -(prim_root_exp_coprime _ prim_z) -def_uz.
Qed.

Lemma aut_unity_rootP u z n : n > 0 -> z ^+ n = 1 -> {k | u z = z ^+ k}.
Proof.
by move=> _ /prim_order_exists[// | m /(aut_prim_rootP u)[k]]; exists k.
Qed.

Lemma aut_unity_rootC u v z n : n > 0 -> z ^+ n = 1 -> u (v z) = v (u z).
Proof.
move=> n_gt0 /(aut_unity_rootP _ n_gt0) def_z.
have [[i def_uz] [j def_vz]] := (def_z u, def_z v).
by rewrite def_vz def_uz !rmorphXn /= def_vz def_uz exprAC.
Qed.

End AutPolyRoot.

Module UnityRootTheory.

Notation "n .-unity_root" := (root_of_unity n) : unity_root_scope.
Notation "n .-primitive_root" := (primitive_root_of_unity n) : unity_root_scope.
Open Scope unity_root_scope.

Definition unity_rootE := unity_rootE.
Definition unity_rootP := @unity_rootP.
Arguments unity_rootP {R n z}.

Definition prim_order_exists := prim_order_exists.
Notation prim_order_gt0 :=  prim_order_gt0.
Notation prim_expr_order := prim_expr_order.
Definition prim_expr_mod := prim_expr_mod.
Definition prim_order_dvd := prim_order_dvd.
Definition eq_prim_root_expr := eq_prim_root_expr.

Definition rmorph_unity_root := rmorph_unity_root.
Definition fmorph_unity_root := fmorph_unity_root.
Definition fmorph_primitive_root := fmorph_primitive_root.
Definition max_unity_roots := max_unity_roots.
Definition mem_unity_roots := mem_unity_roots.
Definition prim_rootP := prim_rootP.

End UnityRootTheory.

Module Export Pdeg2.

Module Export Field.

Section Pdeg2Field.
Variable F : fieldType.
Hypothesis nz2 : 2 != 0 :> F.

Variable p : {poly F}.
Hypothesis degp : size p = 3.

Let a := p`_2.
Let b := p`_1.
Let c := p`_0.

Let pneq0 : p != 0. Proof. by rewrite -size_poly_gt0 degp. Qed.
Let aneq0 : a != 0.
Proof. by move: pneq0; rewrite -lead_coef_eq0 lead_coefE degp. Qed.
Let a2neq0 : 2 * a != 0. Proof. by rewrite mulf_neq0. Qed.
Let sqa2neq0 : (2 * a) ^+ 2 != 0. Proof. exact: expf_neq0. Qed.

Let aa4 : 4 * a * a = (2 * a)^+2.
Proof. by rewrite expr2 mulrACA mulrA -natrM. Qed.

Let splitr (x : F) : x = x / 2 + x / 2.
Proof.
by apply: (mulIf nz2); rewrite -mulrDl mulfVK// mulr_natr mulr2n.
Qed.

Let pE : p = a *: 'X^2 + b *: 'X + c%:P.
Proof.
apply/polyP => + /[!coefE] => -[|[|[|i]]] /=; rewrite !Monoid.simpm//.
by rewrite nth_default// degp.
Qed.

Let delta := b ^+ 2 - 4 * a * c.

Lemma deg2_poly_canonical :
  p = a *: (('X + (b / (2 * a))%:P)^+2 - (delta / (4 * a ^+ 2))%:P).
Proof.
rewrite pE sqrrD -!addrA scalerDr; congr +%R; rewrite addrA scalerDr; congr +%R.
- rewrite -mulrDr -polyCD -!mul_polyC mulrA mulrAC -polyCM.
  by rewrite [a * _]mulrC mulrDl invfM -!mulrA mulVf// mulr1 -splitr.
- rewrite [a ^+ 2]expr2 mulrA aa4 -polyC_exp -polyCB expr_div_n -mulrBl subKr.
  by rewrite scale_polyC mulrCA mulrACA aa4 mulrCA mulfV// mulr1.
Qed.

Variable r : F.
Hypothesis r_sqrt_delta : r ^+ 2 = delta.

Let r1 := (- b - r) / (2 * a).
Let r2 := (- b + r) / (2 * a).

Lemma deg2_poly_factor : p = a *: ('X - r1%:P) * ('X - r2%:P).
Proof.
rewrite [p]deg2_poly_canonical//= -/a -/b -/c -/delta /r1 /r2.
rewrite ![(- b + _) * _]mulrDl 2!polyCD 2!opprD 2!addrA !mulNr !polyCN !opprK.
rewrite -scalerAl [in RHS]mulrC -subr_sqr -polyC_exp -[4]/(2 * 2)%:R natrM.
by rewrite -expr2 -exprMn [in RHS]exprMn exprVn r_sqrt_delta.
Qed.

Lemma deg2_poly_root1 : root p r1.
Proof.
apply/factor_theorem.
by exists (a *: ('X - r2%:P)); rewrite deg2_poly_factor -!scalerAl mulrC.
Qed.

Lemma deg2_poly_root2 : root p r2.
Proof.
apply/factor_theorem.
by exists (a *: ('X - r1%:P)); rewrite deg2_poly_factor -!scalerAl.
Qed.

End Pdeg2Field.
End Field.

Module FieldMonic.

Section Pdeg2FieldMonic.
Variable F : fieldType.
Hypothesis nz2 : 2 != 0 :> F.

Variable p : {poly F}.
Hypothesis degp : size p = 3.
Hypothesis monicp : p \is monic.

Let a := p`_2.
Let b := p`_1.
Let c := p`_0.

Let a1 : a = 1. Proof. by move: (monicP monicp); rewrite lead_coefE degp. Qed.

Let delta := b ^+ 2 - 4 * c.

Lemma deg2_poly_canonical : p = (('X + (b / 2)%:P)^+2 - (delta / 4)%:P).
Proof. by rewrite [p]deg2_poly_canonical// -/a a1 scale1r expr1n !mulr1. Qed.

Variable r : F.
Hypothesis r_sqrt_delta : r ^+ 2 = delta.

Let r1 := (- b - r) / 2.
Let r2 := (- b + r) / 2.

Lemma deg2_poly_factor : p = ('X - r1%:P) * ('X - r2%:P).
Proof.
by rewrite [p](@deg2_poly_factor _ _ _ _ r)// -/a a1 !mulr1 ?scale1r.
Qed.

Lemma deg2_poly_root1 : root p r1.
Proof.
rewrite /r1 -[2]mulr1 -[X in 2 * X]a1.
by apply: deg2_poly_root1; rewrite // -/a a1 mulr1.
Qed.

Lemma deg2_poly_root2 : root p r2.
Proof.
rewrite /r2 -[2]mulr1 -[X in 2 * X]a1.
by apply: deg2_poly_root2; rewrite // -/a a1 mulr1.
Qed.

End Pdeg2FieldMonic.
End FieldMonic.
End Pdeg2.

Section DecField.

Variable F : decFieldType.

Lemma dec_factor_theorem (p : {poly F}) :
  {s : seq F & {q : {poly F} | p = q * \prod_(x <- s) ('X - x%:P)
                             /\ (q != 0 -> forall x, ~~ root q x)}}.
Proof.
pose polyT (p : seq F) := (foldr (fun c f => f * 'X_0 + c%:T) (0%R)%:T p)%T.
have eval_polyT (q : {poly F}) x : GRing.eval [:: x] (polyT q) = q.[x].
  by rewrite /horner; elim: (val q) => //= ? ? ->.
have [n] := ubnP (size p); elim: n => // n IHn in p *.
have /decPcases /= := @satP F [::] ('exists 'X_0, polyT p == 0%T).
case: ifP => [_ /sig_eqW[x]|_ noroot]; last first.
  exists [::], p; rewrite big_nil mulr1; split => // p_neq0 x.
  by apply/negP=> /rootP rpx; apply: noroot; exists x; rewrite eval_polyT.
rewrite eval_polyT => /rootP/factor_theorem/sig_eqW[p1 ->].
have [->|nz_p1] := eqVneq p1 0; first by exists [::], 0; rewrite !mul0r eqxx.
rewrite size_Mmonic ?monicXsubC // size_XsubC addn2 => /IHn[s [q [-> irr_q]]].
by exists (rcons s x), q; rewrite -cats1 big_cat big_seq1 mulrA.
Qed.

End DecField.

Module PreClosedField.
Section UseAxiom.

Variable F : fieldType.
Hypothesis closedF : GRing.closed_field_axiom F.
Implicit Type p : {poly F}.

Lemma closed_rootP p : reflect (exists x, root p x) (size p != 1).
Proof.
have [-> | nz_p] := eqVneq p 0.
  by rewrite size_poly0; left; exists 0; rewrite root0.
rewrite neq_ltn [in _ < 1]polySpred //=.
apply: (iffP idP) => [p_gt1 | [a]]; last exact: root_size_gt1.
pose n := (size p).-1; have n_gt0: n > 0 by rewrite -ltnS -polySpred.
have [a Dan] := closedF (fun i => - p`_i / lead_coef p) n_gt0.
exists a; apply/rootP; rewrite horner_coef polySpred // big_ord_recr /= -/n.
rewrite {}Dan mulr_sumr -big_split big1 //= => i _.
by rewrite -!mulrA mulrCA mulNr mulVKf ?subrr ?lead_coef_eq0.
Qed.

Lemma closed_nonrootP p : reflect (exists x, ~~ root p x) (p != 0).
Proof.
apply: (iffP idP) => [nz_p | [x]]; last first.
  by apply: contraNneq => ->; apply: root0.
have [[x /rootP p1x0]|] := altP (closed_rootP (p - 1)).
  by exists x; rewrite -[p](subrK 1) /root hornerD p1x0 add0r hornerC oner_eq0.
rewrite negbK => /size_poly1P[c _ /(canRL (subrK 1)) Dp].
by exists 0; rewrite Dp -raddfD polyC_eq0 rootC in nz_p *.
Qed.

End UseAxiom.
End PreClosedField.

Section ClosedField.

Variable F : closedFieldType.
Implicit Type p : {poly F}.

Let closedF := @solve_monicpoly F.

Lemma closed_rootP p : reflect (exists x, root p x) (size p != 1).
Proof. exact: PreClosedField.closed_rootP. Qed.

Lemma closed_nonrootP p : reflect (exists x, ~~ root p x) (p != 0).
Proof. exact: PreClosedField.closed_nonrootP. Qed.

Lemma closed_field_poly_normal p :
  {r : seq F | p = lead_coef p *: \prod_(z <- r) ('X - z%:P)}.
Proof.
apply: sig_eqW; have [r [q [->]]] /= := dec_factor_theorem p.
have [->|] := eqVneq; first by exists [::]; rewrite mul0r lead_coef0 scale0r.
have [[x rqx ? /(_ isT x) /negP /(_ rqx)] //|] := altP (closed_rootP q).
rewrite negbK => /size_poly1P [c c_neq0-> _ _]; exists r.
rewrite mul_polyC lead_coefZ (monicP _) ?mulr1 //.
by rewrite monic_prod => // i; rewrite monicXsubC.
Qed.

End ClosedField.
