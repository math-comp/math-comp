# How to port a development from MathComp 1 to MathComp 2

Using https://github.com/coq-community/comp-dec-modal as an example.

compile and stop at the first mistake

## libs/fset.v

************************************************************************************

Put
From HB Require Import structures.
at the top of a file using MathComp structures

************************************************************************************

Canonical Structure fset_subType := [subType for elements by fset_type_rect].
->
HB.instance Definition _ := [isSub for elements by fset_type_rect].

************************************************************************************

Canonical Structure fset_eqType := EqType _ [eqMixin of fset_type by <:].
->
HB.instance Definition _ := [Equality of fset_type by <:].

************************************************************************************

Canonical Structure fset_predType := PredType (fun (X : fset_type) x => nosimpl x \in elements X).
->
unchanged

************************************************************************************

Canonical Structure fset_choiceType := Eval hnf in ChoiceType _ [choiceMixin of fset_type by <:].
->
HB.instance Definition _ := [Choice of fset_type by <:].
(NB: #[hnf] not useful here)

NB: we could have instantiated choice before and got eqtype for free

************************************************************************************

Canonical Structure fset_countType (T : countType) :=
  Eval hnf in CountType _ [countMixin of fset_type T by <:].
->
HB.instance Definition _ (T : countType) := [Countable of fset_type T by <:].

************************************************************************************

Canonical Structure fset_subCountType (T : countType) :=
  Eval hnf in [subCountType of fset_type T].
->
can be removed (look at the message from the previous instance)

************************************************************************************

Canonical Structure fsetU_law (T : choiceType) := 
  Monoid.Law (@fsetUA T) (@fset0U T) (@fsetU0 T).
->...

do
HB.about Monoid.Law.
to discover the type: Monoid.Law.type

do
HB.howto Monoid.Law.type. or HB.howto ({fset _}) Monoid.Law.type.
to discover the factories

pick up the most reasonable one

do
HB.about Monoid.isLaw.Build.
to discover the arguments:

HB: arguments: Monoid.isLaw.Build T idm op opA op1m opm1
    - T : Type
    - idm : T
    - op : T -> T -> T
    - opA : associative op
    - op1m : left_id idm op
    - opm1 : right_id idm op

it is good practice to put (at least) the key explicitly

... ->
HB.instance Definition _ (T : choiceType) := 
  Monoid.isLaw.Build {fset T} fset0 fsetU (@fsetUA T) (@fset0U T) (@fsetU0 T).

************************************************************************************

Canonical Structure fsetU_comlaw (T : choiceType) := 
  Monoid.ComLaw (@fsetUC T).
-> ...

HB.howto fsetU Monoid.ComLaw.type.
to discover the factory

NB: it is important to restrict with the key fsetU here

HB.about SemiGroup.isCommutativeLaw.Build.

...->
HB.instance Definition _ (T : choiceType) :=
  SemiGroup.isCommutativeLaw.Build _ fsetU (@fsetUC T).


NB: we could have instantiated Monoid.ComLaw first and got Monoid.isLaw for free

*****************************************************************************

compile and goes to the next error

## K/K_def.v

Definition form_eqMixin := EqMixin (compareP eq_form_dec).
Canonical Structure form_eqType := Eval hnf in @EqType form form_eqMixin.
-> ...

look at the changelog for EqMixin

it says use hasDecEq.Build

HB.about hasDecEq.Build

... ->
HB.instance Definition _ := hasDecEq.Build form (compareP eq_form_dec).

*************************************************************************

Definition form_countMixin := PcanCountMixin formChoice.pickleP.
Definition form_choiceMixin := CountChoiceMixin form_countMixin.
Canonical Structure form_ChoiceType := Eval hnf in ChoiceType form form_choiceMixin.
Canonical Structure form_CountType := Eval hnf in CountType form form_countMixin.
->

look at the changelog to discover that PcanCountMixin is now PCanIsCountable

or look at the deprecation message when executing
Definition form_countMixin := PcanCountMixin formChoice.pickleP.


->
HB.instance Definition _ : isCountable form := PCanIsCountable formChoice.pickleP.

NB: this is bad practice to not have the key (here form) appearing explicitly

************************************************************************

# Kstar_def.v

Definition form_eqMixin := EqMixin (compareP eq_form_dec).
Canonical Structure form_eqType := Eval hnf in @EqType form form_eqMixin.

same change as above

****************************************************************************

# gen_def.v


Definition annot_eqMixin := EqMixin (compareP eq_annot_dec).
Canonical Structure annot_eqType := Eval hnf in @EqType annot annot_eqMixin.

**********************************************************

# CTL_def.v

same as above (form)

**************************************************

dags.v

SubP -> eqtype.subP
TODO: change this back

SubK -> subK

******************************************************

# demo.v

move => [p' y]. rewrite /MRel /Mstate (negbTE (root_internal _)) [_ && _]/=.
rewrite orbF.

not terminating compuation

->

rewrite [in X in X <-> _]orbF.


*****************

# PDL_def.v

Definition form_eqMixin := EqMixin (fst Eq.form_prog_dec).
Canonical Structure form_eqType := Eval hnf in @EqType form form_eqMixin.

Definition prog_eqMixin := EqMixin (snd Eq.form_prog_dec).
Canonical Structure prog_eqType := Eval hnf in @EqType prog prog_eqMixin.

->

HB.instance Definition _ := hasDecEq.Build form (fst Eq.form_prog_dec).
 
HB.instance Definition _ := hasDecEq.Build prog (snd Eq.form_prog_dec).
