(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From Corelib Require Export ssreflect.
Global Set SsrOldRewriteGoalsOrder.
Global Set Asymmetric Patterns.
Global Set Bullet Behavior "None".

#[deprecated(since="mathcomp 2.3.0", note="Use `Arguments def : simpl never` instead (should work fine since Coq 8.18).")]
Notation nosimpl t := (nosimpl t).

(**
  Additions to be ported to Corelib ssreflect:
      hide t == t, but hide t displays as <hidden>
     hideT t == t, but both hideT t and its inferred type display as <hidden>
  New ltac views:
      => /#[#hide#]#     := insert hide in the type of the top assumption (and
                        its body if it is a 'let'), so it displays as <hidden>.
      => /#[#let#]#      := if the type (or body) of the top assumption is a
                        'let', make that 'let' the top assumption, e.g.,
                      turn (let n := 1 in m < half n) -> G
                      into let n := 1 in m < half n -> G
      => /#[#fix#]#      := names a 'fix' expression f in the goal G(f), by 
                        replacing the goal with let fx := hide f in G(fx),
                        where fx is a fresh variable, and hide f displays
                        as <hidden>.    
      => /#[#cofix#]#    := similarly, names a 'cofix' expression in the goal.
            
**)
Definition hide {T} t : T := t.
Notation hideT := (@hide (hide _)) (only parsing).
Notation "<hidden >" := (hide _)
  (at level 0, format "<hidden >", only printing) : ssr_scope.

Notation "'[' 'hide' ']'" := (ltac:(
  move; lazymatch goal with
    | |- forall x : ?A, ?G =>      change (forall x : hide A, G)
    | |- let x : ?A := ?a in ?G => change (let x : hide A := @hide A a in G)
    | _ => fail "[hide] : no top assumption"
  end)) (at level 0, only parsing) : ssripat_scope.

Notation "'[' 'let' ']'" := (ltac:(
  move; lazymatch goal with
    | |- forall (H : let x : ?A := ?a in ?T), ?G =>
      change (let x : A := a in forall H : T, G)
    | |- let H : (let x : ?A := ?a in ?T) := ?t in ?G =>
      change (let x : A := a in let H : T := t in G)
    | |- let H : ?T := (let x : ?A := ?a in ?t) in ?G =>
      change (let x : A := a in let H : T := t in G)
    | _ => fail "[let]: top assumption type or body is not a 'let'"
  end)) (at level 0, only parsing) : ssripat_scope.

Notation "'[' 'fix' ']'" := (ltac:(
  match goal with
  | |- context [?t] =>
    is_fix t; let f := fresh "fix" in set f := t; move: @f => /[hide]
  | _ => fail 1 "[fix]: no visible 'fix' in goal"
  end)) (at level 0, only parsing) : ssripat_scope.

Notation "'[' 'cofix' ']'" := (ltac:(
  match goal with
  | |- context [?t] =>
    is_cofix t; let z := fresh "cofix" in set z := t; move: @z => /[hide]
  | _ => fail 1 "[cofix]: no visible 'cofix' in goal"
  end)) (at level 0, only parsing) : ssripat_scope.



  (* code belonging to HB, move there once finalized *************************)

From elpi Require Import elpi.
From HB Require Import structures.

Elpi Tactic HB.share_mixins.
Elpi Accumulate Db hb.db.
Elpi Accumulate lp:{{{{

% this exists in either utils or database...
func list-w-params_list list-w-params mixinname -> list mixinname.
list-w-params_list (w-params.nil _ _ F) R :- pi x\ std.map (F x) triple_1 R.
list-w-params_list (w-params.cons _ _ F) R :- pi x\ list-w-params_list (F x) R.

% [known-mixin S C M MI] looks in C for an instance MI of mixin M on subject S
func known-mixin term, list prop, gref -> term.
known-mixin S Ctx M MI :-
  factory->nparams M NP, !, % workaround bad indexing in HB 1.10.1
  known-mixin.aux M NP S Ctx MI.
func known-mixin.aux mixinname, int, term, list prop -> term.
known-mixin.aux M NP S [def X _ (app[global M|Args]) _|_] X :- std.nth NP Args S1, S = S1, !.
known-mixin.aux M NP S [decl X _ (app[global M|Args])|_] X :- std.nth NP Args S1, S = S1, !.
known-mixin.aux M NP S [_|Ctx] X :- known-mixin.aux M NP S Ctx X.

% [share-dep S C T T1] if T is a known-mixin in C, it returns its entry in C
func share-dep term, list prop, term, mixinname -> term.
share-dep S Ctx _ M X :- known-mixin S Ctx M X, !.
share-dep _ _ X _ X.

% [spill-mixin S C X X1] expects X to be
%  (Pack ... let m1 ... in Class ...)
% and returns
%  let m1 ... in hidden (Pack ... (Class ))
% where type type of each m has shared deps, and all m already in C are
% eliminated
func spill-mixins term, list prop, term -> term.
% drop the let, the mixin is already in the context
spill-mixins S Ctx (app Args) R :-
    std.appendR Head [let _ (app[global M|MArgs]) _ F] Args,
    known-mixin S Ctx M X,
  !,
  % sanity check
  std.nth {factory->nparams M} MArgs S1, !, % workaround bad indexing in HB 1.10.1
  std.assert-ok! (coq.unify-eq S S1) "HB.share_mixins: different subject",
  std.append Head [F X] Args1,
  spill-mixins S Ctx (app Args1) R.
% keep the let, share its deps
spill-mixins S Ctx (app Args) (let N TY1 B F1) :-
  std.appendR Head [let N (app[global M|MArgs]) B F] Args, !,
  % sanity check
  std.split-at {factory->nparams M} MArgs Params [S1|Deps],
  std.assert-ok! (coq.unify-eq S S1) "HB.share_mixins: different subject",
  std.map2 Deps {list-w-params_list {gref->deps M}} (share-dep S Ctx) Deps1,
  TY1 = app[global M| {std.append Params [S|Deps1]} ],
  @pi-def N TY1 B x\
    std.append Head [F x] (Args1 x),
    spill-mixins S [def x N TY1 B|Ctx] (app (Args1 x)) (F1 x).
% remove cast
spill-mixins S Ctx (let _ _ B x\x) Y :- !, spill-mixins S Ctx B Y.
% no more lets, hide the structure def
spill-mixins _ _ X {{ hide lp:X }}.

func canonical-mixin-name term, term -> name.
canonical-mixin-name S (app[global GR|_]) Name :-
  coq.term->string S SS,
  rex.replace " " "_" SS SSS,
  coq.gref->path GR M,
  std.last M MMM,
  coq.id->name {calc (SSS ^ "__" ^ MMM)} Name.

% Tells if a mixin contains data (a field in Type)
pred informative-mixin-field mixinname -> .
informative-mixin-field M :-
  exported-op M C _,
  coq.env.typeof (const C) Ty,
  coq.typecheck-ty Ty U ok,
  U = typ _.

func non-informative term -> .
non-informative (app[global M|_]) :-
  not(informative-mixin-field M).

% Introduces mixins as decl (or def when they are informative)
func intros-mixins term, term -> term.
intros-mixins S (let N TY (let _ TY1 B1 F) G) (app[(fun CN TY1 F1),B1]) :- non-informative TY1, !,
  canonical-mixin-name S TY1 CN,
  @pi-def CN TY1 B1 x\
    intros-mixins S (let N TY (F x) G) (F1 x).
intros-mixins S (let N TY (let _ TY1 B1 F) G) (let CN TY1 {{ hide lp:B1 }} F1) :- !,
  canonical-mixin-name S TY1 CN,
  @pi-def CN TY1 B1 x\
    intros-mixins S (let N TY (F x) G) (F1 x).
intros-mixins _ X {{ _ : lp:X }}.

% Expects the goal to be a let of an HB structure and S the naked subject
% of that structure. It spills all mixins and introduces them in the context
% maximizing sharing
solve (goal Ctx _ (let N Ty Bo F) _ [str "noclear", trm S] as G) GL :-
  spill-mixins S Ctx Bo Bo1,
  (pi x\ non-informative x :- !, fail) ==> intros-mixins S (let N Ty Bo1 F) NT,
  refine NT G GL.
solve (goal Ctx _ (let N Ty Bo F) _ [trm S] as G) GL :-
  spill-mixins S Ctx Bo Bo1,
  intros-mixins S (let N Ty Bo1 F) NT,
  refine NT G GL.
}}}}.

Tactic Notation "HB.share_mixins" open_constr(k) :=
  elpi HB.share_mixins ltac_term:(k).

Tactic Notation "HB.share_mixins_noclear" open_constr(k) :=
  elpi HB.share_mixins "noclear" ltac_term:(k).

Tactic Notation "HB.enrich" ident(k) ident(p) "as" ident(id) ":" uconstr(ty) "with" uconstr_list(b) :=
  let khd := k in
  let k := k p in
  pose id p : ty := ltac:(elpi HB.pack ltac_term:(k) ltac_term_list:(b));
  (* list-w-params_list: avoids a shelved goal... *) let ty' := type of id in unify ty ty'; (* /list-w-params_list *)
  do [ HB.share_mixins (khd _) ] in @id *.

Tactic Notation "HB.enrich" ident(k) ident(p) ":" uconstr(tk) "as" ident(id) ":" uconstr(ty) "with" uconstr_list(b) :=
  let khd := k in
  let k := uconstr:(k p : tk) in
  pose id p : ty := ltac:(elpi HB.pack ltac_term:(k) ltac_term_list:(b));
  (* list-w-params_list: avoids a shelved goal... *) let ty' := type of id in unify ty ty'; (* /list-w-params_list *)
  do [ HB.share_mixins (khd _) ] in @id *.

Tactic Notation "HB.enrich" "(" open_constr(k) ")" "as" ident(id) ":" open_constr(ty) "with" uconstr_list(b) :=
  let k := k in
  pose id : ty := ltac:(elpi HB.pack ltac_term:(k) ltac_term_list:(b));
  (* list-w-params_list: avoids a shelved goal... *) let ty' := type of id in unify ty ty'; (* /list-w-params_list *)
  do [ HB.share_mixins k ] in @id *.

Tactic Notation "HB.enrich" "(" open_constr(k) ")" ":" uconstr(tk) "as" ident(id) ":" open_constr(ty) "with" uconstr_list(b) :=
  let k := uconstr:(k : tk) in
  pose id : ty := ltac:(elpi HB.pack ltac_term:(k) ltac_term_list:(b));
  (* list-w-params_list: avoids a shelved goal... *) let ty' := type of id in unify ty ty'; (* /list-w-params_list *)
  do [ HB.share_mixins k ] in @id *.

Tactic Notation "HB.enrich" ident(k) ":" uconstr(tk) "as" ident(id) ":" open_constr(ty) "with" uconstr_list(b) :=
  let k := uconstr:(k : tk) in
  pose id : ty := ltac:(elpi HB.pack ltac_term:(k) ltac_term_list:(b));
  (* list-w-params_list: avoids a shelved goal... *) let ty' := type of id in unify ty ty'; (* /list-w-params_list *)
  do [ HB.share_mixins k ] in @id *.

Tactic Notation "HB.enrich" ident(k) "as" ident(id) ":" open_constr(ty) "with" uconstr_list(b) :=
  pose id : ty := ltac:(elpi HB.pack ltac_term:(k) ltac_term_list:(b));
  (* list-w-params_list: avoids a shelved goal... *) let ty' := type of id in unify ty ty'; (* /list-w-params_list *)
  do [ HB.share_mixins k ] in @id *.

(*****************************************************************************)
