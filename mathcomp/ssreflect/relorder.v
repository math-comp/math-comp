(* Credit: ported from https://github.com/Coq-Polyhedra/order.                *)
(* Initial authors are X. Allamigeon, Q. Canu, and P.-Y. Strub.               *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq.
From mathcomp Require Import path fintype tuple bigop finset.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "<= y" (at level 35).
Reserved Notation ">= y" (at level 35).
Reserved Notation "< y" (at level 35).
Reserved Notation "> y" (at level 35).
Reserved Notation "<= y :> T" (at level 35, y at next level).
Reserved Notation ">= y :> T" (at level 35, y at next level).
Reserved Notation "< y :> T" (at level 35, y at next level).
Reserved Notation "> y :> T" (at level 35, y at next level).
Reserved Notation "x >=< y" (at level 70, no associativity).
Reserved Notation ">=< y" (at level 35).
Reserved Notation ">=< y :> T" (at level 35, y at next level).
Reserved Notation "x >< y" (at level 70, no associativity).
Reserved Notation ">< x" (at level 35).
Reserved Notation ">< y :> T" (at level 35, y at next level).

Reserved Notation "x < y ?<= 'if' c" (at level 70, y, c at next level,
  format "x '[hv'  <  y '/'  ?<=  'if'  c ']'").
Reserved Notation "x < y ?<= 'if' c :> T" (at level 70, y, c at next level,
  format "x '[hv'  <  y '/'  ?<=  'if'  c  :> T ']'").

(* Reserved notation for lattice operations. *)
Reserved Notation "A `&` B"  (at level 48, left associativity).
Reserved Notation "A `|` B" (at level 52, left associativity).
Reserved Notation "A `\` B" (at level 50, left associativity).
Reserved Notation "~` A" (at level 35, right associativity).

Module RelOrder.

Definition dual_rel (T : Type) (r : rel T) := fun y x => r x y.
Definition dual_bottom (T : Type) (top : T) := top.
Definition dual_top (T : Type) (bottom : T) := bottom.
Definition dual_meet (T : Type) (join : T -> T -> T) := join.
Definition dual_join (T : Type) (meet : T -> T -> T) := meet.

(**************)
(* STRUCTURES *)
(**************)

Module POrder.

Section ClassDef.

Variable T : eqType.

(* TODO: the interface (POrder.order) should not be a primitive record. see:  *)
(* https://github.com/math-comp/math-comp/pull/462#issuecomment-598130155.    *)
Set Primitive Projections.

Record mixin_of (le lt : rel T) := Mixin {
  lt_def : forall x y, lt x y = (y != x) && le x y;
  dlt_def : forall x y, lt y x = (y != x) && le y x;
  lexx : reflexive le;
  le_anti : forall x y, le x y -> le y x -> x = y;
  le_trans : transitive le;
}.

Notation class_of := mixin_of (only parsing).

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  #[canonical=no] class_ : class_of le lt;
}.

Unset Primitive Projections.

Variable (phT : phant T) (ord : order phT).

Definition class : class_of (le ord) (lt ord) :=
  let: Pack _ _ c as ord' := ord in c.

Variable (leT ltT : rel T).

Definition clone c of phant_id class c := @Pack phT leT ltT c.

End ClassDef.

Notation class_of := mixin_of (only parsing).

Module Exports.
Notation "{ 'pOrder' T }" := (order (Phant T))
  (at level 0, format "{ 'pOrder'  T }").
Notation POrder le lt mixin := (@Pack _ (Phant _) le lt mixin).
Notation "[ 'leo:' leT ]" :=
  (@clone _ (Phant _) _ leT _ _ id) (at level 0, format "[ 'leo:'  leT ]").
Notation "[ 'lto:' ltT ]" :=
  (@clone _ (Phant _) _ _ ltT _ id) (at level 0, format "[ 'lto:'  ltT ]").
End Exports.

End POrder.
Import POrder.Exports.

Notation le := POrder.le.
Notation lt := POrder.lt.
Arguments le {T phT} ord x y : rename, simpl never.
Arguments lt {T phT} ord x y : rename, simpl never.

Module Import DualPOrder.

Canonical dual_pOrder (T : eqType) (ord : {pOrder T}) :=
  POrder
    (dual_rel (le ord)) (dual_rel (lt ord))
    (let mixin := POrder.class ord in
     @POrder.Mixin
       T (dual_rel (le ord)) (dual_rel (lt ord))
       (POrder.dlt_def mixin) (POrder.lt_def mixin) (POrder.lexx mixin)
       (fun x y yx xy => POrder.le_anti mixin xy yx)
       (fun y x z xy yz => POrder.le_trans mixin yz xy)).

End DualPOrder.

Module BPOrder.

Section ClassDef.

Variable T : eqType.

Definition mixin_of (ord : {pOrder T}) (bottom : T) :=
  forall x, le ord bottom x.

Set Primitive Projections.

Record class_of (le lt : rel T) (bottom : T) := Class {
  base : POrder.class_of le lt;
  mixin : mixin_of (POrder.Pack _ base) bottom;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  bottom : T;
  #[canonical=no] class_ : class_of le lt bottom;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> POrder.class_of.

Variable (phT : phant T) (ord : order phT).

Definition class : class_of (le ord) (lt ord) (bottom ord) :=
  let: Pack _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.

Variable (leT ltT : rel T) (bottomT : T).

Definition clone c of phant_id class c := @Pack phT leT ltT bottomT c.

Definition pack (b0 : POrder.class_of leT ltT)
                (m0 : mixin_of (POrder.Pack _ b0) bottomT) :=
  fun (b : POrder.class_of leT ltT)            & phant_id b0 b =>
  fun (m : mixin_of (POrder.Pack _ b) bottomT) & phant_id m0 m =>
  @Pack phT leT ltT bottomT (Class m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> POrder.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Notation "{ 'bPOrder' T }" := (order (Phant T))
  (at level 0, format "{ 'bPOrder'  T }").
Notation BPOrder le lt bottom mixin :=
  (@pack _ (Phant _) le lt bottom _ mixin _ id _ id).
Notation "[ 'bPOrder' 'of' le ]" :=
  (@clone _ (Phant _) _ le (nosimpl _) (nosimpl _) _ id)
  (at level 0, format "[ 'bPOrder'  'of'  le ]").
End Exports.

End BPOrder.
Import BPOrder.Exports.

Notation bottom := BPOrder.bottom.
Arguments bottom {T phT} ord : rename, simpl never.

Module TPOrder.

Section ClassDef.

Variable T : eqType.

Definition mixin_of (ord : {pOrder T}) (top : T) := forall x, le ord x top.

Set Primitive Projections.

Record class_of (le lt : rel T) (top : T) := Class {
  base : POrder.class_of le lt;
  mixin : mixin_of (POrder.Pack _ base) top;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  top : T;
  #[canonical=no] class_ : class_of le lt top;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> POrder.class_of.

Variable (phT : phant T) (ord : order phT).

Definition class : class_of (le ord) (lt ord) (top ord) :=
  let: Pack _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.

Variable (leT ltT : rel T) (topT : T).

Definition clone c of phant_id class c := @Pack phT leT ltT topT c.

Definition pack (b0 : POrder.class_of leT ltT)
                (m0 : mixin_of (POrder.Pack _ b0) topT) :=
  fun (b : POrder.class_of leT ltT)         & phant_id b0 b =>
  fun (m : mixin_of (POrder.Pack _ b) topT) & phant_id m0 m =>
  @Pack phT leT ltT topT (Class m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> POrder.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Notation "{ 'tPOrder' T }" := (order (Phant T))
  (at level 0, format "{ 'tPOrder'  T }").
Notation TPOrder le lt top mixin :=
  (@pack _ (Phant _) le lt top _ mixin _ id _ id).
Notation "[ 'tPOrder' 'of' le ]" :=
  (@clone _ (Phant _) _ le (nosimpl _) (nosimpl _) _ id)
  (at level 0, format "[ 'tPOrder'  'of'  le ]").
End Exports.

End TPOrder.
Import TPOrder.Exports.

Notation top := TPOrder.top.
Arguments top {T phT} ord : rename, simpl never.

Module TBPOrder.

Section ClassDef.

Variable T : eqType.

Set Primitive Projections.

Record class_of (le lt : rel T) (bottom top : T) := Class {
  base : BPOrder.class_of le lt bottom;
  mixin : TPOrder.mixin_of (POrder.Pack _ base) top;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  bottom : T;
  top : T;
  #[canonical=no] class_ : class_of le lt bottom top;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> BPOrder.class_of.
Local Coercion base2 le lt bottom top (c : class_of le lt bottom top) :
  TPOrder.class_of le lt top := TPOrder.Class (mixin c).

Variable (phT : phant T) (ord : order phT).

Definition class : class_of (le ord) (lt ord) (bottom ord) (top ord) :=
  let: Pack _ _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.
Definition bPOrder := @BPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) class.
Definition tPOrder := @TPOrder.Pack _ phT (le ord) (lt ord) (top ord) class.
(* NB: [nosimpl] is needed to let the [Canonical] command ignore a field.     *)
Definition bP_tPOrder :=
  @TPOrder.Pack _ phT (BPOrder.le bPOrder) (BPOrder.lt bPOrder)
                ((* hack! *) nosimpl (top ord)) class.

Variable (leT ltT : rel T) (bottomT topT : T).

Definition pack :=
  fun (bord : BPOrder.order phT) (b : BPOrder.class_of leT ltT bottomT)
      & phant_id (BPOrder.class bord) b =>
  fun (mord : TPOrder.order phT) m
      & phant_id (TPOrder.class mord) (TPOrder.Class (base := b) m) =>
  @Pack phT leT ltT bottomT topT (Class (base := b) m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> BPOrder.class_of.
Coercion base2 : class_of >-> TPOrder.class_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Coercion bPOrder : order >-> BPOrder.order.
Canonical bPOrder.
Coercion tPOrder : order >-> TPOrder.order.
Canonical tPOrder.
Canonical bP_tPOrder.
Notation "{ 'tbPOrder' T }" := (order (Phant T))
  (at level 0, format "{ 'tbPOrder'  T }").
Notation "[ 'tbPOrder' 'of' le ]" :=
  (@pack _ (Phant _) le (nosimpl _) (nosimpl _) (nosimpl _) _ _ id _ _ id)
  (at level 0, format "[ 'tbPOrder'  'of'  le ]").
End Exports.

End TBPOrder.
Import TBPOrder.Exports.

Module Meet.

Section ClassDef.

Variable T : eqType.

Set Primitive Projections.

Record mixin_of (ord : {pOrder T}) (meet : T -> T -> T) := Mixin {
  meetC : commutative meet;
  meetA : associative meet;
  leEmeet : forall x y, (le ord x y) = (meet x y == x);
}.

Record class_of (le lt : rel T) (meet : T -> T -> T) := Class {
  base : POrder.class_of le lt;
  mixin : mixin_of (POrder.Pack _ base) meet;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  #[canonical=no] class_ : class_of le lt meet;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> POrder.class_of.

Variable (phT : phant T) (ord : order phT).

Definition class : class_of (le ord) (lt ord) (meet ord) :=
  let: Pack _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.

Variable (leT ltT : rel T) (meetT : T -> T -> T).

Definition clone c of phant_id class c := @Pack phT leT ltT meetT c.

Definition pack (b0 : POrder.class_of leT ltT)
                (m0 : mixin_of (POrder.Pack _ b0) meetT) :=
  fun (b : POrder.class_of leT ltT)          & phant_id b0 b =>
  fun (m : mixin_of (POrder.Pack _ b) meetT) & phant_id m0 m =>
  @Pack phT leT ltT meetT (Class m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> POrder.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Notation "{ 'meetOrder' T }" := (order (Phant T))
  (at level 0, format "{ 'meetOrder'  T }").
Notation MeetOrder le lt meet mixin :=
  (@pack _ (Phant _) le lt meet _ mixin _ id _ id).
Notation "[ 'meetOrder' 'of' le ]" :=
  (@clone _ (Phant _) _ le (nosimpl _) (nosimpl _) _ id)
  (at level 0, format "[ 'meetOrder'  'of'  le ]").
End Exports.

End Meet.
Import Meet.Exports.

Notation meet := Meet.meet.
Arguments meet {T phT} ord x y : rename, simpl never.

Module BMeet.

Section ClassDef.

Variable T : eqType.

Set Primitive Projections.

Record class_of (le lt : rel T) (meet : T -> T -> T) (bottom : T) := Class {
  base : Meet.class_of le lt meet;
  mixin : BPOrder.mixin_of (POrder.Pack _ base) bottom;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  bottom : T;
  #[canonical=no] class_ : class_of le lt meet bottom;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> Meet.class_of.
Local Coercion base2 le lt meet bottom (c : class_of le lt meet bottom) :
  BPOrder.class_of le lt bottom := BPOrder.Class (mixin c).

Variable (phT : phant T) (ord : order phT).

Definition class : class_of (le ord) (lt ord) (meet ord) (bottom ord) :=
  let: Pack _ _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.
Definition bPOrder := @BPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) class.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) class.
Definition bP_meetOrder :=
  @Meet.Pack
    _ phT (BPOrder.le bPOrder) (BPOrder.lt bPOrder) (nosimpl (meet ord)) class.

Variable (leT ltT : rel T) (meetT : T -> T -> T) (bottomT : T).

Definition pack :=
  fun (bord : Meet.order phT) (b : Meet.class_of leT ltT meetT)
      & phant_id (Meet.class bord) b =>
  fun (mord : BPOrder.order phT) m
      & phant_id (BPOrder.class mord) (BPOrder.Class (base := b) m) =>
  @Pack phT leT ltT meetT bottomT (Class (base := b) m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> Meet.class_of.
Coercion base2 : class_of >-> BPOrder.class_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Coercion bPOrder : order >-> BPOrder.order.
Canonical bPOrder.
Coercion meetOrder : order >-> Meet.order.
Canonical meetOrder.
Canonical bP_meetOrder.
Notation "{ 'bMeetOrder' T }" := (order (Phant T))
  (at level 0, format "{ 'bMeetOrder'  T }").
Notation "[ 'bMeetOrder' 'of' le ]" :=
  (@pack _ (Phant _) le (nosimpl _) (nosimpl _) (nosimpl _) _ _ id _ _ id)
  (at level 0, format "[ 'bMeetOrder'  'of'  le ]").
End Exports.

End BMeet.
Import BMeet.Exports.

Module TMeet.

Section ClassDef.

Variable T : eqType.

Set Primitive Projections.

Record class_of (le lt : rel T) (meet : T -> T -> T) (top : T) := Class {
  base : Meet.class_of le lt meet;
  mixin : TPOrder.mixin_of (POrder.Pack _ base) top;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  top : T;
  #[canonical=no] class_ : class_of le lt meet top;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> Meet.class_of.
Local Coercion base2 le lt meet top (c : class_of le lt meet top) :
  TPOrder.class_of le lt top := TPOrder.Class (mixin c).

Variable (phT : phant T) (ord : order phT).

Definition class : class_of (le ord) (lt ord) (meet ord) (top ord) :=
  let: Pack _ _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.
Definition tPOrder := @TPOrder.Pack _ phT (le ord) (lt ord) (top ord) class.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) class.
Definition tP_meetOrder :=
  @Meet.Pack
    _ phT (TPOrder.le tPOrder) (TPOrder.lt tPOrder) (nosimpl (meet ord)) class.

Variable (leT ltT : rel T) (meetT : T -> T -> T) (topT : T).

Definition pack :=
  fun (bord : Meet.order phT) (b : Meet.class_of leT ltT meetT)
      & phant_id (Meet.class bord) b =>
  fun (mord : TPOrder.order phT) m
      & phant_id (TPOrder.class mord) (TPOrder.Class (base := b) m) =>
  @Pack phT leT ltT meetT topT (Class (base := b) m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> Meet.class_of.
Coercion base2 : class_of >-> TPOrder.class_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Coercion tPOrder : order >-> TPOrder.order.
Canonical tPOrder.
Coercion meetOrder : order >-> Meet.order.
Canonical meetOrder.
Canonical tP_meetOrder.
Notation "{ 'tMeetOrder' T }" := (order (Phant T))
  (at level 0, format "{ 'tMeetOrder'  T }").
Notation "[ 'tMeetOrder' 'of' le ]" :=
  (@pack _ (Phant _) le (nosimpl _) (nosimpl _) (nosimpl _) _ _ id _ _ id)
  (at level 0, format "[ 'tMeetOrder'  'of'  le ]").
End Exports.

End TMeet.
Import TMeet.Exports.

Module TBMeet.

Section ClassDef.

Variable T : eqType.

Set Primitive Projections.

Record class_of (le lt : rel T) (meet : T -> T -> T) (bottom top : T) := Class {
  base : BMeet.class_of le lt meet bottom;
  mixin : TPOrder.mixin_of (POrder.Pack _ base) top;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  bottom : T;
  top : T;
  #[canonical=no] class_ : class_of le lt meet bottom top;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> BMeet.class_of.
Local Coercion base2 le lt meet bottom top
                     (c : class_of le lt meet bottom top) :
  TMeet.class_of le lt meet top := TMeet.Class (mixin c).
Local Coercion base3 le lt meet bottom top
                     (c : class_of le lt meet bottom top) :
  TBPOrder.class_of le lt bottom top := TBPOrder.Class (base := c) (mixin c).

Variable (phT : phant T) (ord : order phT).

Definition class :
  class_of (le ord) (lt ord) (meet ord) (bottom ord) (top ord) :=
  let: Pack _ _ _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.
Definition bPOrder := @BPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) class.
Definition tPOrder := @TPOrder.Pack _ phT (le ord) (lt ord) (top ord) class.
Definition tbPOrder :=
  @TBPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) (top ord) class.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) class.
Definition bMeetOrder :=
  @BMeet.Pack _ phT (le ord) (lt ord) (meet ord) (bottom ord) class.
Definition tMeetOrder :=
  @TMeet.Pack _ phT (le ord) (lt ord) (meet ord) (top ord) class.
Definition bP_tMeetOrder :=
  @TMeet.Pack _ phT (BPOrder.le bPOrder) (BPOrder.lt bPOrder)
              (nosimpl (meet ord)) (nosimpl (top ord)) class.
Definition tP_bMeetOrder :=
  @BMeet.Pack _ phT (TPOrder.le tPOrder) (TPOrder.lt tPOrder)
              (nosimpl (meet ord)) (nosimpl (bottom ord)) class.
Definition tbP_meetOrder :=
  @Meet.Pack _ phT (TBPOrder.le tbPOrder) (TBPOrder.lt tbPOrder)
             (nosimpl (meet ord)) class.
Definition tbP_bMeetOrder :=
  @BMeet.Pack _ phT (TBPOrder.le tbPOrder) (TBPOrder.lt tbPOrder)
              (nosimpl (meet ord)) (TBPOrder.bottom tbPOrder) class.
Definition tbP_tMeetOrder :=
  @TMeet.Pack _ phT (TBPOrder.le tbPOrder) (TBPOrder.lt tbPOrder)
              (nosimpl (meet ord)) (TBPOrder.top tbPOrder) class.
Definition bMeet_tMeetOrder :=
  @TMeet.Pack _ phT (BMeet.le bMeetOrder) (BMeet.lt bMeetOrder)
              (BMeet.meet bMeetOrder) (nosimpl (top ord)) class.

Variable (leT ltT : rel T) (meetT : T -> T -> T) (bottomT topT : T).

Definition pack :=
  fun (bord : BMeet.order phT) (b : BMeet.class_of leT ltT meetT bottomT)
      & phant_id (BMeet.class bord) b =>
  fun (mord : TPOrder.order phT) m
      & phant_id (TPOrder.class mord) (TPOrder.Class (base := b) m) =>
  @Pack phT leT ltT meetT bottomT topT (Class (base := b) m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> BMeet.class_of.
Coercion base2 : class_of >-> TMeet.class_of.
Coercion base3 : class_of >-> TBPOrder.class_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Coercion bPOrder : order >-> BPOrder.order.
Canonical bPOrder.
Coercion tPOrder : order >-> TPOrder.order.
Canonical tPOrder.
Coercion tbPOrder : order >-> TBPOrder.order.
Canonical tbPOrder.
Coercion meetOrder : order >-> Meet.order.
Canonical meetOrder.
Coercion bMeetOrder : order >-> BMeet.order.
Canonical bMeetOrder.
Coercion tMeetOrder : order >-> TMeet.order.
Canonical tMeetOrder.
Canonical bP_tMeetOrder.
Canonical tP_bMeetOrder.
Canonical tbP_meetOrder.
Canonical tbP_bMeetOrder.
Canonical tbP_tMeetOrder.
Canonical bMeet_tMeetOrder.
Notation "{ 'tbMeetOrder' T }" := (order (Phant T))
  (at level 0, format "{ 'tbMeetOrder'  T }").
Notation "[ 'tbMeetOrder' 'of' le ]" :=
  (@pack _ (Phant _) le (nosimpl _) (nosimpl _) (nosimpl _) (nosimpl _)
         _ _ id _ _ id)
  (at level 0, format "[ 'tbMeetOrder'  'of'  le ]").
End Exports.

End TBMeet.
Import TBMeet.Exports.

Module Join.

Section ClassDef.

Variable T : eqType.

Definition mixin_of (ord : {pOrder T}) := Meet.mixin_of (dual_pOrder ord).

Set Primitive Projections.

Record class_of (le lt : rel T) (join : T -> T -> T) := Class {
  base : POrder.class_of le lt;
  mixin : mixin_of (POrder.Pack _ base) join;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  join : T -> T -> T;
  #[canonical=no] class_ : class_of le lt join;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> POrder.class_of.

Variable (phT : phant T) (ord : order phT).

Definition class : class_of (le ord) (lt ord) (join ord) :=
  let: Pack _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.

Variable (leT ltT : rel T) (joinT : T -> T -> T).

Definition clone c of phant_id class c := @Pack phT leT ltT joinT c.

Definition pack (b0 : POrder.class_of leT ltT)
                (m0 : mixin_of (POrder.Pack _ b0) joinT) :=
  fun (b : POrder.class_of leT ltT)          & phant_id b0 b =>
  fun (m : mixin_of (POrder.Pack _ b) joinT) & phant_id m0 m =>
  @Pack phT leT ltT joinT (Class m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> POrder.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Notation "{ 'joinOrder' T }" := (order (Phant T))
  (at level 0, format "{ 'joinOrder'  T }").
Notation JoinOrder le lt join mixin :=
  (@pack _ (Phant _) le lt join _ mixin _ id _ id).
Notation "[ 'joinOrder' 'of' le ]" :=
  (@clone _ (Phant _) _ le (nosimpl _) (nosimpl _) _ id)
  (at level 0, format "[ 'joinOrder'  'of'  le ]").
End Exports.

End Join.
Import Join.Exports.

Notation join := Join.join.
Arguments join {T phT} ord x y : rename, simpl never.

Module BJoin.

Section ClassDef.

Variable T : eqType.

Set Primitive Projections.

Record class_of (le lt : rel T) (join : T -> T -> T) (bottom : T) := Class {
  base : Join.class_of le lt join;
  mixin : BPOrder.mixin_of (POrder.Pack _ base) bottom;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  join : T -> T -> T;
  bottom : T;
  #[canonical=no] class_ : class_of le lt join bottom;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> Join.class_of.
Local Coercion base2 le lt join bottom (c : class_of le lt join bottom) :
  BPOrder.class_of le lt bottom := BPOrder.Class (mixin c).

Variable (phT : phant T) (ord : order phT).

Definition class : class_of (le ord) (lt ord) (join ord) (bottom ord) :=
  let: Pack _ _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.
Definition bPOrder := @BPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) class.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) class.
Definition bP_joinOrder :=
  @Join.Pack
    _ phT (BPOrder.le bPOrder) (BPOrder.lt bPOrder) (nosimpl (join ord)) class.

Variable (leT ltT : rel T) (joinT : T -> T -> T) (bottomT : T).

Definition pack :=
  fun (bord : Join.order phT) (b : Join.class_of leT ltT joinT)
      & phant_id (Join.class bord) b =>
  fun (mord : BPOrder.order phT) m
      & phant_id (BPOrder.class mord) (BPOrder.Class (base := b) m) =>
  @Pack phT leT ltT joinT bottomT (Class (base := b) m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> Join.class_of.
Coercion base2 : class_of >-> BPOrder.class_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Coercion bPOrder : order >-> BPOrder.order.
Canonical bPOrder.
Coercion joinOrder : order >-> Join.order.
Canonical joinOrder.
Canonical bP_joinOrder.
Notation "{ 'bJoinOrder' T }" := (order (Phant T))
  (at level 0, format "{ 'bJoinOrder'  T }").
Notation "[ 'bJoinOrder' 'of' le ]" :=
  (@pack _ (Phant _) le (nosimpl _) (nosimpl _) (nosimpl _) _ _ id _ _ id)
  (at level 0, format "[ 'bJoinOrder'  'of'  le ]").
End Exports.

End BJoin.
Import BJoin.Exports.

Module TJoin.

Section ClassDef.

Variable T : eqType.

Set Primitive Projections.

Record class_of (le lt : rel T) (join : T -> T -> T) (top : T) := Class {
  base : Join.class_of le lt join;
  mixin : TPOrder.mixin_of (POrder.Pack _ base) top;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  join : T -> T -> T;
  top : T;
  #[canonical=no] class_ : class_of le lt join top;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> Join.class_of.
Local Coercion base2 le lt join top (c : class_of le lt join top) :
  TPOrder.class_of le lt top := TPOrder.Class (mixin c).

Variable (phT : phant T) (ord : order phT).

Definition class : class_of (le ord) (lt ord) (join ord) (top ord) :=
  let: Pack _ _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.
Definition tPOrder := @TPOrder.Pack _ phT (le ord) (lt ord) (top ord) class.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) class.
Definition tP_joinOrder :=
  @Join.Pack
    _ phT (TPOrder.le tPOrder) (TPOrder.lt tPOrder) (nosimpl (join ord)) class.

Variable (leT ltT : rel T) (joinT : T -> T -> T) (topT : T).

Definition pack :=
  fun (bord : Join.order phT) (b : Join.class_of leT ltT joinT)
      & phant_id (Join.class bord) b =>
  fun (mord : TPOrder.order phT) m
      & phant_id (TPOrder.class mord) (TPOrder.Class (base := b) m) =>
  @Pack phT leT ltT joinT topT (Class (base := b) m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> Join.class_of.
Coercion base2 : class_of >-> TPOrder.class_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Coercion tPOrder : order >-> TPOrder.order.
Canonical tPOrder.
Coercion joinOrder : order >-> Join.order.
Canonical joinOrder.
Canonical tP_joinOrder.
Notation "{ 'tJoinOrder' T }" := (order (Phant T))
  (at level 0, format "{ 'tJoinOrder'  T }").
Notation "[ 'tJoinOrder' 'of' le ]" :=
  (@pack _ (Phant _) le (nosimpl _) (nosimpl _) (nosimpl _) _ _ id _ _ id)
  (at level 0, format "[ 'tJoinOrder'  'of'  le ]").
End Exports.

End TJoin.
Import TJoin.Exports.

Module TBJoin.

Section ClassDef.

Variable T : eqType.

Set Primitive Projections.

Record class_of (le lt : rel T) (join : T -> T -> T) (bottom top : T) := Class {
  base : BJoin.class_of le lt join bottom;
  mixin : TPOrder.mixin_of (POrder.Pack _ base) top;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  join : T -> T -> T;
  bottom : T;
  top : T;
  #[canonical=no] class_ : class_of le lt join bottom top;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> BJoin.class_of.
Local Coercion base2 le lt join bottom top
                     (c : class_of le lt join bottom top) :
  TJoin.class_of le lt join top := TJoin.Class (mixin c).
Local Coercion base3 le lt join bottom top
                     (c : class_of le lt join bottom top) :
  TBPOrder.class_of le lt bottom top := TBPOrder.Class (base := c) (mixin c).

Variable (phT : phant T).
Variable (ord : order phT).

Definition class :
  class_of (le ord) (lt ord) (join ord) (bottom ord) (top ord) :=
  let: Pack _ _ _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.
Definition bPOrder := @BPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) class.
Definition tPOrder := @TPOrder.Pack _ phT (le ord) (lt ord) (top ord) class.
Definition tbPOrder :=
  @TBPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) (top ord) class.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) class.
Definition bJoinOrder :=
  @BJoin.Pack _ phT (le ord) (lt ord) (join ord) (bottom ord) class.
Definition tJoinOrder :=
  @TJoin.Pack _ phT (le ord) (lt ord) (join ord) (top ord) class.
Definition bP_tJoinOrder :=
  @TJoin.Pack _ phT (BPOrder.le bPOrder) (BPOrder.lt bPOrder)
              (nosimpl (join ord)) (nosimpl (top ord)) class.
Definition tP_bJoinOrder :=
  @BJoin.Pack _ phT (TPOrder.le tPOrder) (TPOrder.lt tPOrder)
              (nosimpl (join ord)) (nosimpl (bottom ord)) class.
Definition tbP_joinOrder :=
  @Join.Pack _ phT (TBPOrder.le tbPOrder) (TBPOrder.lt tbPOrder)
             (nosimpl (join ord)) class.
Definition tbP_bJoinOrder :=
  @BJoin.Pack _ phT (TBPOrder.le tbPOrder) (TBPOrder.lt tbPOrder)
              (nosimpl (join ord)) (TBPOrder.bottom tbPOrder) class.
Definition tbP_tJoinOrder :=
  @TJoin.Pack _ phT (TBPOrder.le tbPOrder) (TBPOrder.lt tbPOrder)
              (nosimpl (join ord)) (TBPOrder.top tbPOrder) class.
Definition bJoin_tJoinOrder :=
  @TJoin.Pack _ phT (BJoin.le bJoinOrder) (BJoin.lt bJoinOrder)
              (BJoin.join bJoinOrder) (nosimpl (top ord)) class.

Variable (leT ltT : rel T) (joinT : T -> T -> T) (bottomT topT : T).

Definition pack :=
  fun (bord : BJoin.order phT) (b : BJoin.class_of leT ltT joinT bottomT)
      & phant_id (BJoin.class bord) b =>
  fun (mord : TPOrder.order phT) m
      & phant_id (TPOrder.class mord) (TPOrder.Class (base := b) m) =>
  @Pack phT leT ltT joinT bottomT topT (Class (base := b) m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> BJoin.class_of.
Coercion base2 : class_of >-> TJoin.class_of.
Coercion base3 : class_of >-> TBPOrder.class_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Coercion bPOrder : order >-> BPOrder.order.
Canonical bPOrder.
Coercion tPOrder : order >-> TPOrder.order.
Canonical tPOrder.
Coercion tbPOrder : order >-> TBPOrder.order.
Canonical tbPOrder.
Coercion joinOrder : order >-> Join.order.
Canonical joinOrder.
Coercion bJoinOrder : order >-> BJoin.order.
Canonical bJoinOrder.
Coercion tJoinOrder : order >-> TJoin.order.
Canonical tJoinOrder.
Canonical bP_tJoinOrder.
Canonical tP_bJoinOrder.
Canonical tbP_joinOrder.
Canonical tbP_bJoinOrder.
Canonical tbP_tJoinOrder.
Canonical bJoin_tJoinOrder.
Notation "{ 'tbJoinOrder' T }" := (order (Phant T))
  (at level 0, format "{ 'tbJoinOrder'  T }").
Notation "[ 'tbJoinOrder' 'of' le ]" :=
  (@pack _ (Phant _) le (nosimpl _) (nosimpl _) (nosimpl _) (nosimpl _)
         _ _ id _ _ id)
  (at level 0, format "[ 'tbJoinOrder'  'of'  le ]").
End Exports.

End TBJoin.
Import TBJoin.Exports.

Module Lattice.

Section ClassDef.

Variable T : eqType.

Set Primitive Projections.

Record class_of (le lt : rel T) (meet join : T -> T -> T) := Class {
  base : Meet.class_of le lt meet;
  mixin : Join.mixin_of (POrder.Pack _ base) join;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  join : T -> T -> T;
  #[canonical=no] class_ : class_of le lt meet join;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> Meet.class_of.
Local Coercion base2 le lt meet join (c : class_of le lt meet join) :
  Join.class_of le lt join := Join.Class (mixin c).

Variable (phT : phant T) (ord : order phT).

Definition class : class_of (le ord) (lt ord) (meet ord) (join ord) :=
  let: Pack _ _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) class.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) class.
Definition meet_joinOrder :=
  @Join.Pack
    _ phT (Meet.le meetOrder) (Meet.lt meetOrder) (nosimpl (join ord)) class.

Variable (leT ltT : rel T) (meetT joinT : T -> T -> T).

Definition pack :=
  fun (bord : Meet.order phT) (b : Meet.class_of leT ltT meetT)
      & phant_id (Meet.class bord) b =>
  fun (mord : Join.order phT) m
      & phant_id (Join.class mord) (Join.Class (base := b) m) =>
  @Pack phT leT ltT meetT joinT (Class (base := b) m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> Meet.class_of.
Coercion base2 : class_of >-> Join.class_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Coercion meetOrder : order >-> Meet.order.
Canonical meetOrder.
Coercion joinOrder : order >-> Join.order.
Canonical joinOrder.
Canonical meet_joinOrder.
Notation "{ 'lattice' T }" := (order (Phant T))
  (at level 0, format "{ 'lattice'  T }").
Notation "[ 'lattice' 'of' le ]" :=
  (@pack _ (Phant _) le (nosimpl _) (nosimpl _) (nosimpl _) _ _ id _ _ id)
  (at level 0, format "[ 'lattice'  'of'  le ]").
End Exports.

End Lattice.
Import Lattice.Exports.

Module BLattice.

Section ClassDef.

Variable T : eqType.

Set Primitive Projections.

Record class_of (le lt : rel T) (meet join : T -> T -> T) (bottom : T) :=
  Class {
  base : Lattice.class_of le lt meet join;
  mixin : BPOrder.mixin_of (POrder.Pack _ base) bottom;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  join : T -> T -> T;
  bottom : T;
  #[canonical=no] class_ : class_of le lt meet join bottom;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> Lattice.class_of.
Local Coercion base2 le lt meet join bottom
                     (c : class_of le lt meet join bottom) :
  BMeet.class_of le lt meet bottom := BMeet.Class (mixin c).
Local Coercion base3 le lt meet join bottom
                     (c : class_of le lt meet join bottom) :
  BJoin.class_of le lt join bottom := BJoin.Class (base := c) (mixin c).

Variable (phT : phant T) (ord : order phT).

Definition class :
  class_of (le ord) (lt ord) (meet ord) (join ord) (bottom ord) :=
  let: Pack _ _ _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.
Definition bPOrder := @BPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) class.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) class.
Definition bMeetOrder :=
  @BMeet.Pack _ phT (le ord) (lt ord) (meet ord) (bottom ord) class.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) class.
Definition bJoinOrder :=
  @BJoin.Pack _ phT (le ord) (lt ord) (join ord) (bottom ord) class.
Definition lattice :=
  @Lattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) class.
Definition meet_bJoinOrder :=
  @BJoin.Pack _ phT (Meet.le meetOrder) (Meet.lt meetOrder)
              (nosimpl (join ord)) (nosimpl (bottom ord)) class.
Definition join_bMeetOrder :=
  @BMeet.Pack _ phT (Join.le joinOrder) (Join.lt joinOrder)
              (nosimpl (meet ord)) (nosimpl (bottom ord)) class.
Definition bMeet_bJoinOrder :=
  @BJoin.Pack _ phT (BMeet.le bMeetOrder) (BMeet.lt bMeetOrder)
              (nosimpl (join ord)) (BMeet.bottom bMeetOrder) class.
Definition lattice_bPOrder :=
  @BPOrder.Pack _ phT (Lattice.le lattice) (Lattice.lt lattice)
                (nosimpl (bottom ord)) class.
Definition lattice_bMeetOrder :=
  @BMeet.Pack _ phT (Lattice.le lattice) (Lattice.lt lattice)
              (Lattice.meet lattice) (nosimpl (bottom ord)) class.
Definition lattice_bJoinOrder :=
  @BJoin.Pack _ phT (Lattice.le lattice) (Lattice.lt lattice)
              (Lattice.join lattice) (nosimpl (bottom ord)) class.

Variable (leT ltT : rel T) (meetT joinT : T -> T -> T) (bottomT : T).

Definition pack :=
  fun (bord : Lattice.order phT) (b : Lattice.class_of leT ltT meetT joinT)
      & phant_id (Lattice.class bord) b =>
  fun (mord : BPOrder.order phT) m
      & phant_id (BPOrder.class mord) (BPOrder.Class (base := b) m) =>
  @Pack phT leT ltT meetT joinT bottomT (Class (base := b) m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> Lattice.class_of.
Coercion base2 : class_of >-> BMeet.class_of.
Coercion base3 : class_of >-> BJoin.class_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Coercion bPOrder : order >-> BPOrder.order.
Canonical bPOrder.
Coercion meetOrder : order >-> Meet.order.
Canonical meetOrder.
Coercion bMeetOrder : order >-> BMeet.order.
Canonical bMeetOrder.
Coercion joinOrder : order >-> Join.order.
Canonical joinOrder.
Coercion bJoinOrder : order >-> BJoin.order.
Canonical bJoinOrder.
Coercion lattice : order >-> Lattice.order.
Canonical lattice.
Canonical meet_bJoinOrder.
Canonical join_bMeetOrder.
Canonical bMeet_bJoinOrder.
Canonical lattice_bPOrder.
Canonical lattice_bMeetOrder.
Canonical lattice_bJoinOrder.

Notation "{ 'bLattice' T }" := (order (Phant T))
  (at level 0, format "{ 'bLattice'  T }").
Notation "[ 'bLattice' 'of' le ]" :=
  (@pack _ (Phant _) le (nosimpl _) (nosimpl _) (nosimpl _) (nosimpl _)
         _ _ id _ _ id)
  (at level 0, format "[ 'bLattice'  'of'  le ]").
End Exports.

End BLattice.
Import BLattice.Exports.

Module TLattice.

Section ClassDef.

Variable T : eqType.

Set Primitive Projections.

Record class_of (le lt : rel T) (meet join : T -> T -> T) (top : T) := Class {
  base : Lattice.class_of le lt meet join;
  mixin : TPOrder.mixin_of (POrder.Pack _ base) top;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  join : T -> T -> T;
  top : T;
  #[canonical=no] class_ : class_of le lt meet join top;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> Lattice.class_of.
Local Coercion base2 le lt meet join top (c : class_of le lt meet join top) :
  TMeet.class_of le lt meet top := TMeet.Class (mixin c).
Local Coercion base3 le lt meet join top (c : class_of le lt meet join top) :
  TJoin.class_of le lt join top := TJoin.Class (base := c) (mixin c).

Variable (phT : phant T) (ord : order phT).

Definition class : class_of (le ord) (lt ord) (meet ord) (join ord) (top ord) :=
  let: Pack _ _ _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.
Definition tPOrder := @TPOrder.Pack _ phT (le ord) (lt ord) (top ord) class.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) class.
Definition tMeetOrder :=
  @TMeet.Pack _ phT (le ord) (lt ord) (meet ord) (top ord) class.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) class.
Definition tJoinOrder :=
  @TJoin.Pack _ phT (le ord) (lt ord) (join ord) (top ord) class.
Definition lattice :=
  @Lattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) class.
Definition meet_tJoinOrder :=
  @TJoin.Pack _ phT (Meet.le meetOrder) (Meet.lt meetOrder)
              (nosimpl (join ord)) (nosimpl (top ord)) class.
Definition join_tMeetOrder :=
  @TMeet.Pack _ phT (Join.le joinOrder) (Join.lt joinOrder)
              (nosimpl (meet ord)) (nosimpl (top ord)) class.
Definition tMeet_tJoinOrder :=
  @TJoin.Pack _ phT (TMeet.le tMeetOrder) (TMeet.lt tMeetOrder)
              (nosimpl (join ord)) (TMeet.top tMeetOrder) class.
Definition lattice_tPOrder :=
  @TPOrder.Pack _ phT (Lattice.le lattice) (Lattice.lt lattice)
                (nosimpl (top ord)) class.
Definition lattice_tMeetOrder :=
  @TMeet.Pack _ phT (Lattice.le lattice) (Lattice.lt lattice)
              (Lattice.meet lattice) (nosimpl (top ord)) class.
Definition lattice_tJoinOrder :=
  @TJoin.Pack _ phT (Lattice.le lattice) (Lattice.lt lattice)
              (Lattice.join lattice) (nosimpl (top ord)) class.

Variable (leT ltT : rel T) (meetT joinT : T -> T -> T) (topT : T).

Definition pack :=
  fun (bord : Lattice.order phT) (b : Lattice.class_of leT ltT meetT joinT)
      & phant_id (Lattice.class bord) b =>
  fun (mord : TPOrder.order phT) m
      & phant_id (TPOrder.class mord) (TPOrder.Class (base := b) m) =>
  @Pack phT leT ltT meetT joinT topT (Class (base := b) m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> Lattice.class_of.
Coercion base2 : class_of >-> TMeet.class_of.
Coercion base3 : class_of >-> TJoin.class_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Coercion tPOrder : order >-> TPOrder.order.
Canonical tPOrder.
Coercion meetOrder : order >-> Meet.order.
Canonical meetOrder.
Coercion tMeetOrder : order >-> TMeet.order.
Canonical tMeetOrder.
Coercion joinOrder : order >-> Join.order.
Canonical joinOrder.
Coercion tJoinOrder : order >-> TJoin.order.
Canonical tJoinOrder.
Coercion lattice : order >-> Lattice.order.
Canonical lattice.
Canonical meet_tJoinOrder.
Canonical join_tMeetOrder.
Canonical tMeet_tJoinOrder.
Canonical lattice_tPOrder.
Canonical lattice_tMeetOrder.
Canonical lattice_tJoinOrder.
Notation "{ 'tLattice' T }" := (order (Phant T))
  (at level 0, format "{ 'tLattice'  T }").
Notation "[ 'tLattice' 'of' le ]" :=
  (@pack _ (Phant _) le (nosimpl _) (nosimpl _) (nosimpl _) (nosimpl _)
         _ _ id _ _ id)
  (at level 0, format "[ 'tLattice'  'of'  le ]").
End Exports.

End TLattice.
Import TLattice.Exports.

Module TBLattice.

Section ClassDef.

Variable T : eqType.

Set Primitive Projections.

Record class_of (le lt : rel T) (meet join : T -> T -> T) (bottom top : T) :=
  Class {
  base : BLattice.class_of le lt meet join bottom;
  mixin : TPOrder.mixin_of (POrder.Pack _ base) top;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  join : T -> T -> T;
  bottom : T;
  top : T;
  #[canonical=no] class_ : class_of le lt meet join bottom top;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> BLattice.class_of.
Local Coercion base2 le lt meet join bottom top
      (c : class_of le lt meet join bottom top) :
  TLattice.class_of le lt meet join top := TLattice.Class (mixin c).
Local Coercion base3 le lt meet join bottom top
      (c : class_of le lt meet join bottom top) :
  TBMeet.class_of le lt meet bottom top := TBMeet.Class (base := c) (mixin c).
Local Coercion base4 le lt meet join bottom top
      (c : class_of le lt meet join bottom top) :
  TBJoin.class_of le lt join bottom top := TBJoin.Class (base := c) (mixin c).

Variable (phT : phant T) (ord : order phT).

Definition class :
  class_of (le ord) (lt ord) (meet ord) (join ord) (bottom ord) (top ord) :=
  let: Pack _ _ _ _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.
Definition bPOrder := @BPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) class.
Definition tPOrder := @TPOrder.Pack _ phT (le ord) (lt ord) (top ord) class.
Definition tbPOrder :=
  @TBPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) (top ord) class.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) class.
Definition bMeetOrder :=
  @BMeet.Pack _ phT (le ord) (lt ord) (meet ord) (bottom ord) class.
Definition tMeetOrder :=
  @TMeet.Pack _ phT (le ord) (lt ord) (meet ord) (top ord) class.
Definition tbMeetOrder :=
  @TBMeet.Pack _ phT (le ord) (lt ord) (meet ord) (bottom ord) (top ord) class.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) class.
Definition bJoinOrder :=
  @BJoin.Pack _ phT (le ord) (lt ord) (join ord) (bottom ord) class.
Definition tJoinOrder :=
  @TJoin.Pack _ phT (le ord) (lt ord) (join ord) (top ord) class.
Definition tbJoinOrder :=
  @TBJoin.Pack _ phT (le ord) (lt ord) (join ord) (bottom ord) (top ord) class.
Definition lattice :=
  @Lattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) class.
Definition bLattice :=
  @BLattice.Pack
    _ phT (le ord) (lt ord) (meet ord) (join ord) (bottom ord) class.
Definition tLattice :=
  @TLattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) (top ord) class.
(* TODO: non-trivial joins are missing below. *)

Variable (leT ltT : rel T) (meetT joinT : T -> T -> T) (bottomT topT : T).

Definition pack :=
  fun (bord : BLattice.order phT)
      (b : BLattice.class_of leT ltT meetT joinT bottomT)
      & phant_id (BLattice.class bord) b =>
  fun (mord : TPOrder.order phT) m
      & phant_id (TPOrder.class mord) (TPOrder.Class (base := b) m) =>
  @Pack phT leT ltT meetT joinT bottomT topT (Class (base := b) m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> BLattice.class_of.
Coercion base2 : class_of >-> TLattice.class_of.
Coercion base3 : class_of >-> TBMeet.class_of.
Coercion base4 : class_of >-> TBJoin.class_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Coercion bPOrder : order >-> BPOrder.order.
Canonical bPOrder.
Coercion tPOrder : order >-> TPOrder.order.
Canonical tPOrder.
Coercion tbPOrder : order >-> TBPOrder.order.
Canonical tbPOrder.
Coercion meetOrder : order >-> Meet.order.
Canonical meetOrder.
Coercion bMeetOrder : order >-> BMeet.order.
Canonical bMeetOrder.
Coercion tMeetOrder : order >-> TMeet.order.
Canonical tMeetOrder.
Coercion tbMeetOrder : order >-> TBMeet.order.
Canonical tbMeetOrder.
Coercion joinOrder : order >-> Join.order.
Canonical joinOrder.
Coercion bJoinOrder : order >-> BJoin.order.
Canonical bJoinOrder.
Coercion tJoinOrder : order >-> TJoin.order.
Canonical tJoinOrder.
Coercion tbJoinOrder : order >-> TBJoin.order.
Canonical tbJoinOrder.
Coercion lattice : order >-> Lattice.order.
Canonical lattice.
Coercion bLattice : order >-> BLattice.order.
Canonical bLattice.
Coercion tLattice : order >-> TLattice.order.
Canonical tLattice.
Notation "{ 'tbLattice' T }" := (order (Phant T))
  (at level 0, format "{ 'tbLattice'  T }").
Notation "[ 'tbLattice' 'of' le ]" :=
  (@pack _ (Phant _) le (nosimpl _) (nosimpl _) (nosimpl _) (nosimpl _)
         (nosimpl _) _ _ id _ _ id)
  (at level 0, format "[ 'tbLattice'  'of'  le ]").
End Exports.

End TBLattice.
Import TBLattice.Exports.

Module DistrLattice.

Section ClassDef.

Variable T : eqType.

Set Primitive Projections.

Record mixin_of (ord : {lattice T}) := Mixin {
  meetUl : left_distributive (meet ord) (join ord);
  joinIl : left_distributive (join ord) (meet ord);
}.

Record class_of (le lt : rel T) (meet join : T -> T -> T) := Class {
  base : Lattice.class_of le lt meet join;
  mixin : mixin_of (Lattice.Pack _ base);
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  join : T -> T -> T;
  #[canonical=no] class_ : class_of le lt meet join;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> Lattice.class_of.

Variable (phT : phant T) (ord : order phT).

Definition class : class_of (le ord) (lt ord) (meet ord) (join ord) :=
  let: Pack _ _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) class.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) class.
Definition lattice :=
  @Lattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) class.

Variable (leT ltT : rel T) (meetT joinT : T -> T -> T).

Definition clone c of phant_id class c := @Pack phT leT ltT meetT joinT c.

Definition pack (b0 : Lattice.class_of leT ltT meetT joinT)
                (m0 : mixin_of (Lattice.Pack _ b0)) :=
  fun (b : Lattice.class_of leT ltT meetT joinT) & phant_id b0 b =>
  fun (m : mixin_of (Lattice.Pack _ b))          & phant_id m0 m =>
  @Pack phT leT ltT meetT joinT (Class m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> Lattice.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Coercion meetOrder : order >-> Meet.order.
Canonical meetOrder.
Coercion joinOrder : order >-> Join.order.
Canonical joinOrder.
Coercion lattice : order >-> Lattice.order.
Canonical lattice.
Notation "{ 'distrLattice' T }" := (order (Phant T))
  (at level 0, format "{ 'distrLattice'  T }").
Notation DistrLattice le lt meet join mixin :=
  (@pack _ (Phant _) le lt meet join _ mixin _ id _ id).
Notation "[ 'distrLattice' 'of' le ]" :=
  (@clone _ (Phant _) _ le (nosimpl _) (nosimpl _) (nosimpl _) _ id)
  (at level 0, format "[ 'distrLattice'  'of'  le ]").
End Exports.

End DistrLattice.
Import DistrLattice.Exports.

Module BDistrLattice.

Section ClassDef.

Variable T : eqType.

Set Primitive Projections.

Record class_of (le lt : rel T) (meet join : T -> T -> T) (bottom : T) :=
  Class {
  base : DistrLattice.class_of le lt meet join;
  mixin : BPOrder.mixin_of (Lattice.Pack _ base) bottom;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  join : T -> T -> T;
  bottom : T;
  #[canonical=no] class_ : class_of le lt meet join bottom;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> DistrLattice.class_of.
Local Coercion base2 le lt meet join bottom
                     (c : class_of le lt meet join bottom) :
  BLattice.class_of le lt meet join bottom := BLattice.Class (mixin c).

Variable (phT : phant T) (ord : order phT).

Definition class :
  class_of (le ord) (lt ord) (meet ord) (join ord) (bottom ord) :=
  let: Pack _ _ _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.
Definition bPOrder := @BPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) class.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) class.
Definition bMeetOrder :=
  @BMeet.Pack _ phT (le ord) (lt ord) (meet ord) (bottom ord) class.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) class.
Definition bJoinOrder :=
  @BJoin.Pack _ phT (le ord) (lt ord) (join ord) (bottom ord) class.
Definition lattice :=
  @Lattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) class.
Definition bLattice :=
  @BLattice.Pack
    _ phT (le ord) (lt ord) (meet ord) (join ord) (bottom ord) class.
Definition distrLattice :=
  @DistrLattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) class.

Variable (leT ltT : rel T) (meetT joinT : T -> T -> T) (bottomT : T).

Definition pack :=
  fun (bord : DistrLattice.order phT)
      (b : DistrLattice.class_of leT ltT meetT joinT)
      & phant_id (DistrLattice.class bord) b =>
  fun (mord : BPOrder.order phT) m
      & phant_id (BPOrder.class mord) (BPOrder.Class (base := b) m) =>
  @Pack phT leT ltT meetT joinT bottomT (Class (base := b) m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> DistrLattice.class_of.
Coercion base2 : class_of >-> BLattice.class_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Coercion bPOrder : order >-> BPOrder.order.
Canonical bPOrder.
Coercion meetOrder : order >-> Meet.order.
Canonical meetOrder.
Coercion bMeetOrder : order >-> BMeet.order.
Canonical bMeetOrder.
Coercion joinOrder : order >-> Join.order.
Canonical joinOrder.
Coercion bJoinOrder : order >-> BJoin.order.
Canonical bJoinOrder.
Coercion lattice : order >-> Lattice.order.
Canonical lattice.
Coercion bLattice : order >-> BLattice.order.
Canonical bLattice.
Coercion distrLattice : order >-> DistrLattice.order.
Canonical distrLattice.
Notation "{ 'bDistrLattice' T }" := (order (Phant T))
  (at level 0, format "{ 'bDistrLattice'  T }").
Notation "[ 'bDistrLattice' 'of' le ]" :=
  (@pack _ (Phant _) le (nosimpl _) (nosimpl _) (nosimpl _) (nosimpl _)
         _ _ id _ _ id)
  (at level 0, format "[ 'bDistrLattice'  'of'  le ]").
End Exports.

End BDistrLattice.
Import BDistrLattice.Exports.

Module TDistrLattice.

Section ClassDef.

Variable T : eqType.

Set Primitive Projections.

Record class_of (le lt : rel T) (meet join : T -> T -> T) (top : T) :=
  Class {
  base : DistrLattice.class_of le lt meet join;
  mixin : TPOrder.mixin_of (POrder.Pack _ base) top;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  join : T -> T -> T;
  top : T;
  #[canonical=no] class_ : class_of le lt meet join top;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> DistrLattice.class_of.
Local Coercion base2 le lt meet join top (c : class_of le lt meet join top) :
  TLattice.class_of le lt meet join top := TLattice.Class (mixin c).

Variable (phT : phant T) (ord : order phT).

Definition class : class_of (le ord) (lt ord) (meet ord) (join ord) (top ord) :=
  let: Pack _ _ _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.
Definition tPOrder := @TPOrder.Pack _ phT (le ord) (lt ord) (top ord) class.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) class.
Definition tMeetOrder :=
  @TMeet.Pack _ phT (le ord) (lt ord) (meet ord) (top ord) class.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) class.
Definition tJoinOrder :=
  @TJoin.Pack _ phT (le ord) (lt ord) (join ord) (top ord) class.
Definition lattice :=
  @Lattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) class.
Definition tLattice :=
  @TLattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) (top ord) class.
Definition distrLattice :=
  @DistrLattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) class.

Variable (leT ltT : rel T) (meetT joinT : T -> T -> T) (topT : T).

Definition pack :=
  fun (bord : DistrLattice.order phT)
      (b : DistrLattice.class_of leT ltT meetT joinT)
      & phant_id (DistrLattice.class bord) b =>
  fun (mord : TPOrder.order phT) m
      & phant_id (TPOrder.class mord) (TPOrder.Class (base := b) m) =>
  @Pack phT leT ltT meetT joinT topT (Class (base := b) m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> DistrLattice.class_of.
Coercion base2 : class_of >-> TLattice.class_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Coercion tPOrder : order >-> TPOrder.order.
Canonical tPOrder.
Coercion meetOrder : order >-> Meet.order.
Canonical meetOrder.
Coercion tMeetOrder : order >-> TMeet.order.
Canonical tMeetOrder.
Coercion joinOrder : order >-> Join.order.
Canonical joinOrder.
Coercion tJoinOrder : order >-> TJoin.order.
Canonical tJoinOrder.
Coercion lattice : order >-> Lattice.order.
Canonical lattice.
Coercion tLattice : order >-> TLattice.order.
Canonical tLattice.
Coercion distrLattice : order >-> DistrLattice.order.
Canonical distrLattice.
Notation "{ 'tDistrLattice' T }" := (order (Phant T))
  (at level 0, format "{ 'tDistrLattice'  T }").
Notation "[ 'tDistrLattice' 'of' le ]" :=
  (@pack _ (Phant _) le (nosimpl _) (nosimpl _) (nosimpl _) (nosimpl _)
         _ _ id _ _ id)
  (at level 0, format "[ 'tDistrLattice'  'of'  le ]").
End Exports.

End TDistrLattice.
Import TDistrLattice.Exports.

Module TBDistrLattice.

Section ClassDef.

Variable T : eqType.

Set Primitive Projections.

Record class_of (le lt : rel T) (meet join : T -> T -> T) (bottom top : T) :=
  Class {
  base : BDistrLattice.class_of le lt meet join bottom;
  mixin : TPOrder.mixin_of (POrder.Pack _ base) top;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  join : T -> T -> T;
  bottom : T;
  top : T;
  #[canonical=no] class_ : class_of le lt meet join bottom top;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> BDistrLattice.class_of.
Local Coercion base2 le lt meet join bottom top
      (c : class_of le lt meet join bottom top) :
  TDistrLattice.class_of le lt meet join top :=
  TDistrLattice.Class (mixin c).
Local Coercion base3 le lt meet join bottom top
      (c : class_of le lt meet join bottom top) :
  TBLattice.class_of le lt meet join bottom top :=
  TBLattice.Class (base := c) (mixin c).

Variable (phT : phant T) (ord : order phT).

Definition class :
  class_of (le ord) (lt ord) (meet ord) (join ord) (bottom ord) (top ord) :=
  let: Pack _ _ _ _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.
Definition bPOrder := @BPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) class.
Definition tPOrder := @TPOrder.Pack _ phT (le ord) (lt ord) (top ord) class.
Definition tbPOrder :=
  @TBPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) (top ord) class.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) class.
Definition bMeetOrder :=
  @BMeet.Pack _ phT (le ord) (lt ord) (meet ord) (bottom ord) class.
Definition tMeetOrder :=
  @TMeet.Pack _ phT (le ord) (lt ord) (meet ord) (top ord) class.
Definition tbMeetOrder :=
  @TBMeet.Pack _ phT (le ord) (lt ord) (meet ord) (bottom ord) (top ord) class.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) class.
Definition bJoinOrder :=
  @BJoin.Pack _ phT (le ord) (lt ord) (join ord) (bottom ord) class.
Definition tJoinOrder :=
  @TJoin.Pack _ phT (le ord) (lt ord) (join ord) (top ord) class.
Definition tbJoinOrder :=
  @TBJoin.Pack _ phT (le ord) (lt ord) (join ord) (bottom ord) (top ord) class.
Definition lattice :=
  @Lattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) class.
Definition bLattice :=
  @BLattice.Pack
    _ phT (le ord) (lt ord) (meet ord) (join ord) (bottom ord) class.
Definition tLattice :=
  @TLattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) (top ord) class.
Definition tbLattice :=
  @TBLattice.Pack
    _ phT (le ord) (lt ord) (meet ord) (join ord) (bottom ord) (top ord) class.
Definition distrLattice :=
  @DistrLattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) class.
Definition bDistrLattice :=
  @BDistrLattice.Pack
    _ phT (le ord) (lt ord) (meet ord) (join ord) (bottom ord) class.
Definition tDistrLattice :=
  @TDistrLattice.Pack
    _ phT (le ord) (lt ord) (meet ord) (join ord) (top ord) class.

Variable (leT ltT : rel T) (meetT joinT : T -> T -> T) (bottomT topT : T).

Definition pack :=
  fun (bord : BDistrLattice.order phT)
      (b : BDistrLattice.class_of leT ltT meetT joinT bottomT)
      & phant_id (BDistrLattice.class bord) b =>
  fun (mord : TPOrder.order phT) m
      & phant_id (TPOrder.class mord) (TPOrder.Class (base := b) m) =>
  @Pack phT leT ltT meetT joinT bottomT topT (Class (base := b) m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> BDistrLattice.class_of.
Coercion base2 : class_of >-> TDistrLattice.class_of.
Coercion base3 : class_of >-> TBLattice.class_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Coercion bPOrder : order >-> BPOrder.order.
Canonical bPOrder.
Coercion tPOrder : order >-> TPOrder.order.
Canonical tPOrder.
Coercion tbPOrder : order >-> TBPOrder.order.
Canonical tbPOrder.
Coercion meetOrder : order >-> Meet.order.
Canonical meetOrder.
Coercion bMeetOrder : order >-> BMeet.order.
Canonical bMeetOrder.
Coercion tMeetOrder : order >-> TMeet.order.
Canonical tMeetOrder.
Coercion tbMeetOrder : order >-> TBMeet.order.
Canonical tbMeetOrder.
Coercion joinOrder : order >-> Join.order.
Canonical joinOrder.
Coercion bJoinOrder : order >-> BJoin.order.
Canonical bJoinOrder.
Coercion tJoinOrder : order >-> TJoin.order.
Canonical tJoinOrder.
Coercion tbJoinOrder : order >-> TBJoin.order.
Canonical tbJoinOrder.
Coercion lattice : order >-> Lattice.order.
Canonical lattice.
Coercion bLattice : order >-> BLattice.order.
Canonical bLattice.
Coercion tLattice : order >-> TLattice.order.
Canonical tLattice.
Coercion tbLattice : order >-> TBLattice.order.
Canonical tbLattice.
Coercion distrLattice : order >-> DistrLattice.order.
Canonical distrLattice.
Coercion bDistrLattice : order >-> BDistrLattice.order.
Canonical bDistrLattice.
Coercion tDistrLattice : order >-> TDistrLattice.order.
Canonical tDistrLattice.
Notation "{ 'tbDistrLattice' T }" := (order (Phant T))
  (at level 0, format "{ 'tbDistrLattice'  T }").
Notation "[ 'tbDistrLattice' 'of' le ]" :=
  (@pack _ (Phant _) le (nosimpl _) (nosimpl _) (nosimpl _) (nosimpl _)
         (nosimpl _) _ _ id _ _ id)
  (at level 0, format "[ 'tbDistrLattice'  'of' le ]").
End Exports.

End TBDistrLattice.
Import TBDistrLattice.Exports.

Module Total.

Section ClassDef.

Variable T : eqType.

Definition mixin_of (ord : {pOrder T}) := total (le ord).

Definition le_total ord (m : mixin_of ord) : total (le ord) := m.

Set Primitive Projections.

Record class_of (le lt : rel T) (meet join : T -> T -> T) := Class {
  base : DistrLattice.class_of le lt meet join;
  mixin : mixin_of (POrder.Pack _ base);
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  join : T -> T -> T;
  #[canonical=no] class_ : class_of le lt meet join;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> DistrLattice.class_of.

Variable (phT : phant T) (ord : order phT).

Definition class : class_of (le ord) (lt ord) (meet ord) (join ord) :=
  let: Pack _ _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) class.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) class.
Definition lattice :=
  @Lattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) class.
Definition distrLattice :=
  @DistrLattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) class.

Variable (leT ltT : rel T) (meetT joinT : T -> T -> T).

Definition clone c of phant_id class c := @Pack phT leT ltT meetT joinT c.

Definition pack (m0 : total leT) :=
  fun (bord : DistrLattice.order phT) b
        & phant_id (DistrLattice.class bord) b =>
  fun m & phant_id m0 m =>
  @Pack phT leT ltT meetT joinT (@Class leT ltT meetT joinT b m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> DistrLattice.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion le_total : mixin_of >-> total.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Coercion meetOrder : order >-> Meet.order.
Canonical meetOrder.
Coercion joinOrder : order >-> Join.order.
Canonical joinOrder.
Coercion lattice : order >-> Lattice.order.
Canonical lattice.
Coercion distrLattice : order >-> DistrLattice.order.
Canonical distrLattice.
Notation "{ 'totalOrder' T }" := (order (Phant T))
  (at level 0, format "{ 'totalOrder'  T }").
Notation TotalOrder le lt meet join mixin :=
  (@pack _ (Phant _) le lt meet join mixin _ _ id _ id).
Notation "[ 'totalOrder' 'of' le ]" :=
  (@clone _ (Phant _) _ le (nosimpl _) (nosimpl _) (nosimpl _) _ id)
  (at level 0, format "[ 'totalOrder'  'of'  le ]").
End Exports.

End Total.
Import Total.Exports.

Module BTotal.

Section ClassDef.

Variable T : eqType.

Set Primitive Projections.

Record class_of (le lt : rel T) (meet join : T -> T -> T) (bottom : T) :=
  Class {
  base : Total.class_of le lt meet join;
  mixin : BPOrder.mixin_of (POrder.Pack _ base) bottom;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  join : T -> T -> T;
  bottom : T;
  #[canonical=no] class_ : class_of le lt meet join bottom;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> Total.class_of.
Local Coercion base2 le lt meet join bottom
                     (c : class_of le lt meet join bottom) :
  BDistrLattice.class_of le lt meet join bottom :=
  BDistrLattice.Class (mixin c).

Variable (phT : phant T) (ord : order phT).

Definition class :
  class_of (le ord) (lt ord) (meet ord) (join ord) (bottom ord) :=
  let: Pack _ _ _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.
Definition bPOrder := @BPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) class.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) class.
Definition bMeetOrder :=
  @BMeet.Pack _ phT (le ord) (lt ord) (meet ord) (bottom ord) class.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) class.
Definition bJoinOrder :=
  @BJoin.Pack _ phT (le ord) (lt ord) (join ord) (bottom ord) class.
Definition lattice :=
  @Lattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) class.
Definition bLattice :=
  @BLattice.Pack
    _ phT (le ord) (lt ord) (meet ord) (join ord) (bottom ord) class.
Definition distrLattice :=
  @DistrLattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) class.
Definition bDistrLattice :=
  @BDistrLattice.Pack
    _ phT (le ord) (lt ord) (meet ord) (join ord) (bottom ord) class.
Definition totalOrder :=
  @Total.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) class.

Variable (leT ltT : rel T) (meetT joinT : T -> T -> T) (bottomT : T).

Definition pack :=
  fun (bord : Total.order phT) (b : Total.class_of leT ltT meetT joinT)
      & phant_id (Total.class bord) b =>
  fun (mord : BPOrder.order phT) m
      & phant_id (BPOrder.class mord) (BPOrder.Class (base := b) m) =>
  @Pack phT leT ltT meetT joinT bottomT (Class (base := b) m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> Total.class_of.
Coercion base2 : class_of >-> BDistrLattice.class_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Coercion bPOrder : order >-> BPOrder.order.
Canonical bPOrder.
Coercion meetOrder : order >-> Meet.order.
Canonical meetOrder.
Coercion bMeetOrder : order >-> BMeet.order.
Canonical bMeetOrder.
Coercion joinOrder : order >-> Join.order.
Canonical joinOrder.
Coercion bJoinOrder : order >-> BJoin.order.
Canonical bJoinOrder.
Coercion lattice : order >-> Lattice.order.
Canonical lattice.
Coercion bLattice : order >-> BLattice.order.
Canonical bLattice.
Coercion distrLattice : order >-> DistrLattice.order.
Canonical distrLattice.
Coercion bDistrLattice : order >-> BDistrLattice.order.
Canonical bDistrLattice.
Coercion totalOrder : order >-> Total.order.
Canonical totalOrder.
Notation "{ 'bTotalOrder' T }" := (order (Phant T))
  (at level 0, format "{ 'bTotalOrder'  T }").
Notation "[ 'bTotalOrder' 'of' le ]" :=
  (@pack _ (Phant _) le (nosimpl _) (nosimpl _) (nosimpl _) (nosimpl _)
         _ _ id _ _ id)
  (at level 0, format "[ 'bTotalOrder'  'of'  le ]").
End Exports.

End BTotal.
Import BTotal.Exports.

Module TTotal.

Section ClassDef.

Variable T : eqType.

Set Primitive Projections.

Record class_of (le lt : rel T) (meet join : T -> T -> T) (top : T) :=
  Class {
  base : Total.class_of le lt meet join;
  mixin : TPOrder.mixin_of (POrder.Pack _ base) top;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  join : T -> T -> T;
  top : T;
  #[canonical=no] class_ : class_of le lt meet join top;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> Total.class_of.
Local Coercion base2 le lt meet join top (c : class_of le lt meet join top) :
  TDistrLattice.class_of le lt meet join top :=
  TDistrLattice.Class (mixin c).

Variable (phT : phant T) (ord : order phT).

Definition class : class_of (le ord) (lt ord) (meet ord) (join ord) (top ord) :=
  let: Pack _ _ _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.
Definition tPOrder := @TPOrder.Pack _ phT (le ord) (lt ord) (top ord) class.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) class.
Definition tMeetOrder :=
  @TMeet.Pack _ phT (le ord) (lt ord) (meet ord) (top ord) class.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) class.
Definition tJoinOrder :=
  @TJoin.Pack _ phT (le ord) (lt ord) (join ord) (top ord) class.
Definition lattice :=
  @Lattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) class.
Definition tLattice :=
  @TLattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) (top ord) class.
Definition distrLattice :=
  @DistrLattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) class.
Definition tDistrLattice :=
  @TDistrLattice.Pack
    _ phT (le ord) (lt ord) (meet ord) (join ord) (top ord) class.
Definition totalOrder :=
  @Total.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) class.

Variable (leT ltT : rel T) (meetT joinT : T -> T -> T) (topT : T).

Definition pack :=
  fun (bord : Total.order phT) (b : Total.class_of leT ltT meetT joinT)
      & phant_id (Total.class bord) b =>
  fun (mord : TPOrder.order phT) m
      & phant_id (TPOrder.class mord) (TPOrder.Class (base := b) m) =>
  @Pack phT leT ltT meetT joinT topT (Class (base := b) m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> Total.class_of.
Coercion base2 : class_of >-> TDistrLattice.class_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Coercion tPOrder : order >-> TPOrder.order.
Canonical tPOrder.
Coercion meetOrder : order >-> Meet.order.
Canonical meetOrder.
Coercion tMeetOrder : order >-> TMeet.order.
Canonical tMeetOrder.
Coercion joinOrder : order >-> Join.order.
Canonical joinOrder.
Coercion tJoinOrder : order >-> TJoin.order.
Canonical tJoinOrder.
Coercion lattice : order >-> Lattice.order.
Canonical lattice.
Coercion tLattice : order >-> TLattice.order.
Canonical tLattice.
Coercion distrLattice : order >-> DistrLattice.order.
Canonical distrLattice.
Coercion tDistrLattice : order >-> TDistrLattice.order.
Canonical tDistrLattice.
Coercion totalOrder : order >-> Total.order.
Canonical totalOrder.
Notation "{ 'tTotalOrder' T }" := (order (Phant T))
  (at level 0, format "{ 'tTotalOrder'  T }").
Notation "[ 'tTotalOrder' 'of' le ]" :=
  (@pack _ (Phant _) le (nosimpl _) (nosimpl _) (nosimpl _) (nosimpl _)
         _ _ id _ _ id)
  (at level 0, format "[ 'tTotalOrder'  'of'  le ]").
End Exports.

End TTotal.
Import TTotal.Exports.

Module TBTotal.

Section ClassDef.

Variable T : eqType.

Set Primitive Projections.

Record class_of (le lt : rel T) (meet join : T -> T -> T) (bottom top : T) :=
  Class {
  base : BTotal.class_of le lt meet join bottom;
  mixin : TPOrder.mixin_of (POrder.Pack _ base) top;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  join : T -> T -> T;
  bottom : T;
  top : T;
  #[canonical=no] class_ : class_of le lt meet join bottom top;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> BTotal.class_of.
Local Coercion base2 le lt meet join bottom top
      (c : class_of le lt meet join bottom top) :
  TTotal.class_of le lt meet join top := TTotal.Class (mixin c).
Local Coercion base3 le lt meet join bottom top
      (c : class_of le lt meet join bottom top) :
  TBDistrLattice.class_of le lt meet join bottom top :=
  TBDistrLattice.Class (base := c) (mixin c).

Variable (phT : phant T) (ord : order phT).

Definition class :
  class_of (le ord) (lt ord) (meet ord) (join ord) (bottom ord) (top ord) :=
  let: Pack _ _ _ _ _ _ c as ord' := ord in c.

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) class.
Definition bPOrder := @BPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) class.
Definition tPOrder := @TPOrder.Pack _ phT (le ord) (lt ord) (top ord) class.
Definition tbPOrder :=
  @TBPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) (top ord) class.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) class.
Definition bMeetOrder :=
  @BMeet.Pack _ phT (le ord) (lt ord) (meet ord) (bottom ord) class.
Definition tMeetOrder :=
  @TMeet.Pack _ phT (le ord) (lt ord) (meet ord) (top ord) class.
Definition tbMeetOrder :=
  @TBMeet.Pack _ phT (le ord) (lt ord) (meet ord) (bottom ord) (top ord) class.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) class.
Definition bJoinOrder :=
  @BJoin.Pack _ phT (le ord) (lt ord) (join ord) (bottom ord) class.
Definition tJoinOrder :=
  @TJoin.Pack _ phT (le ord) (lt ord) (join ord) (top ord) class.
Definition tbJoinOrder :=
  @TBJoin.Pack _ phT (le ord) (lt ord) (join ord) (bottom ord) (top ord) class.
Definition lattice :=
  @Lattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) class.
Definition bLattice :=
  @BLattice.Pack
    _ phT (le ord) (lt ord) (meet ord) (join ord) (bottom ord) class.
Definition tLattice :=
  @TLattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) (top ord) class.
Definition tbLattice :=
  @TBLattice.Pack
    _ phT (le ord) (lt ord) (meet ord) (join ord) (bottom ord) (top ord) class.
Definition distrLattice :=
  @DistrLattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) class.
Definition bDistrLattice :=
  @BDistrLattice.Pack
    _ phT (le ord) (lt ord) (meet ord) (join ord) (bottom ord) class.
Definition tDistrLattice :=
  @TDistrLattice.Pack
    _ phT (le ord) (lt ord) (meet ord) (join ord) (top ord) class.
Definition tbDistrLattice :=
  @TBDistrLattice.Pack
    _ phT (le ord) (lt ord) (meet ord) (join ord) (bottom ord) (top ord) class.
Definition totalOrder :=
  @Total.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) class.
Definition bTotalOrder :=
  @BTotal.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) (bottom ord) class.
Definition tTotalOrder :=
  @TTotal.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) (top ord) class.

Variable (leT ltT : rel T) (meetT joinT : T -> T -> T) (bottomT topT : T).

Definition pack :=
  fun (bord : BTotal.order phT)
      (b : BTotal.class_of leT ltT meetT joinT bottomT)
      & phant_id (BTotal.class bord) b =>
  fun (mord : TPOrder.order phT) m
      & phant_id (TPOrder.class mord) (TPOrder.Class (base := b) m) =>
  @Pack phT leT ltT meetT joinT bottomT topT (Class (base := b) m).

End ClassDef.

Module Exports.
Coercion base : class_of >-> BTotal.class_of.
Coercion base2 : class_of >-> TTotal.class_of.
Coercion base3 : class_of >-> TBDistrLattice.class_of.
Coercion pOrder : order >-> POrder.order.
Canonical pOrder.
Coercion bPOrder : order >-> BPOrder.order.
Canonical bPOrder.
Coercion tPOrder : order >-> TPOrder.order.
Canonical tPOrder.
Coercion tbPOrder : order >-> TBPOrder.order.
Canonical tbPOrder.
Coercion meetOrder : order >-> Meet.order.
Canonical meetOrder.
Coercion bMeetOrder : order >-> BMeet.order.
Canonical bMeetOrder.
Coercion tMeetOrder : order >-> TMeet.order.
Canonical tMeetOrder.
Coercion tbMeetOrder : order >-> TBMeet.order.
Canonical tbMeetOrder.
Coercion joinOrder : order >-> Join.order.
Canonical joinOrder.
Coercion bJoinOrder : order >-> BJoin.order.
Canonical bJoinOrder.
Coercion tJoinOrder : order >-> TJoin.order.
Canonical tJoinOrder.
Coercion tbJoinOrder : order >-> TBJoin.order.
Canonical tbJoinOrder.
Coercion lattice : order >-> Lattice.order.
Canonical lattice.
Coercion bLattice : order >-> BLattice.order.
Canonical bLattice.
Coercion tLattice : order >-> TLattice.order.
Canonical tLattice.
Coercion tbLattice : order >-> TBLattice.order.
Canonical tbLattice.
Coercion distrLattice : order >-> DistrLattice.order.
Canonical distrLattice.
Coercion bDistrLattice : order >-> BDistrLattice.order.
Canonical bDistrLattice.
Coercion tDistrLattice : order >-> TDistrLattice.order.
Canonical tDistrLattice.
Coercion tbDistrLattice : order >-> TBDistrLattice.order.
Canonical tbDistrLattice.
Coercion totalOrder : order >-> Total.order.
Canonical totalOrder.
Coercion bTotalOrder : order >-> BTotal.order.
Canonical bTotalOrder.
Coercion tTotalOrder : order >-> TTotal.order.
Canonical tTotalOrder.
Notation "{ 'tbTotalOrder' T }" := (order (Phant T))
  (at level 0, format "{ 'tbTotalOrder'  T }").
Notation "[ 'tbTotalOrder' 'of' le ]" :=
  (@pack _ (Phant _) le (nosimpl _) (nosimpl _) (nosimpl _) (nosimpl _)
         (nosimpl _) _ _ id _ _ id)
  (at level 0, format "[ 'tbTotalOrder'  'of'  le ]").
End Exports.

End TBTotal.
Import TBTotal.Exports.

(* ========================================================================== *)

Section POrderDef.

Context {T: eqType} (ord : {pOrder T}).
Implicit Types (x y z : T).

Local Notation le := (le ord).
Local Notation lt := (lt ord).
Local Notation "x <= y" := (le x y).
Local Notation "x < y" := (lt x y).

Definition comparable : rel T := fun x y => (x <= y) || (y <= x).

Local Notation "x >< y" := (~~ (comparable x y)).

Definition ge : simpl_rel T := [rel x y | y <= x].
Definition gt : simpl_rel T := [rel x y | y < x].

Definition leif x y C : Prop := ((x <= y) * ((x == y) = C))%type.

Definition le_of_leif x y C (le_xy : leif x y C) : x <= y := le_xy.1.

Definition lteif x y C := if C then x <= y else x < y.

Definition min x y := if x < y then x else y.
Definition max x y := if x < y then y else x.

Definition arg_min {I : finType} := @extremum T I le.
Definition arg_max {I : finType} := @extremum T I ge.

End POrderDef.

Section LatticeDef.

Context {T: eqType} (ord : {lattice T}).
Implicit Types (x y : T).

Local Notation "x <= y" := (le ord x y).
Local Notation "x < y" := (lt ord x y).
Local Notation "x >< y" := (~~ (comparable ord x y)).
Local Notation "x `&` y" := (meet ord x y).
Local Notation "x `|` y" := (join ord x y).

End LatticeDef.

Variant le_xor_gt T (le lt : rel T) x y :
    T -> T -> T -> T -> bool -> bool -> Set :=
  | LeNotGt of le x y : le_xor_gt le lt x y x x y y true false
  | GtNotLe of lt y x : le_xor_gt le lt x y y y x x false true.

Variant lt_xor_ge T (le lt : rel T) x y :
    T -> T -> T -> T -> bool -> bool -> Set :=
  | LtNotGe of lt x y : lt_xor_ge le lt x y x x y y false true
  | GeNotLt of le y x : lt_xor_ge le lt x y y y x x true false.

Variant compare T (lt : rel T) x y :
    T -> T -> T -> T -> bool -> bool -> bool -> bool -> bool -> bool -> Set :=
  | CompareLt of lt x y :
    compare lt x y x x y y false false false true false true
  | CompareGt of lt y x :
    compare lt x y y y x x false false true false true false
  | CompareEq of x = y :
    compare lt x y x x x x true true true true false false.

Variant incompare T (lt comp : rel T) x y :
    T -> T -> T -> T ->
    bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> Set :=
  | InCompareLt of lt x y      : incompare lt comp x y
    x x y y false false false true false true true true
  | InCompareGt of lt y x      : incompare lt comp x y
    y y x x false false true false true false true true
  | InCompare   of ~~ comp x y : incompare lt comp x y
    x y y x false false false false false false false false
  | InCompareEq of x = y       : incompare lt comp x y
    x x x x true true true true false false true true.

Variant lel_xor_gt T (le lt : rel T) x y :
    T -> T -> T -> T -> T -> T -> T -> T -> bool -> bool -> Set :=
  | LelNotGt of le x y : lel_xor_gt le lt x y x x y y x x y y true false
  | GtlNotLe of lt y x : lel_xor_gt le lt x y y y x x y y x x false true.

Variant ltl_xor_ge T (le lt : rel T) x y :
    T -> T -> T -> T -> T -> T -> T -> T -> bool -> bool -> Set :=
  | LtlNotGe of lt x y : ltl_xor_ge le lt x y x x y y x x y y false true
  | GelNotLt of le y x : ltl_xor_ge le lt x y y y x x y y x x true false.

Variant comparel T (lt : rel T) x y :
    T -> T -> T -> T -> T -> T -> T -> T ->
    bool -> bool -> bool -> bool -> bool -> bool -> Set :=
  | ComparelLt of lt x y :
    comparel lt x y x x y y x x y y false false false true false true
  | ComparelGt of lt y x :
    comparel lt x y y y x x y y x x false false true false true false
  | ComparelEq of x = y :
    comparel lt x y x x x x x x x x true true true true false false.

Variant incomparel T (lt comp : rel T) (meet join : T -> T -> T) x y :
    T -> T -> T -> T -> T -> T -> T -> T ->
    bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> Set :=
  | InComparelLt of lt x y      : incomparel lt comp meet join x y
    x x y y x x y y false false false true false true true true
  | InComparelGt of lt y x      : incomparel lt comp meet join x y
    y y x x y y x x false false true false true false true true
  | InComparel   of ~~ comp x y : incomparel lt comp meet join x y
    x y y x (meet y x) (meet x y) (join y x) (join x y)
    false false false false false false false false
  | InComparelEq of x = y       : incomparel lt comp meet join x y
    x x x x x x x x true true true true false false true true.

(* TODO: Reserved Notation *)

Module Import Syntax.

Notation "<=: r" := (le r) (at level 2, r at level 1, format "<=: r").
Notation "<: r" := (lt r) (at level 2, r at level 1, format "<: r").
Notation "x <=_ r y" :=
  (<=: r x y) (at level 65, r at level 2, format "x  <=_ r  y").
Notation "x >=_ r y" := (y <=_r x) (at level 65, r at level 2, only parsing).
Notation "x <_ r y" :=
  (<: r x y) (at level 65, r at level 2, format "x  <_ r  y").
Notation "x >_ r y" := (y <_r x) (at level 65, r at level 2, only parsing).
Notation "x <=_ r0 y <=_ r1 z" := ((x <=_r0 y) && (y <=_r1 z))
  (at level 65, y, z at next level, r0 at level 2, r1 at level 2, format "x  <=_ r0  y  <=_ r1  z").
Notation "x <_ r0 y <_ r1 z" := ((x <_r0 y) && (y <_r1 z))
  (at level 65, y, z at next level, r0 at level 2, r1 at level 2, format "x  <_ r0  y  <_ r1  z").
Notation "x <=_ r0 y <_ r1 z" := ((x <=_r0 y) && (y <_r1 z))
  (at level 65, y, z at next level, r0 at level 2, r1 at level 2, format "x  <=_ r0  y  <_ r1  z").
Notation "x <_ r0 y <=_ r1 z" := ((x <_r0 y) && (y <=_r1 z))
  (at level 70, r0 at level 2, r1 at level 2, format "x  <_ r0  y  <=_ r1  z").
Notation "x >=<_ r y" := (comparable r x y)
  (at level 70, r at level 2, no associativity, format "x  >=<_ r  y").
Notation "x ><_ r y" := (~~ comparable r x y)
  (at level 70, r at level 2, no associativity, format "x  ><_ r  y").
Notation ">=<_ r y" :=
  [pred x | x >=<_r y] (at level 80, r at level 2, format ">=<_ r  y").
Notation "><_ r y" :=
  [pred x | x ><_r y] (at level 80, r at level 2, format "><_ r  y").

Notation "x <=_ r y ?= 'iff' C" := (leif r x y C)
  (at level 70, C at level 1, r at level 2,
   format "x '[hv'  <=_ r '/'  y  ?=  'iff'  C ']'").

Notation "x <_ r y ?<= 'if' C" := (lteif r x y C)
  (at level 71, C at level 1, r at level 1, y at next level,
   format "x '[hv'  <_ r '/'  y  ?<=  'if'  C ']'").

End Syntax.

(* ========================================================================== *)

Section DualOrder.

Variable T : eqType.

Canonical dual_pOrder (ord : {pOrder T}) :=
  POrder
    (dual_rel <=:ord) (dual_rel <:ord)
    (let mixin := POrder.class ord in
     @POrder.Mixin
       T (dual_rel <=:ord) (dual_rel <:ord)
       (POrder.dlt_def mixin) (POrder.lt_def mixin) (POrder.lexx mixin)
       (fun x y yx xy => POrder.le_anti mixin xy yx)
       (fun y x z xy yz => POrder.le_trans mixin yz xy)).

Canonical dual_bPOrder (ord : {tPOrder T}) :=
  BPOrder (dual_rel <=:ord) (dual_rel <:ord) (dual_bottom (top ord))
          (TPOrder.mixin (TPOrder.class ord) :
             BPOrder.mixin_of (dual_pOrder ord) _).

Canonical dual_tPOrder (ord : {bPOrder T}) :=
  TPOrder (dual_rel <=:ord) (dual_rel <:ord) (dual_top (bottom ord))
          (BPOrder.mixin (BPOrder.class ord) :
             TPOrder.mixin_of (dual_pOrder ord) _).

(* BUG, TODO: can we design better packagers to infer head symbols of         *)
(* operators from existing instances, or should operators other than [le] be  *)
(* specified (e.g., TBOrder le lt bottom top) to synthesize proper            *)
(* unification hints anyway? Clone notations have the same issue.             *)
Canonical dual_tbPOrder (ord : {tbPOrder T}) := [tbPOrder of dual_rel <=:ord].

Canonical dual_meetOrder (ord : {joinOrder T}) :=
  MeetOrder (dual_rel <=:ord) (dual_rel <:ord) (dual_meet (join ord))
            (Join.mixin (Join.class ord)).

Canonical dual_bMeetOrder (ord : {tJoinOrder T}) :=
  [bMeetOrder of dual_rel <=:ord].

Canonical dual_tMeetOrder (ord : {bJoinOrder T}) :=
  [tMeetOrder of dual_rel <=:ord].

Canonical dual_tbMeetOrder (ord : {tbJoinOrder T}) :=
  [tbMeetOrder of dual_rel <=:ord].

Canonical dual_joinOrder (ord : {meetOrder T}) :=
  JoinOrder (dual_rel <=:ord) (dual_rel <:ord) (dual_join (meet ord))
            (Meet.mixin (Meet.class ord) : Join.mixin_of (dual_pOrder ord) _).

Canonical dual_bJoinOrder (ord : {tMeetOrder T}) :=
  [bJoinOrder of dual_rel <=:ord].

Canonical dual_tJoinOrder (ord : {bMeetOrder T}) :=
  [tJoinOrder of dual_rel <=:ord].

Canonical dual_tbJoinOrder (ord : {tbMeetOrder T}) :=
  [tbJoinOrder of dual_rel <=:ord].

Canonical dual_lattice (ord : {lattice T}) := [lattice of dual_rel <=:ord].

Canonical dual_bLattice (ord : {tLattice T}) := [bLattice of dual_rel <=:ord].

Canonical dual_tLattice (ord : {bLattice T}) := [tLattice of dual_rel <=:ord].

Canonical dual_tbLattice (ord : {tbLattice T}) :=
  [tbLattice of dual_rel <=:ord].

Canonical dual_distrLattice (ord : {distrLattice T}) :=
  DistrLattice
    (dual_rel <=:ord) (dual_rel <:ord)
    (dual_meet (join ord)) (dual_join (meet ord))
    (let mixin := DistrLattice.mixin (DistrLattice.class ord) in
     @DistrLattice.Mixin _ (dual_lattice ord)
       (DistrLattice.joinIl mixin) (DistrLattice.meetUl mixin)).

Canonical dual_bDistrLattice (ord : {tDistrLattice T}) :=
  [bDistrLattice of dual_rel <=:ord].

Canonical dual_tDistrLattice (ord : {bDistrLattice T}) :=
  [tDistrLattice of dual_rel <=:ord].

Canonical dual_tbDistrLattice (ord : {tbDistrLattice T}) :=
  [tbDistrLattice of dual_rel <=:ord].

Canonical dual_totalOrder (ord : {totalOrder T}) :=
  TotalOrder
    (dual_rel <=:ord) (dual_rel <:ord)
    (dual_meet (join ord)) (dual_join (meet ord))
    (fun x y => Total.mixin (Total.class ord) y x).

Canonical dual_bTotalOrder (ord : {tTotalOrder T}) :=
  [bTotalOrder of dual_rel <=:ord].

Canonical dual_tTotalOrder (ord : {bTotalOrder T}) :=
  [tTotalOrder of dual_rel <=:ord].

Canonical dual_tbTotalOrder (ord : {tbTotalOrder T}) :=
  [tbTotalOrder of dual_rel <=:ord].

End DualOrder.
(* See [Module DualOrderTest] for tests. *)

(**********)
(* THEORY *)
(**********)

Module Import POrderTheory.
Section POrderTheory.
Context {T : eqType} {ord : {pOrder T}}.
Implicit Types (x y : T) (s : seq T).

Local Notation le := (le ord).
Local Notation lt := (lt ord).
Local Notation ge := (ge ord).
Local Notation gt := (gt ord).
Local Notation comparable := (comparable ord).
Local Notation leif := (leif ord).
Local Notation lteif := (lteif ord).
Local Notation min := (min ord).
Local Notation max := (max ord).
Local Notation le_xor_gt := (le_xor_gt le lt).
Local Notation lt_xor_ge := (lt_xor_ge le lt).
Local Notation compare := (compare lt).
Local Notation incompare := (incompare lt comparable).
Local Notation arg_min := (arg_min ord).
Local Notation arg_max := (arg_max ord).

Local Notation "x <= y" := (x <=_ord y).
Local Notation "x < y" := (x <_ord y).
Local Notation "x >= y" := (x >=_ord y) (only parsing).
Local Notation "x > y" := (x >_ord y) (only parsing).
Local Notation "x <= y <= z" := ((x <= y) && (y <= z)).
Local Notation "x < y < z"   := ((x < y) && (y < z)).
Local Notation "x < y <= z"  := ((x < y) && (y <= z)).
Local Notation "x <= y < z"  := ((x <= y) && (y < z)).

Local Notation ">=<%O" := comparable.
Local Notation ">=< y" := (>=<_ord y).
Local Notation "x >=< y" := (x >=<_ord y).
Local Notation "x >< y" := (x ><_ord y).

Local Notation "x <= y ?= 'iff' C" := (leif x y C).
Local Notation "x < y ?<= 'if' C" := (lteif x y C).

Lemma geE x y : ge x y = (y <= x). Proof. by []. Qed.
Lemma gtE x y : gt x y = (y < x). Proof. by []. Qed.

Lemma lexx : reflexive le.
Proof. by case: ord => ? ? []. Qed.
Hint Resolve lexx : core.
Hint Extern 0 (is_true (_ <=__ _)) => exact: lexx : core.

Definition le_refl : reflexive le := lexx.
Definition ge_refl : reflexive ge := lexx.

Lemma le_anti : antisymmetric le.
Proof. by case: ord => le lt [] ? ? ? ha ? x y /andP []; exact: ha. Qed.

Lemma ge_anti : antisymmetric ge.
Proof. by move=> x y /le_anti. Qed.

Lemma le_trans : transitive le.
Proof. by case: ord => ? ? []. Qed.

Lemma ge_trans : transitive ge.
Proof. by move=> ? ? ? ? /le_trans; apply. Qed.

Lemma lt_def x y : (x < y) = (y != x) && (x <= y).
Proof. by case: ord => ? ? []. Qed.

Lemma lt_neqAle x y : (x < y) = (x != y) && (x <= y).
Proof. by rewrite lt_def eq_sym. Qed.

Lemma ltxx x : x < x = false.
Proof. by rewrite lt_def eqxx. Qed.

Definition lt_irreflexive : irreflexive lt := ltxx.
Hint Resolve lt_irreflexive : core.

Definition ltexx := (lexx, ltxx).

Lemma le_eqVlt x y : (x <= y) = (x == y) || (x < y).
Proof. by rewrite lt_neqAle; case: eqP => //= ->; rewrite lexx. Qed.

Lemma lt_eqF x y : x < y -> x == y = false.
Proof. by rewrite lt_neqAle => /andP [/negbTE->]. Qed.

Lemma gt_eqF x y : y < x -> x == y = false.
Proof. by apply: contraTF => /eqP ->; rewrite ltxx. Qed.

Lemma eq_le x y : (x == y) = (x <= y <= x).
Proof. by apply/eqP/idP => [->|/le_anti]; rewrite ?lexx. Qed.

Lemma ltW x y : x < y -> x <= y.
Proof. by rewrite le_eqVlt orbC => ->. Qed.

Lemma lt_le_trans y x z : x < y -> y <= z -> x < z.
Proof.
rewrite !lt_neqAle => /andP [nexy lexy leyz]; rewrite (le_trans lexy) // andbT.
by apply: contraNneq nexy => eqxz; rewrite eqxz eq_le leyz andbT in lexy *.
Qed.

Lemma lt_trans : transitive lt.
Proof. by move=> y x z le1 /ltW le2; apply/(@lt_le_trans y). Qed.

Lemma le_lt_trans y x z : x <= y -> y < z -> x < z.
Proof. by rewrite le_eqVlt => /orP [/eqP ->|/lt_trans t /t]. Qed.

Lemma lt_nsym x y : x < y -> y < x -> False.
Proof. by move=> xy /(lt_trans xy); rewrite ltxx. Qed.

Lemma lt_asym x y : x < y < x = false.
Proof. by apply/negP => /andP []; apply: lt_nsym. Qed.

Lemma le_gtF x y : x <= y -> y < x = false.
Proof.
by move=> le_xy; apply/negP => /lt_le_trans /(_ le_xy); rewrite ltxx.
Qed.

Lemma lt_geF x y : (x < y) -> y <= x = false.
Proof.
by move=> le_xy; apply/negP => /le_lt_trans /(_ le_xy); rewrite ltxx.
Qed.

Definition lt_gtF x y hxy := le_gtF (@ltW x y hxy).

Lemma lt_leAnge x y : (x < y) = (x <= y) && ~~ (y <= x).
Proof.
apply/idP/idP => [ltxy|/andP[lexy Nleyx]]; first by rewrite ltW // lt_geF.
by rewrite lt_neqAle lexy andbT; apply: contraNneq Nleyx => ->.
Qed.

Lemma lt_le_asym x y : x < y <= x = false.
Proof. by rewrite lt_neqAle -andbA -eq_le eq_sym andNb. Qed.

Lemma le_lt_asym x y : x <= y < x = false.
Proof. by rewrite andbC lt_le_asym. Qed.

Definition lte_anti := (=^~ eq_le, lt_asym, lt_le_asym, le_lt_asym).

Lemma lt_sorted_uniq_le s : sorted lt s = uniq s && sorted le s.
Proof.
rewrite (sorted_pairwise le_trans) (sorted_pairwise lt_trans) uniq_pairwise.
by rewrite -pairwise_relI; apply/eq_pairwise => ? ?; rewrite lt_neqAle.
Qed.

Lemma lt_sorted_eq s1 s2 : sorted lt s1 -> sorted lt s2 -> s1 =i s2 -> s1 = s2.
Proof. by apply: irr_sorted_eq => //; apply: lt_trans. Qed.

Lemma le_sorted_eq s1 s2 :
  sorted le s1 -> sorted le s2 -> perm_eq s1 s2 -> s1 = s2.
Proof. exact/sorted_eq/le_anti/le_trans. Qed.

Lemma sort_le_id s : sorted le s -> sort le s = s.
Proof. exact/sorted_sort/le_trans. Qed.

Lemma le_sorted_ltn_nth (x0 : T) (s : seq T) : sorted <=:ord s ->
 {in [pred n | (n < size s)%N] &,
    {homo nth x0 s : i j / (i < j)%N >-> i <= j}}.
Proof. exact/sorted_ltn_nth/le_trans. Qed.

Lemma le_sorted_leq_nth (x0 : T) (s : seq T) : sorted <=:ord s ->
  {in [pred n | (n < size s)%N] &,
    {homo nth x0 s : i j / (i <= j)%N >-> i <= j}}.
Proof. exact: (sorted_leq_nth le_trans le_refl). Qed.

Lemma lt_sorted_leq_nth (x0 : T) (s : seq T) : sorted <:ord s ->
  {in [pred n | (n < size s)%N] &,
    {mono nth x0 s : i j / (i <= j)%N >-> i <= j}}.
Proof.
rewrite lt_sorted_uniq_le => /andP[s_uniq le_s].
apply: (total_homo_mono_in _ _ ltn_neqAle lt_neqAle le_anti leq_total) => //.
move=> i j ilt jlt ltij; rewrite lt_neqAle le_sorted_leq_nth// 1?ltnW//.
by rewrite nth_uniq// ltn_eqF.
Qed.

Lemma lt_sorted_ltn_nth (x0 : T) (s : seq T) : sorted <:ord s ->
  {in [pred n | (n < size s)%N] &,
    {mono nth x0 s : i j / (i < j)%N >-> i < j}}.
Proof.
move=> ss; have := lt_sorted_leq_nth x0 ss.
exact: (anti_mono_in _ ltn_neqAle lt_neqAle anti_leq).
Qed.

Lemma filter_lt_nth x0 s i : sorted <:ord s -> (i < size s)%N ->
  [seq x <- s | x < nth x0 s i] = take i s.
Proof.
move=> ss i_lt/=; rewrite -[X in filter _ X](mkseq_nth x0) filter_map.
under eq_in_filter => j do
  [rewrite ?mem_iota => j_s /=; rewrite lt_sorted_ltn_nth//].
by rewrite (filter_iota_ltn 0) ?map_nth_iota0 // ltnW.
Qed.

Lemma count_lt_nth x0 s i : sorted <:ord s -> (i < size s)%N ->
  count (fun y => y < nth x0 s i) s = i.
Proof.
by move=> ss i_lt; rewrite -size_filter/= filter_lt_nth// size_take i_lt.
Qed.

Lemma filter_le_nth x0 s i : sorted <:ord s -> (i < size s)%N ->
  [seq x <- s | x <= nth x0 s i] = take i.+1 s.
Proof.
move=> ss i_lt/=; rewrite -[X in filter _ X](mkseq_nth x0) filter_map.
under eq_in_filter => j do
  [rewrite ?mem_iota => j_s /=; rewrite lt_sorted_leq_nth//].
by rewrite (filter_iota_leq 0)// map_nth_iota0.
Qed.

Lemma count_le_nth x0 s i : sorted <:ord s -> (i < size s)%N ->
  count (le^~ (nth x0 s i)) s = i.+1.
Proof.
by move=> ss i_lt; rewrite -size_filter/= filter_le_nth// size_takel.
Qed.

Lemma count_lt_le_mem x s : (count (lt^~ x) s < count (le^~ x) s)%N = (x \in s).
Proof.
have := count_predUI (pred1 x) (lt^~ x) s.
have -> : count (predI (pred1 x) (lt^~ x)) s = 0%N.
  rewrite (@eq_count _ _ pred0) ?count_pred0 // => y /=.
  by rewrite lt_def; case: eqP => //= ->; rewrite eqxx.
have /eq_count->: predU (pred1 x) (lt^~ x) =1 le^~ x.
  by move=> y /=; rewrite le_eqVlt.
by rewrite addn0 => ->; rewrite -add1n leq_add2r -has_count has_pred1.
Qed.

Lemma sorted_filter_lt x s :
  sorted <=:ord s -> [seq y <- s | y < x] = take (count (lt^~ x) s) s.
Proof.
elim: s => [//|y s IHs]/=; rewrite (path_sortedE le_trans) => /andP[le_y_s ss].
case: ifP => [|ltyxF]; rewrite IHs//.
rewrite (@eq_in_count _ _ pred0) ?count_pred0/= ?take0// => z.
by move=> /(allP le_y_s) yz; apply: contraFF ltyxF; apply: le_lt_trans.
Qed.

Lemma sorted_filter_le x s :
  sorted <=:ord s -> [seq y <- s | y <= x] = take (count (le^~ x) s) s.
Proof.
elim: s => [//|y s IHs]/=; rewrite (path_sortedE le_trans) => /andP[le_y_s ss].
case: ifP => [|leyxF]; rewrite IHs//.
rewrite (@eq_in_count _ _ pred0) ?count_pred0/= ?take0// => z.
by move=> /(allP le_y_s) yz; apply: contraFF leyxF; apply: le_trans.
Qed.

Lemma nth_count_le x x0 s i : sorted <=:ord s ->
  (i < count (le^~ x) s)%N -> nth x0 s i <= x.
Proof.
move=> ss iltc; rewrite -(nth_take _ iltc) -sorted_filter_le //.
by apply/(all_nthP _ (filter_all (le^~ x) _)); rewrite size_filter.
Qed.

Lemma nth_count_lt x x0 s i : sorted <=:ord s ->
  (i < count (lt^~ x) s)%N -> nth x0 s i < x.
Proof.
move=> ss iltc; rewrite -(nth_take _ iltc) -sorted_filter_lt //.
by apply/(all_nthP _ (filter_all (lt^~ x) _)); rewrite size_filter.
Qed.

Lemma comparable_leNgt x y : x >=< y -> (x <= y) = ~~ (y < x).
Proof.
move=> c_xy; apply/idP/idP => [/le_gtF/negP/negP//|]; rewrite lt_neqAle.
by move: c_xy => /orP [] -> //; rewrite andbT negbK => /eqP ->.
Qed.

Lemma comparable_ltNge x y : x >=< y -> (x < y) = ~~ (y <= x).
Proof.
move=> c_xy; apply/idP/idP => [/lt_geF/negP/negP//|].
by rewrite lt_neqAle eq_le; move: c_xy => /orP [] -> //; rewrite andbT.
Qed.

Lemma comparable_ltgtP x y : x >=< y ->
  compare x y (min y x) (min x y) (max y x) (max x y)
  (y == x) (x == y) (x >= y) (x <= y) (x > y) (x < y).
Proof.
rewrite /min /max /comparable !le_eqVlt [y == x]eq_sym.
have := (eqVneq x y, (boolP (x < y), boolP (y < x))).
move=> [[->//|neq_xy /=] [[] xy [] //=]] ; do ?by rewrite ?ltxx; constructor.
  by rewrite ltxx in xy.
by rewrite le_gtF // ltW.
Qed.

Lemma comparable_leP x y : x >=< y ->
  le_xor_gt x y (min y x) (min x y) (max y x) (max x y) (x <= y) (y < x).
Proof. by case/comparable_ltgtP=> [?|?|->]; constructor; rewrite // ltW. Qed.

Lemma comparable_ltP x y : x >=< y ->
  lt_xor_ge x y (min y x) (min x y) (max y x) (max x y) (y <= x) (x < y).
Proof. by case/comparable_ltgtP=> [?|?|->]; constructor; rewrite // ltW. Qed.

Lemma comparable_sym x y : (y >=< x) = (x >=< y).
Proof. by rewrite /comparable orbC. Qed.

Lemma comparablexx x : x >=< x.
Proof. by rewrite /comparable lexx. Qed.

Lemma incomparable_eqF x y : (x >< y) -> (x == y) = false.
Proof. by apply: contraNF => /eqP ->; rewrite comparablexx. Qed.

Lemma incomparable_leF x y : (x >< y) -> (x <= y) = false.
Proof. by apply: contraNF; rewrite /comparable => ->. Qed.

Lemma incomparable_ltF x y : (x >< y) -> (x < y) = false.
Proof. by rewrite lt_neqAle => /incomparable_leF ->; rewrite andbF. Qed.

Lemma comparableP x y : incompare x y
  (min y x) (min x y) (max y x) (max x y)
  (y == x) (x == y) (x >= y) (x <= y) (x > y) (x < y) (y >=< x) (x >=< y).
Proof.
rewrite ![y >=< _]comparable_sym; have [c_xy|i_xy] := boolP (x >=< y).
  by case: (comparable_ltgtP c_xy) => ?; constructor.
by rewrite /min /max ?incomparable_eqF ?incomparable_leF;
   rewrite ?incomparable_ltF// 1?comparable_sym //; constructor.
Qed.

Lemma le_comparable (x y : T) : x <= y -> x >=< y.
Proof. by case: comparableP. Qed.

Lemma lt_comparable (x y : T) : x < y -> x >=< y.
Proof. by case: comparableP. Qed.

Lemma ge_comparable (x y : T) : y <= x -> x >=< y.
Proof. by case: comparableP. Qed.

Lemma gt_comparable (x y : T) : y < x -> x >=< y.
Proof. by case: comparableP. Qed.

(* leif *)

Lemma leifP x y C : reflect (x <= y ?= iff C) (if C then x == y else x < y).
Proof.
rewrite /leif le_eqVlt; apply: (iffP idP)=> [|[]].
  by case: C => [/eqP->|lxy]; rewrite ?eqxx // lxy lt_eqF.
by case/orP=> [/eqP->|lxy] <-; rewrite ?eqxx // lt_eqF.
Qed.

Lemma leif_refl x C : reflect (x <= x ?= iff C) C.
Proof. by apply: (iffP idP) => [-> | <-] //; split; rewrite ?eqxx. Qed.

Lemma leif_trans x1 x2 x3 C12 C23 :
  x1 <= x2 ?= iff C12 -> x2 <= x3 ?= iff C23 -> x1 <= x3 ?= iff C12 && C23.
Proof.
move=> ltx12 ltx23; apply/leifP; rewrite -ltx12.
case eqx12: (x1 == x2).
  by rewrite (eqP eqx12) lt_neqAle !ltx23 andbT; case C23.
by rewrite (@lt_le_trans x2) ?ltx23 // lt_neqAle eqx12 ltx12.
Qed.

Lemma leif_le x y : x <= y -> x <= y ?= iff (x >= y).
Proof. by move=> lexy; split=> //; rewrite eq_le lexy. Qed.

Lemma leif_eq x y : x <= y -> x <= y ?= iff (x == y).
Proof. by []. Qed.

Lemma ge_leif x y C : x <= y ?= iff C -> (y <= x) = C.
Proof. by case=> le_xy; rewrite eq_le le_xy. Qed.

Lemma lt_leif x y C : x <= y ?= iff C -> (x < y) = ~~ C.
Proof. by move=> le_xy; rewrite lt_neqAle !le_xy andbT. Qed.

Lemma ltNleif x y C : x <= y ?= iff ~~ C -> (x < y) = C.
Proof. by move/lt_leif; rewrite negbK. Qed.

Lemma eq_leif x y C : x <= y ?= iff C -> (x == y) = C.
Proof. by move/leifP; case: C comparableP => [] []. Qed.

Lemma eqTleif x y C : x <= y ?= iff C -> C -> x = y.
Proof. by move=> /eq_leif<-/eqP. Qed.

(* lteif *)

Lemma lteif_trans x y z C1 C2 :
  x < y ?<= if C1 -> y < z ?<= if C2 -> x < z ?<= if C1 && C2.
Proof.
case: C1 C2 => [][];
  [exact: le_trans | exact: le_lt_trans | exact: lt_le_trans | exact: lt_trans].
Qed.

Lemma lteif_anti C1 C2 x y :
  (x < y ?<= if C1) && (y < x ?<= if C2) = C1 && C2 && (x == y).
Proof. by case: C1 C2 => [][]; rewrite lte_anti. Qed.

Lemma lteifxx x C : (x < x ?<= if C) = C.
Proof. by case: C; rewrite /= ltexx. Qed.

Lemma lteifNF x y C : y < x ?<= if ~~ C -> x < y ?<= if C = false.
Proof. by case: C => [/lt_geF|/le_gtF]. Qed.

Lemma lteifS x y C : x < y -> x < y ?<= if C.
Proof. by case: C => //= /ltW. Qed.

Lemma lteifT x y : x < y ?<= if true = (x <= y). Proof. by []. Qed.

Lemma lteifF x y : x < y ?<= if false = (x < y). Proof. by []. Qed.

Lemma lteif_orb x y : {morph lteif x y : p q / p || q}.
Proof. by case=> [][] /=; case: comparableP. Qed.

Lemma lteif_andb x y : {morph lteif x y : p q / p && q}.
Proof. by case=> [][] /=; case: comparableP. Qed.

Lemma lteif_imply C1 C2 x y : C1 ==> C2 -> x < y ?<= if C1 -> x < y ?<= if C2.
Proof. by case: C1 C2 => [][] //= _ /ltW. Qed.

Lemma lteifW C x y : x < y ?<= if C -> x <= y.
Proof. by case: C => // /ltW. Qed.

Lemma ltrW_lteif C x y : x < y -> x < y ?<= if C.
Proof. by case: C => // /ltW. Qed.

Lemma lteifN C x y : x < y ?<= if ~~ C -> ~~ (y < x ?<= if C).
Proof. by case: C => /=; case: comparableP. Qed.

(* min and max *)

Lemma minElt x y : min x y = if x < y then x else y. Proof. by []. Qed.
Lemma maxElt x y : max x y = if x < y then y else x. Proof. by []. Qed.

Lemma minEle x y : min x y = if x <= y then x else y.
Proof. by case: comparableP. Qed.

Lemma maxEle x y : max x y = if x <= y then y else x.
Proof. by case: comparableP. Qed.

Lemma comparable_minEgt x y : x >=< y -> min x y = if x > y then y else x.
Proof. by case: comparableP. Qed.
Lemma comparable_maxEgt x y : x >=< y -> max x y = if x > y then x else y.
Proof. by case: comparableP. Qed.
Lemma comparable_minEge x y : x >=< y -> min x y = if x >= y then y else x.
Proof. by case: comparableP. Qed.
Lemma comparable_maxEge x y : x >=< y -> max x y = if x >= y then x else y.
Proof. by case: comparableP. Qed.

Lemma min_l x y : x <= y -> min x y = x. Proof. by case: comparableP. Qed.
Lemma min_r x y : y <= x -> min x y = y. Proof. by case: comparableP. Qed.
Lemma max_l x y : y <= x -> max x y = x. Proof. by case: comparableP. Qed.
Lemma max_r x y : x <= y -> max x y = y. Proof. by case: comparableP. Qed.

Lemma minxx : idempotent (min : T -> T -> T).
Proof. by rewrite /min => x; rewrite ltxx. Qed.

Lemma maxxx : idempotent (max : T -> T -> T).
Proof. by rewrite /max => x; rewrite ltxx. Qed.

Lemma eq_minl x y : (min x y == x) = (x <= y).
Proof. by rewrite !(fun_if, if_arg) eqxx; case: comparableP. Qed.

Lemma eq_maxr x y : (max x y == y) = (x <= y).
Proof. by rewrite !(fun_if, if_arg) eqxx; case: comparableP. Qed.

Lemma min_idPl x y : reflect (min x y = x) (x <= y).
Proof. by apply: (iffP idP); rewrite (rwP eqP) eq_minl. Qed.

Lemma max_idPr x y : reflect (max x y = y) (x <= y).
Proof. by apply: (iffP idP); rewrite (rwP eqP) eq_maxr. Qed.

Lemma min_minKx x y : min (min x y) y = min x y.
Proof. by rewrite !(fun_if, if_arg) ltxx/=; case: comparableP. Qed.

Lemma min_minxK x y : min x (min x y) = min x y.
Proof. by rewrite !(fun_if, if_arg) ltxx/=; case: comparableP. Qed.

Lemma max_maxKx x y : max (max x y) y = max x y.
Proof. by rewrite !(fun_if, if_arg) ltxx/=; case: comparableP. Qed.

Lemma max_maxxK x y : max x (max x y) = max x y.
Proof. by rewrite !(fun_if, if_arg) ltxx/=; case: comparableP. Qed.

Lemma comparable_minl z : {in >=< z &, forall x y, min x y >=< z}.
Proof. by move=> x y cmp_xz cmp_yz; rewrite /min; case: ifP. Qed.

Lemma comparable_minr z : {in >=<%O z &, forall x y, z >=< min x y}.
Proof. by move=> x y cmp_xz cmp_yz; rewrite /min; case: ifP. Qed.

Lemma comparable_maxl z : {in >=< z &, forall x y, max x y >=< z}.
Proof. by move=> x y cmp_xz cmp_yz; rewrite /max; case: ifP. Qed.

Lemma comparable_maxr z : {in >=<%O z &, forall x y, z >=< max x y}.
Proof. by move=> x y cmp_xz cmp_yz; rewrite /max; case: ifP. Qed.

Section Comparable2.
Variables (z x y : T) (cmp_xy : x >=< y).

Lemma comparable_minC : min x y = min y x.
Proof. by case: comparableP cmp_xy. Qed.

Lemma comparable_maxC : max x y = max y x.
Proof. by case: comparableP cmp_xy. Qed.

Lemma comparable_eq_minr : (min x y == y) = (y <= x).
Proof. by rewrite !(fun_if, if_arg) eqxx; case: comparableP cmp_xy. Qed.

Lemma comparable_eq_maxl : (max x y == x) = (y <= x).
Proof. by rewrite !(fun_if, if_arg) eqxx; case: comparableP cmp_xy. Qed.

Lemma comparable_min_idPr : reflect (min x y = y) (y <= x).
Proof. by apply: (iffP idP); rewrite (rwP eqP) comparable_eq_minr. Qed.

Lemma comparable_max_idPl : reflect (max x y = x) (y <= x).
Proof. by apply: (iffP idP); rewrite (rwP eqP) comparable_eq_maxl. Qed.

Lemma comparable_le_minr : (z <= min x y) = (z <= x) && (z <= y).
Proof.
case: comparableP cmp_xy => // [||<-//]; rewrite ?andbb//; last rewrite andbC;
  by case: (comparableP z) => // [/lt_trans xlt/xlt|->] /ltW.
Qed.

Lemma comparable_le_minl : (min x y <= z) = (x <= z) || (y <= z).
Proof.
case: comparableP cmp_xy => // [||<-//]; rewrite ?orbb//; last rewrite orbC;
  by move=> xy _; apply/idP/idP => [->|/orP[]]//; apply/le_trans/ltW.
Qed.

Lemma comparable_lt_minr : (z < min x y) = (z < x) && (z < y).
Proof.
case: comparableP cmp_xy => // [||<-//]; rewrite ?andbb//; last rewrite andbC;
  by case: (comparableP z) => // /lt_trans xlt/xlt.
Qed.

Lemma comparable_lt_minl : (min x y < z) = (x < z) || (y < z).
Proof.
case: comparableP cmp_xy => // [||<-//]; rewrite ?orbb//; last rewrite orbC;
  by move=> xy _; apply/idP/idP => [->|/orP[]]//; apply/lt_trans.
Qed.

Lemma comparable_le_maxr : (z <= max x y) = (z <= x) || (z <= y).
Proof.
case: comparableP cmp_xy => // [||<-//]; rewrite ?orbb//; first rewrite orbC;
  by move=> xy _; apply/idP/idP => [->|/orP[]]// /le_trans->//; apply/ltW.
Qed.

Lemma comparable_le_maxl : (max x y <= z) = (x <= z) && (y <= z).
Proof.
case: comparableP cmp_xy => // [||<-//]; rewrite ?andbb//; first rewrite andbC;
  by case: (comparableP z) => // [ylt /lt_trans /(_ _)/ltW|->/ltW]->.
Qed.

Lemma comparable_lt_maxr : (z < max x y) = (z < x) || (z < y).
Proof.
case: comparableP cmp_xy => // [||<-//]; rewrite ?orbb//; first rewrite orbC;
  by move=> xy _; apply/idP/idP => [->|/orP[]]// /lt_trans->.
Qed.

Lemma comparable_lt_maxl : (max x y < z) = (x < z) && (y < z).
Proof.
case: comparableP cmp_xy => // [||<-//]; rewrite ?andbb//; first rewrite andbC;
by case: (comparableP z) => // ylt /lt_trans->.
Qed.

Lemma comparable_minxK : max (min x y) y = y.
Proof. by rewrite !(fun_if, if_arg) ltxx/=; case: comparableP cmp_xy. Qed.

Lemma comparable_minKx : max x (min x y) = x.
Proof. by rewrite !(fun_if, if_arg) ltxx/=; case: comparableP cmp_xy. Qed.

Lemma comparable_maxxK : min (max x y) y = y.
Proof. by rewrite !(fun_if, if_arg) ltxx/=; case: comparableP cmp_xy. Qed.

Lemma comparable_maxKx : min x (max x y) = x.
Proof. by rewrite !(fun_if, if_arg) ltxx/=; case: comparableP cmp_xy. Qed.

Lemma comparable_lteifNE C : x >=< y -> x < y ?<= if ~~ C = ~~ (y < x ?<= if C).
Proof. by case: C => /=; case: comparableP. Qed.

Lemma comparable_lteif_minr C :
  (z < min x y ?<= if C) = (z < x ?<= if C) && (z < y ?<= if C).
Proof. by case: C; rewrite /= (comparable_le_minr, comparable_lt_minr). Qed.

Lemma comparable_lteif_minl C :
  (min x y < z ?<= if C) = (x < z ?<= if C) || (y < z ?<= if C).
Proof. by case: C; rewrite /= (comparable_le_minl, comparable_lt_minl). Qed.

Lemma comparable_lteif_maxr C :
  (z < max x y ?<= if C) = (z < x ?<= if C) || (z < y ?<= if C).
Proof. by case: C; rewrite /= (comparable_le_maxr, comparable_lt_maxr). Qed.

Lemma comparable_lteif_maxl C :
  (max x y < z ?<= if C) = (x < z ?<= if C) && (y < z ?<= if C).
Proof. by case: C; rewrite /= (comparable_le_maxl, comparable_lt_maxl). Qed.

End Comparable2.

Section Comparable3.
Variables (x y z : T) (cmp_xy : x >=< y) (cmp_xz : x >=< z) (cmp_yz : y >=< z).
Let P := comparableP.

Lemma comparable_minA : min x (min y z) = min (min x y) z.
Proof.
move: cmp_xy cmp_xz cmp_yz; rewrite !(fun_if, if_arg)/=.
move: (P x y) (P x z) (P y z) => [xy|xy|xy|<-] [xz|xz|xz|<-]// []//= yz.
- by have := lt_trans xy (lt_trans yz xz); rewrite ltxx.
- by have := lt_trans xy (lt_trans xz yz); rewrite ltxx.
- by have := lt_trans xy xz; rewrite yz ltxx.
Qed.

Lemma comparable_maxA : max x (max y z) = max (max x y) z.
Proof.
move: cmp_xy cmp_xz cmp_yz; rewrite !(fun_if, if_arg)/=.
move: (P x y) (P x z) (P y z) => [xy|xy|xy|<-] [xz|xz|xz|<-]// []//= yz.
- by have := lt_trans xy (lt_trans yz xz); rewrite ltxx.
- by have := lt_trans xy (lt_trans xz yz); rewrite ltxx.
- by have := lt_trans xy xz; rewrite yz ltxx.
Qed.

Lemma comparable_max_minl : max (min x y) z = min (max x z) (max y z).
Proof.
move: cmp_xy cmp_xz cmp_yz; rewrite !(fun_if, if_arg)/=.
move: (P x y) (P x z) (P y z).
move=> [xy|xy|xy|<-] [xz|xz|xz|<-] [yz|yz|yz|//->]//= _; rewrite ?ltxx//.
- by have := lt_trans xy (lt_trans yz xz); rewrite ltxx.
- by have := lt_trans xy (lt_trans xz yz); rewrite ltxx.
Qed.

Lemma comparable_min_maxl : min (max x y) z = max (min x z) (min y z).
Proof.
move: cmp_xy cmp_xz cmp_yz; rewrite !(fun_if, if_arg)/=.
move: (P x y) (P x z) (P y z).
move=> [xy|xy|xy|<-] [xz|xz|xz|<-] []yz//= _; rewrite ?ltxx//.
- by have := lt_trans xy (lt_trans yz xz); rewrite ltxx.
- by have := lt_trans xy yz; rewrite ltxx.
- by have := lt_trans xy (lt_trans xz yz); rewrite ltxx.
- by have := lt_trans xy xz; rewrite yz ltxx.
Qed.

End Comparable3.

Lemma comparable_minAC x y z : x >=< y -> x >=< z -> y >=< z ->
  min (min x y) z = min (min x z) y.
Proof.
move=> xy xz yz; rewrite -comparable_minA// [min y z]comparable_minC//.
by rewrite comparable_minA// 1?comparable_sym.
Qed.

Lemma comparable_maxAC x y z : x >=< y -> x >=< z -> y >=< z ->
  max (max x y) z = max (max x z) y.
Proof.
move=> xy xz yz; rewrite -comparable_maxA// [max y z]comparable_maxC//.
by rewrite comparable_maxA// 1?comparable_sym.
Qed.

Lemma comparable_minCA x y z : x >=< y -> x >=< z -> y >=< z ->
  min x (min y z) = min y (min x z).
Proof.
move=> xy xz yz; rewrite comparable_minA// [min x y]comparable_minC//.
by rewrite -comparable_minA// 1?comparable_sym.
Qed.

Lemma comparable_maxCA x y z : x >=< y -> x >=< z -> y >=< z ->
  max x (max y z) = max y (max x z).
Proof.
move=> xy xz yz; rewrite comparable_maxA// [max x y]comparable_maxC//.
by rewrite -comparable_maxA// 1?comparable_sym.
Qed.

Lemma comparable_minACA x y z t :
    x >=< y -> x >=< z -> x >=< t -> y >=< z -> y >=< t -> z >=< t ->
  min (min x y) (min z t) = min (min x z) (min y t).
Proof.
move=> xy xz xt yz yt zt; rewrite comparable_minA// ?comparable_minl//.
rewrite [min _ z]comparable_minAC// -comparable_minA// ?comparable_minl//.
by rewrite inE comparable_sym.
Qed.

Lemma comparable_maxACA x y z t :
    x >=< y -> x >=< z -> x >=< t -> y >=< z -> y >=< t -> z >=< t ->
  max (max x y) (max z t) = max (max x z) (max y t).
Proof.
move=> xy xz xt yz yt zt; rewrite comparable_maxA// ?comparable_maxl//.
rewrite [max _ z]comparable_maxAC// -comparable_maxA// ?comparable_maxl//.
by rewrite inE comparable_sym.
Qed.

Lemma comparable_max_minr x y z : x >=< y -> x >=< z -> y >=< z ->
  max x (min y z) = min (max x y) (max x z).
Proof.
move=> xy xz yz; rewrite ![max x _]comparable_maxC// ?comparable_minr//.
by rewrite comparable_max_minl// 1?comparable_sym.
Qed.

Lemma comparable_min_maxr x y z : x >=< y -> x >=< z -> y >=< z ->
  min x (max y z) = max (min x y) (min x z).
Proof.
move=> xy xz yz; rewrite ![min x _]comparable_minC// ?comparable_maxr//.
by rewrite comparable_min_maxl// 1?comparable_sym.
Qed.

Section ArgExtremum.

Context (I : finType) (i0 : I) (P : {pred I}) (F : I -> T) (Pi0 : P i0).
Hypothesis F_comparable : {in P &, forall i j, F i >=< F j}.

Lemma comparable_arg_minP : extremum_spec le P F (arg_min i0 P F).
Proof.
by apply: extremum_inP => // [x _|y x z _ _ _]; [apply: lexx|apply: le_trans].
Qed.

Lemma comparable_arg_maxP : extremum_spec ge P F (arg_max i0 P F).
Proof.
apply: extremum_inP => // [x _|y x z _ _ _|]; [exact: lexx|exact: ge_trans|].
by move=> x y xP yP; rewrite orbC [_ || _]F_comparable.
Qed.

End ArgExtremum.

(* monotonicity *)

Lemma mono_in_leif (A : {pred T}) (f : T -> T) C :
   {in A &, {mono f : x y / x <= y}} ->
  {in A &, forall x y, (f x <= f y ?= iff C) = (x <= y ?= iff C)}.
Proof. by move=> mf x y Ax Ay; rewrite /leif !eq_le !mf. Qed.

Lemma mono_leif (f : T -> T) C :
    {mono f : x y / x <= y} ->
  forall x y, (f x <= f y ?= iff C) = (x <= y ?= iff C).
Proof. by move=> mf x y; rewrite /leif !eq_le !mf. Qed.

Lemma nmono_in_leif (A : {pred T}) (f : T -> T) C :
    {in A &, {mono f : x y /~ x <= y}} ->
  {in A &, forall x y, (f x <= f y ?= iff C) = (y <= x ?= iff C)}.
Proof. by move=> mf x y Ax Ay; rewrite /leif !eq_le !mf. Qed.

Lemma nmono_leif (f : T -> T) C : {mono f : x y /~ x <= y} ->
  forall x y, (f x <= f y ?= iff C) = (y <= x ?= iff C).
Proof. by move=> mf x y; rewrite /leif !eq_le !mf. Qed.

Lemma comparable_bigl x x0 op I (P : pred I) F (s : seq I) :
  {in >=< x &, forall y z, op y z >=< x} -> x0 >=< x ->
  {in P, forall i, F i >=< x} -> \big[op/x0]_(i <- s | P i) F i >=< x.
Proof. by move=> *; elim/big_ind : _. Qed.

Lemma comparable_bigr x x0 op I (P : pred I) F (s : seq I) :
  {in >=<%O x &, forall y z, x >=< op y z} -> x >=< x0 ->
  {in P, forall i, x >=< F i} -> x >=< \big[op/x0]_(i <- s | P i) F i.
Proof. by move=> *; elim/big_ind : _. Qed.

End POrderTheory.

Section ContraTheory.

Context {T1 T2 : eqType} {ord1 : {pOrder T1}} {ord2 : {pOrder T2}}.
Implicit Types (x y : T1) (z t : T2) (b : bool) (m n : nat) (P : Prop).

Local Notation "x <= y" := (x <=_ord1 y).
Local Notation "x < y" := (x <_ord1 y).
Local Notation "x >=< y" := (x >=<_ord1 y).

Lemma comparable_contraTle b x y : x >=< y -> (y < x -> ~~ b) -> (b -> x <= y).
Proof. by case: comparableP; case: b. Qed.

Lemma comparable_contraTlt b x y : x >=< y -> (y <= x -> ~~ b) -> (b -> x < y).
Proof. by case: comparableP; case: b. Qed.

Lemma comparable_contraPle P x y : x >=< y -> (y < x -> ~ P) -> (P -> x <= y).
Proof. by case: comparableP => // _ _ /(_ isT). Qed.

Lemma comparable_contraPlt P x y : x >=< y -> (y <= x -> ~ P) -> (P -> x < y).
Proof. by case: comparableP => // _ _ /(_ isT). Qed.

Lemma comparable_contraNle b x y : x >=< y -> (y < x -> b) -> (~~ b -> x <= y).
Proof. by case: comparableP; case: b. Qed.

Lemma comparable_contraNlt b x y : x >=< y -> (y <= x -> b) -> (~~ b -> x < y).
Proof. by case: comparableP; case: b. Qed.

Lemma comparable_contra_not_le P x y : x >=< y -> (y < x -> P) -> (~ P -> x <= y).
Proof. by case: comparableP => // _ _ /(_ isT). Qed.

Lemma comparable_contra_not_lt P x y : x >=< y -> (y <= x -> P) -> (~ P -> x < y).
Proof. by case: comparableP => // _ _ /(_ isT). Qed.

Lemma comparable_contraFle b x y : x >=< y -> (y < x -> b) -> (b = false -> x <= y).
Proof. by case: comparableP; case: b => // _ _ /implyP. Qed.

Lemma comparable_contraFlt b x y : x >=< y -> (y <= x -> b) -> (b = false -> x < y).
Proof. by case: comparableP; case: b => // _ _ /implyP. Qed.

Lemma contra_leT b x y : (~~ b -> x < y) -> (y <= x -> b).
Proof. by case: comparableP; case: b. Qed.

Lemma contra_ltT b x y : (~~ b -> x <= y) -> (y < x -> b).
Proof. by case: comparableP; case: b. Qed.

Lemma contra_leN b x y : (b -> x < y) -> (y <= x -> ~~ b).
Proof. by case: comparableP; case: b. Qed.

Lemma contra_ltN b x y : (b -> x <= y) -> (y < x -> ~~ b).
Proof. by case: comparableP; case: b. Qed.

Lemma contra_le_not P x y : (P -> x < y) -> (y <= x -> ~ P).
Proof. by case: comparableP => // _ PF _ /PF. Qed.

Lemma contra_lt_not P x y : (P -> x <= y) -> (y < x -> ~ P).
Proof. by case: comparableP => // _ PF _ /PF. Qed.

Lemma contra_leF b x y : (b -> x < y) -> (y <= x -> b = false).
Proof. by case: comparableP; case: b => // _ /implyP. Qed.

Lemma contra_ltF b x y : (b -> x <= y) -> (y < x -> b = false).
Proof. by case: comparableP; case: b => // _ /implyP. Qed.

Lemma comparable_contra_leq_le m n x y : x >=< y ->
  (y < x -> (n < m)%N) -> ((m <= n)%N -> x <= y).
Proof. by case: comparableP; case: ltngtP. Qed.

Lemma comparable_contra_leq_lt m n x y : x >=< y ->
  (y <= x -> (n < m)%N) -> ((m <= n)%N -> x < y).
Proof. by case: comparableP; case: ltngtP. Qed.

Lemma comparable_contra_ltn_le m n x y : x >=< y ->
  (y < x -> (n <= m)%N) -> ((m < n)%N -> x <= y).
Proof. by case: comparableP; case: ltngtP. Qed.

Lemma comparable_contra_ltn_lt m n x y : x >=< y ->
  (y <= x -> (n <= m)%N) -> ((m < n)%N -> x < y).
Proof. by case: comparableP; case: ltngtP. Qed.

Lemma contra_le_leq x y m n : ((n < m)%N -> y < x) -> (x <= y -> (m <= n)%N).
Proof. by case: comparableP; case: ltngtP. Qed.

Lemma contra_le_ltn x y m n : ((n <= m)%N -> y < x) -> (x <= y -> (m < n)%N).
Proof. by case: comparableP; case: ltngtP. Qed.

Lemma contra_lt_leq x y m n : ((n < m)%N -> y <= x) -> (x < y -> (m <= n)%N).
Proof. by case: comparableP; case: ltngtP. Qed.

Lemma contra_lt_ltn x y m n : ((n <= m)%N -> y <= x) -> (x < y -> (m < n)%N).
Proof. by case: comparableP; case: ltngtP. Qed.

Lemma comparable_contra_le x y z t : z >=<_ord2 t ->
  (t <_ord2 z -> y < x) -> (x <= y -> z <=_ord2 t).
Proof. by do 2![case: comparableP => //= ?]. Qed.

Lemma comparable_contra_le_lt x y z t : z >=<_ord2 t ->
  (t <=_ord2 z -> y < x) -> (x <= y -> z <_ord2 t).
Proof. by do 2![case: comparableP => //= ?]. Qed.

Lemma comparable_contra_lt_le x y z t : z >=<_ord2 t ->
  (t <_ord2 z -> y <= x) -> (x < y -> z <=_ord2 t).
Proof. by do 2![case: comparableP => //= ?]. Qed.

Lemma comparable_contra_lt x y z t : z >=<_ord2 t ->
 (t <=_ord2 z -> y <= x) -> (x < y -> z <_ord2 t).
Proof. by do 2![case: comparableP => //= ?]. Qed.

End ContraTheory.

Section POrderMonotonyTheory.

Context {T T' : eqType} {ord : {pOrder T}} {ord' : {pOrder T'}}.
Implicit Types (m n p : nat) (x y z : T) (u v w : T').
Variables (D D' : {pred T}) (f : T -> T').

Let leT_refl := @lexx _ ord.
Let leT'_refl := @lexx _ ord'.
Let ltT_neqAle := @lt_neqAle _ ord.
Let ltT'_neqAle := @lt_neqAle _ ord'.
Let ltT_def := @lt_def _ ord.
Let leT_anti := @le_anti _ ord.

Let ge_antiT : antisymmetric (ge ord).
Proof. by move=> ? ? /le_anti. Qed.

Lemma ltW_homo : {homo f : x y / x <_ord y >-> x <_ord' y} ->
                 {homo f : x y / x <=_ord y >-> x <=_ord' y}.
Proof. exact: homoW. Qed.

Lemma ltW_nhomo : {homo f : x y / y <_ord x >-> x <_ord' y} ->
                  {homo f : x y / y <=_ord x >-> x <=_ord' y}.
Proof. exact: homoW. Qed.

Lemma inj_homo_lt :
  injective f -> {homo f : x y / x <=_ord y >-> x <=_ord' y} ->
  {homo f : x y / x <_ord y >-> x <_ord' y}.
Proof. exact: inj_homo. Qed.

Lemma inj_nhomo_lt :
  injective f -> {homo f : x y / y <=_ord x >-> x <=_ord' y} ->
  {homo f : x y / y <_ord x >-> x <_ord' y}.
Proof. exact: inj_homo. Qed.

Lemma inc_inj : {mono f : x y / x <=_ord y >-> x <=_ord' y} -> injective f.
Proof. exact: mono_inj. Qed.

Lemma dec_inj : {mono f : x y / y <=_ord x >-> x <=_ord' y} -> injective f.
Proof. exact: mono_inj. Qed.

Lemma leW_mono : {mono f : x y / x <=_ord y >-> x <=_ord' y} ->
                 {mono f : x y / x <_ord y >-> x <_ord' y}.
Proof. exact: anti_mono. Qed.

Lemma leW_nmono : {mono f : x y / y <=_ord x >-> x <=_ord' y} ->
                  {mono f : x y / y <_ord x >-> x <_ord' y}.
Proof. exact: anti_mono. Qed.

(* Monotony in D D' *)
Lemma ltW_homo_in : {in D & D', {homo f : x y / x <_ord y >-> x <_ord' y}} ->
                    {in D & D', {homo f : x y / x <=_ord y >-> x <=_ord' y}}.
Proof. exact: homoW_in. Qed.

Lemma ltW_nhomo_in : {in D & D', {homo f : x y / y <_ord x >-> x <_ord' y}} ->
                     {in D & D', {homo f : x y / y <=_ord x >-> x <=_ord' y}}.
Proof. exact: homoW_in. Qed.

Lemma inj_homo_lt_in :
  {in D & D', injective f} ->
  {in D & D', {homo f : x y / x <=_ord y >-> x <=_ord' y}} ->
  {in D & D', {homo f : x y / x <_ord y >-> x <_ord' y}}.
Proof. exact: inj_homo_in. Qed.

Lemma inj_nhomo_lt_in :
  {in D & D', injective f} ->
  {in D & D', {homo f : x y / y <=_ord x >-> x <=_ord' y}} ->
  {in D & D', {homo f : x y / y <_ord x >-> x <_ord' y}}.
Proof. exact: inj_homo_in. Qed.

Lemma inc_inj_in : {in D &, {mono f : x y / x <=_ord y >-> x <=_ord' y}} ->
                   {in D &, injective f}.
Proof. exact: mono_inj_in. Qed.

Lemma dec_inj_in : {in D &, {mono f : x y / y <=_ord x >-> x <=_ord' y}} ->
                   {in D &, injective f}.
Proof. exact: mono_inj_in. Qed.

Lemma leW_mono_in : {in D &, {mono f : x y / x <=_ord y >-> x <=_ord' y}} ->
                    {in D &, {mono f : x y / x <_ord y >-> x <_ord' y}}.
Proof. exact: anti_mono_in. Qed.

Lemma leW_nmono_in : {in D &, {mono f : x y / y <=_ord x >-> x <=_ord' y}} ->
                     {in D &, {mono f : x y / y <_ord x >-> x <_ord' y}}.
Proof. exact: anti_mono_in. Qed.

End POrderMonotonyTheory.

End POrderTheory.

#[global] Hint Extern 0 (is_true (le _ _ _)) => apply: lexx : core.
#[global] Hint Resolve lexx ltxx lt_irreflexive ltW lt_eqF : core.

Arguments leifP {T ord x y C}.
Arguments leif_refl {T ord x C}.
Arguments mono_in_leif [T ord A f C].
Arguments nmono_in_leif [T ord A f C].
Arguments mono_leif [T ord f C].
Arguments nmono_leif [T ord f C].
Arguments min_idPl {T ord x y}.
Arguments max_idPr {T ord x y}.
Arguments comparable_min_idPr {T ord x y _}.
Arguments comparable_max_idPl {T ord x y _}.

Module Import BPOrderTheory.
Section BPOrderTheory.
Context {T : eqType} {ord : {bPOrder T}}.
Implicit Types (x y : T).

Local Notation "x <= y" := (x <=_ord y).
Local Notation "x < y" := (x <_ord y).
Local Notation "0" := (bottom ord).

Lemma le0x x : 0 <= x. Proof. by case: ord => ? ? ? []. Qed.

Lemma lex0 x : (x <= 0) = (x == 0).
Proof. by rewrite le_eqVlt (le_gtF (le0x _)) orbF. Qed.

Lemma ltx0 x : (x < 0) = false.
Proof. by rewrite lt_neqAle lex0 andNb. Qed.

Lemma lt0x x : (0 < x) = (x != 0).
Proof. by rewrite lt_neqAle le0x andbT eq_sym. Qed.

Variant eq0_xor_gt0 x : bool -> bool -> Set :=
    Eq0NotPOs : x = 0 -> eq0_xor_gt0 x true false
  | POsNotEq0 : 0 < x -> eq0_xor_gt0 x false true.

Lemma posxP x : eq0_xor_gt0 x (x == 0) (0 < x).
Proof. by rewrite lt0x; have [] := eqVneq; constructor; rewrite ?lt0x. Qed.

End BPOrderTheory.
End BPOrderTheory.

Module Import TPOrderTheory.
Section TPOrderTheory.
Context {T : eqType} {ord : {tPOrder T}}.
Let ord_dual := [bPOrder of dual_rel <=:ord].
Implicit Types (x y : T).

Local Notation "x <= y" := (x <=_ord y).
Local Notation "x < y" := (x <_ord y).
Local Notation "1" := (top ord).

Lemma lex1 (x : T) : x <= 1. Proof. exact: (@le0x _ ord_dual). Qed.
Lemma le1x x : (1 <= x) = (x == 1). Proof. exact: (@lex0 _ ord_dual). Qed.
Lemma lt1x x : (1 < x) = false. Proof. exact: (@ltx0 _ ord_dual). Qed.
Lemma ltx1 x : (x < 1) = (x != 1). Proof. exact: (@lt0x _ ord_dual). Qed.

End TPOrderTheory.
End TPOrderTheory.

#[global] Hint Extern 0 (is_true (le _ (bottom _) _)) => apply: le0x : core.
#[global] Hint Extern 0 (is_true (le _ _ (top _))) => apply: lex1 : core.

Module Import MeetTheory.
Section MeetTheory.
Context {L : eqType} {ord : {meetOrder L}}.
Implicit Types (x y : L).

Local Notation meet := (meet ord).

Local Notation "x <= y" := (x <=_ord y).
Local Notation "x `&` y" := (meet x y).

Lemma meetC : commutative meet. Proof. by case: ord => ? ? ? [? []]. Qed.
Lemma meetA : associative meet. Proof. by case: ord => ? ? ? [? []]. Qed.
Lemma leEmeet x y : (x <= y) = (x `&` y == x).
Proof. by case: ord => ? ? ? [? []]. Qed.

Lemma meetxx : idempotent meet.
Proof. by move=> x; apply/eqP; rewrite -leEmeet. Qed.
Lemma meetAC : right_commutative meet.
Proof. by move=> x y z; rewrite -!meetA [X in _ `&` X]meetC. Qed.
Lemma meetCA : left_commutative meet.
Proof. by move=> x y z; rewrite !meetA [X in X `&` _]meetC. Qed.
Lemma meetACA : interchange meet meet.
Proof. by move=> x y z t; rewrite !meetA [X in X `&` _]meetAC. Qed.

Lemma meetKI y x : x `&` (x `&` y) = x `&` y.
Proof. by rewrite meetA meetxx. Qed.
Lemma meetIK y x : (x `&` y) `&` y = x `&` y.
Proof. by rewrite -meetA meetxx. Qed.
Lemma meetKIC y x : x `&` (y `&` x) = x `&` y.
Proof. by rewrite meetC meetIK meetC. Qed.
Lemma meetIKC y x : y `&` x `&` y = x `&` y.
Proof. by rewrite meetAC meetC meetxx. Qed.

(* interaction with order *)

Lemma lexI x y z : (x <= y `&` z) = (x <= y) && (x <= z).
Proof.
rewrite !leEmeet; apply/eqP/andP => [<-|[/eqP<- /eqP<-]].
  by rewrite meetA meetIK eqxx -meetA meetACA meetxx meetAC eqxx.
by rewrite -[X in X `&` _]meetA meetIK meetA.
Qed.

Lemma leIxl x y z : y <= x -> y `&` z <= x.
Proof. by rewrite !leEmeet meetAC => /eqP ->. Qed.

Lemma leIxr x y z : z <= x -> y `&` z <= x.
Proof. by rewrite !leEmeet -meetA => /eqP ->. Qed.

Lemma leIx2 x y z : (y <= x) || (z <= x) -> y `&` z <= x.
Proof. by case/orP => [/leIxl|/leIxr]. Qed.

Lemma leIr x y : y `&` x <= x.
Proof. by rewrite leIx2 ?lexx ?orbT. Qed.

Lemma leIl x y : x `&` y <= x.
Proof. by rewrite leIx2 ?lexx ?orbT. Qed.

Lemma meet_idPl {x y} : reflect (x `&` y = x) (x <= y).
Proof. by rewrite leEmeet; apply/eqP. Qed.
Lemma meet_idPr {x y} : reflect (y `&` x = x) (x <= y).
Proof. by rewrite meetC; apply/meet_idPl. Qed.

Lemma meet_l x y : x <= y -> x `&` y = x. Proof. exact/meet_idPl. Qed.
Lemma meet_r x y : y <= x -> x `&` y = y. Proof. exact/meet_idPr. Qed.

Lemma leIidl x y : (x <= x `&` y) = (x <= y).
Proof. by rewrite !leEmeet meetKI. Qed.
Lemma leIidr x y : (x <= y `&` x) = (x <= y).
Proof. by rewrite !leEmeet meetKIC. Qed.

Lemma eq_meetl x y : (x `&` y == x) = (x <= y).
Proof. by apply/esym/leEmeet. Qed.

Lemma eq_meetr x y : (x `&` y == y) = (y <= x).
Proof. by rewrite meetC eq_meetl. Qed.

Lemma leI2 x y z t : x <= z -> y <= t -> x `&` y <= z `&` t.
Proof. by move=> xz yt; rewrite lexI !leIx2 ?xz ?yt ?orbT //. Qed.

End MeetTheory.
End MeetTheory.

Arguments meet_idPl {L ord x y}.
Arguments meet_idPr {L ord x y}.

Module Import BMeetTheory.
Section BMeetTheory.
Context {L : eqType} {ord : {bMeetOrder L}}.

Local Notation meet := (meet ord).
Local Notation "0" := (bottom ord).

Lemma meet0x : left_zero 0 meet. Proof. by move=> x; apply/meet_idPl. Qed.
Lemma meetx0 : right_zero 0 meet. Proof. by move=> x; apply/meet_idPr. Qed.

Canonical meet_muloid := Monoid.MulLaw meet0x meetx0.

End BMeetTheory.
End BMeetTheory.

Module Import TMeetTheory.
Section TMeetTheory.
Context {L : eqType} {ord : {tMeetOrder L}}.
Implicit Types (I : finType) (T : eqType) (x y : L).

Local Notation meet := (meet ord).

Local Notation "x <= y" := (x <=_ord y).
Local Notation "x `&` y" := (meet x y).
Local Notation "1" := (top ord).

Lemma meetx1 : right_id 1 meet. Proof. by move=> x; apply/meet_idPl. Qed.
Lemma meet1x : left_id 1 meet. Proof. by move=> x; apply/meet_idPr. Qed.

Lemma meet_eq1 x y : (x `&` y == 1) = (x == 1) && (y == 1).
Proof. by rewrite !(@eq_le _ ord) !lex1 lexI. Qed.

Canonical meet_monoid := Monoid.Law meetA meet1x meetx1.
Canonical meet_comoid := Monoid.ComLaw meetC.

Lemma meets_inf_seq T (r : seq T) (P : {pred T}) (F : T -> L) (x : T) :
  x \in r -> P x -> \big[meet/1]_(i <- r | P i) F i <= F x.
Proof. by move=> xr Px; rewrite (big_rem x) ?Px //= leIl. Qed.

Lemma meets_max_seq T (r : seq T) (P : {pred T}) (F : T -> L) (x : T) (u : L) :
  x \in r -> P x -> F x <= u -> \big[meet/1]_(x <- r | P x) F x <= u.
Proof. by move=> ? ?; apply/le_trans/meets_inf_seq. Qed.

Lemma meets_inf I (j : I) (P : {pred I}) (F : I -> L) :
   P j -> \big[meet/1]_(i | P i) F i <= F j.
Proof. exact: meets_inf_seq. Qed.

Lemma meets_max I (j : I) (u : L) (P : {pred I}) (F : I -> L) :
   P j -> F j <= u -> \big[meet/1]_(i | P i) F i <= u.
Proof. exact: meets_max_seq. Qed.

Lemma meets_ge J (r : seq J) (P : {pred J}) (F : J -> L) (u : L) :
  (forall x : J, P x -> u <= F x) -> u <= \big[meet/1]_(x <- r | P x) F x.
Proof. by move=> leFm; elim/big_rec: _ => // i x Px xu; rewrite lexI leFm. Qed.

Lemma meetsP_seq T (r : seq T) (P : {pred T}) (F : T -> L) (l : L) :
  reflect (forall x : T, x \in r -> P x -> l <= F x)
          (l <= \big[meet/1]_(x <- r | P x) F x).
Proof.
apply: (iffP idP) => leFm => [x xr Px|].
  exact/(le_trans leFm)/meets_inf_seq.
by rewrite big_seq_cond meets_ge // => x /andP[/leFm].
Qed.

Lemma meetsP I (l : L) (P : {pred I}) (F : I -> L) :
   reflect (forall i : I, P i -> l <= F i) (l <= \big[meet/1]_(i | P i) F i).
Proof. by apply: (iffP (meetsP_seq _ _ _ _)) => H ? ?; apply: H. Qed.

Lemma le_meets I (A B : {set I}) (F : I -> L) :
   A \subset B -> \big[meet/1]_(i in B) F i <= \big[meet/1]_(i in A) F i.
Proof. by move=> /subsetP AB; apply/meetsP => i iA; apply/meets_inf/AB. Qed.

Lemma meets_setU I (A B : {set I}) (F : I -> L) :
  \big[meet/1]_(i in (A :|: B)) F i =
  \big[meet/1]_(i in A) F i `&` \big[meet/1]_(i in B) F i.
Proof.
rewrite -!big_enum; have /= <- := @big_cat _ _ meet_comoid.
apply/eq_big_idem; first exact: meetxx.
by move=> ?; rewrite mem_cat !mem_enum inE.
Qed.

Lemma meets_seq I (r : seq I) (F : I -> L) :
  \big[meet/1]_(i <- r) F i = \big[meet/1]_(i in r) F i.
Proof.
by rewrite -big_enum; apply/eq_big_idem => ?; rewrite /= ?meetxx ?mem_enum.
Qed.

End TMeetTheory.
End TMeetTheory.

Module Import JoinTheory.
Section JoinTheory.
Context {L : eqType} {ord : {joinOrder L}}.
Let ord_dual := [meetOrder of dual_rel <=:ord].
Implicit Types (x y : L).

Local Notation join := (join ord).

Local Notation "x <= y" := (x <=_ord y).
Local Notation "x `|` y" := (join x y).

Lemma joinC : commutative join. Proof. exact: (@meetC _ ord_dual). Qed.
Lemma joinA : associative join. Proof. exact: (@meetA _ ord_dual). Qed.
Lemma leEjoin x y : (x <= y) = (x `|` y == y).
Proof. by rewrite joinC; apply: (@leEmeet _ ord_dual). Qed.

Lemma joinxx : idempotent join. Proof. exact: (@meetxx _ ord_dual). Qed.
Lemma joinAC : right_commutative join. Proof. exact: (@meetAC _ ord_dual). Qed.
Lemma joinCA : left_commutative join. Proof. exact: (@meetCA _ ord_dual). Qed.
Lemma joinACA : interchange join join.
Proof. exact: (@meetACA _ ord_dual). Qed.

Lemma joinKU y x : x `|` (x `|` y) = x `|` y.
Proof. exact: (@meetKI _ ord_dual). Qed.
Lemma joinUK y x : (x `|` y) `|` y = x `|` y.
Proof. exact: (@meetIK _ ord_dual). Qed.
Lemma joinKUC y x : x `|` (y `|` x) = x `|` y.
Proof. exact: (@meetKIC _ ord_dual). Qed.
Lemma joinUKC y x : y `|` x `|` y = x `|` y.
Proof. exact: (@meetIKC _ ord_dual). Qed.

(* interaction with order *)
Lemma leUx x y z : (x `|` y <= z) = (x <= z) && (y <= z).
Proof. exact: (@lexI _ ord_dual). Qed.
Lemma lexUl x y z : x <= y -> x <= y `|` z.
Proof. exact: (@leIxl _ ord_dual). Qed.
Lemma lexUr x y z : x <= z -> x <= y `|` z.
Proof. exact: (@leIxr _ ord_dual). Qed.
Lemma lexU2 x y z : (x <= y) || (x <= z) -> x <= y `|` z.
Proof. exact: (@leIx2 _ ord_dual). Qed.

Lemma leUr x y : x <= y `|` x. Proof. exact: (@leIr _ ord_dual). Qed.
Lemma leUl x y : x <= x `|` y. Proof. exact: (@leIl _ ord_dual). Qed.

Lemma join_idPl {x y} : reflect (y `|` x = y) (x <= y).
Proof. exact: (@meet_idPl _ ord_dual). Qed.
Lemma join_idPr {x y} : reflect (x `|` y = y) (x <= y).
Proof. exact: (@meet_idPr _ ord_dual). Qed.

Lemma join_l x y : y <= x -> x `|` y = x. Proof. exact/join_idPl. Qed.
Lemma join_r x y : x <= y -> x `|` y = y. Proof. exact/join_idPr. Qed.

Lemma leUidl x y : (x `|` y <= y) = (x <= y).
Proof. exact: (@leIidr _ ord_dual). Qed.
Lemma leUidr x y : (y `|` x <= y) = (x <= y).
Proof. exact: (@leIidl _ ord_dual). Qed.

Lemma eq_joinl x y : (x `|` y == x) = (y <= x).
Proof. exact: (@eq_meetl _ ord_dual). Qed.
Lemma eq_joinr x y : (x `|` y == y) = (x <= y).
Proof. exact: (@eq_meetr _ ord_dual). Qed.

Lemma leU2 x y z t : x <= z -> y <= t -> x `|` y <= z `|` t.
Proof. exact: (@leI2 _ ord_dual). Qed.

End JoinTheory.
End JoinTheory.

Arguments join_idPl {L ord x y}.
Arguments join_idPr {L ord x y}.

Module Import BJoinTheory.
Section BJoinTheory.
Context {L : eqType} {ord : {bJoinOrder L}}.
Let ord_dual := [tMeetOrder of dual_rel <=:ord].
Implicit Types (I : finType) (T : eqType) (x y : L).

Local Notation join := (join ord).

Local Notation "x <= y" := (x <=_ord y).
Local Notation "x `|` y" := (join x y).
Local Notation "0" := (bottom ord).

Lemma joinx0 : right_id 0 join. Proof. exact: (@meetx1 _ ord_dual). Qed.
Lemma join0x : left_id 0 join. Proof. exact: (@meet1x _ ord_dual). Qed.

Lemma join_eq0 x y : (x `|` y == 0) = (x == 0) && (y == 0).
Proof. exact: (@meet_eq1 _ ord_dual). Qed.

Canonical join_monoid := Monoid.Law joinA join0x joinx0.
Canonical join_comoid := Monoid.ComLaw joinC.

Lemma joins_sup_seq T (r : seq T) (P : {pred T}) (F : T -> L) (x : T) :
  x \in r -> P x -> F x <= \big[join/0]_(i <- r | P i) F i.
Proof. exact: (@meets_inf_seq _ ord_dual). Qed.

Lemma joins_min_seq T (r : seq T) (P : {pred T}) (F : T -> L) (x : T) (l : L) :
  x \in r -> P x -> l <= F x -> l <= \big[join/0]_(x <- r | P x) F x.
Proof. exact: (@meets_max_seq _ ord_dual). Qed.

Lemma joins_sup I (j : I) (P : {pred I}) (F : I -> L) :
  P j -> F j <= \big[join/0]_(i | P i) F i.
Proof. exact: (@meets_inf _ ord_dual). Qed.

Lemma joins_min I (j : I) (l : L) (P : {pred I}) (F : I -> L) :
  P j -> l <= F j -> l <= \big[join/0]_(i | P i) F i.
Proof. exact: (@meets_max _ ord_dual). Qed.

Lemma joins_le J (r : seq J) (P : {pred J}) (F : J -> L) (u : L) :
  (forall x : J, P x -> F x <= u) -> \big[join/0]_(x <- r | P x) F x <= u.
Proof. exact: (@meets_ge _ ord_dual). Qed.

Lemma joinsP_seq T (r : seq T) (P : {pred T}) (F : T -> L) (u : L) :
  reflect (forall x : T, x \in r -> P x -> F x <= u)
          (\big[join/0]_(x <- r | P x) F x <= u).
Proof. exact: (@meetsP_seq _ ord_dual). Qed.

Lemma joinsP I (u : L) (P : {pred I}) (F : I -> L) :
  reflect (forall i : I, P i -> F i <= u) (\big[join/0]_(i | P i) F i <= u).
Proof. exact: (@meetsP _ ord_dual). Qed.

Lemma le_joins I (A B : {set I}) (F : I -> L) :
  A \subset B -> \big[join/0]_(i in A) F i <= \big[join/0]_(i in B) F i.
Proof. exact: (@le_meets _ ord_dual). Qed.

Lemma joins_setU I (A B : {set I}) (F : I -> L) :
  \big[join/0]_(i in (A :|: B)) F i =
  \big[join/0]_(i in A) F i `|` \big[join/0]_(i in B) F i.
Proof. exact: (@meets_setU _ ord_dual). Qed.

Lemma joins_seq I (r : seq I) (F : I -> L) :
  \big[join/0]_(i <- r) F i = \big[join/0]_(i in r) F i.
Proof. exact: (@meets_seq _ ord_dual). Qed.

End BJoinTheory.
End BJoinTheory.

Module Import TJoinTheory.
Section TJoinTheory.
Context {L : eqType} {ord : {tJoinOrder L}}.
Let ord_dual := [bMeetOrder of dual_rel <=:ord].

Local Notation join := (join ord).
Local Notation "1" := (top ord).

Lemma joinx1 : right_zero 1 join. Proof. exact: (@meetx0 _ ord_dual). Qed.
Lemma join1x : left_zero 1 join. Proof. exact: (@meet0x _ ord_dual). Qed.

Canonical join_muloid := Monoid.MulLaw join1x joinx1.

End TJoinTheory.
End TJoinTheory.

Module Import LatticeTheory.
Section LatticeTheory.
Context {L : eqType} {ord : {lattice L}}.
Implicit Types (x y : L).

Local Notation le := (le ord).
Local Notation lt := (lt ord).
Local Notation comparable := (comparable ord).
Local Notation min := (min ord).
Local Notation max := (max ord).
Local Notation meet := (meet ord).
Local Notation join := (join ord).
Local Notation lel_xor_gt := (lel_xor_gt le lt).
Local Notation ltl_xor_ge := (ltl_xor_ge le lt).
Local Notation comparel := (comparel lt).
Local Notation incomparel := (incomparel lt comparable meet join).

Local Notation "x <= y" := (x <=_ord y).
Local Notation "x < y" := (x <_ord y).
Local Notation "x >= y" := (x >=_ord y) (only parsing).
Local Notation "x > y" := (x >_ord y) (only parsing).
Local Notation "x >=< y" := (comparable x y).
Local Notation "x `&` y" := (meet x y).
Local Notation "x `|` y" := (join x y).

Lemma meetUK x y : (x `&` y) `|` y = y.
Proof. by apply/eqP; rewrite eq_joinr -eq_meetl meetIK. Qed.

Lemma meetUKC x y : (y `&` x) `|` y = y. Proof. by rewrite meetC meetUK. Qed.
Lemma meetKUC y x : x `|` (y `&` x) = x. Proof. by rewrite joinC meetUK. Qed.
Lemma meetKU y x : x `|` (x `&` y) = x. Proof. by rewrite meetC meetKUC. Qed.

Lemma joinIK x y : (x `|` y) `&` y = y.
Proof. by apply/eqP; rewrite eq_meetr -eq_joinl joinUK. Qed.

Lemma joinIKC x y : (y `|` x) `&` y = y. Proof. by rewrite joinC joinIK. Qed.
Lemma joinKIC y x : x `&` (y `|` x) = x. Proof. by rewrite meetC joinIK. Qed.
Lemma joinKI y x : x `&` (x `|` y) = x. Proof. by rewrite joinC joinKIC. Qed.

(* comparison predicates *)

Lemma lcomparableP x y : incomparel x y
  (min y x) (min x y) (max y x) (max x y)
  (y `&` x) (x `&` y) (y `|` x) (x `|` y)
  (y == x) (x == y) (x >= y) (x <= y) (x > y) (x < y) (y >=< x) (x >=< y).
Proof.
by case: (comparableP x) => [hxy|hxy|hxy|->]; do 1?have hxy' := ltW hxy;
   rewrite ?(meetxx, joinxx);
   rewrite ?(meet_l hxy', meet_r hxy', join_l hxy', join_r hxy');
   constructor.
Qed.

Lemma lcomparable_ltgtP x y : x >=< y ->
  comparel x y (min y x) (min x y) (max y x) (max x y)
               (y `&` x) (x `&` y) (y `|` x) (x `|` y)
               (y == x) (x == y) (x >= y) (x <= y) (x > y) (x < y).
Proof. by case: (lcomparableP x) => // *; constructor. Qed.

Lemma lcomparable_leP x y : x >=< y ->
  lel_xor_gt x y (min y x) (min x y) (max y x) (max x y)
                 (y `&` x) (x `&` y) (y `|` x) (x `|` y) (x <= y) (y < x).
Proof. by case/lcomparable_ltgtP => [/ltW xy|xy|->]; constructor. Qed.

Lemma lcomparable_ltP x y : x >=< y ->
  ltl_xor_ge x y (min y x) (min x y) (max y x) (max x y)
                 (y `&` x) (x `&` y) (y `|` x) (x `|` y) (y <= x) (x < y).
Proof. by case/lcomparable_ltgtP => [xy|/ltW xy|->]; constructor. Qed.

End LatticeTheory.
End LatticeTheory.

Module Import DistrLatticeTheory.
Section DistrLatticeTheory.
Context {L : eqType} {ord : {distrLattice L}}.
Implicit Types (x y : L).

Local Notation meet := (meet ord).
Local Notation join := (join ord).

Local Notation "x `&` y" := (meet x y).
Local Notation "x `|` y" := (join x y).

Lemma meetUl : left_distributive meet join.
Proof. by case: ord => ? ? ? ? [? []]. Qed.

Lemma joinIl : left_distributive join meet.
Proof. by case: ord => ? ? ? ? [? []]. Qed.

Lemma meetUr : right_distributive meet join.
Proof. by move=> x y z; rewrite ![x `&` _]meetC meetUl. Qed.

Lemma joinIr : right_distributive join meet.
Proof. by move=> x y z; rewrite ![x `|` _]joinC joinIl. Qed.

End DistrLatticeTheory.
End DistrLatticeTheory.

Module Import BDistrLatticeTheory.
Section BDistrLatticeTheory.
Context {L : eqType} {ord : {bDistrLattice L}}.
Implicit Types (I : finType) (T : eqType) (x y z : L).

Local Notation meet := (meet ord).
Local Notation join := (join ord).

Local Notation "x <= y" := (x <=_ord y).
Local Notation "x `&` y" := (meet x y).
Local Notation "x `|` y" := (join x y).
Local Notation "0" := (bottom ord).
(* Distributive lattice theory with 0 *)

Canonical join_addoid := Monoid.AddLaw (@meetUl _ ord) (@meetUr _ _).

Lemma leU2l_le y t x z : x `&` t = 0 -> x `|` y <= z `|` t -> x <= z.
Proof.
by move=> xIt0 /(leI2 (lexx x)); rewrite joinKI meetUr xIt0 joinx0 leIidl.
Qed.

Lemma leU2r_le y t x z : x `&` t = 0 -> y `|` x <= t `|` z -> x <= z.
Proof. by rewrite joinC [_ `|` z]joinC => /leU2l_le H /H. Qed.

Lemma disjoint_lexUl z x y : x `&` z = 0 -> (x <= y `|` z) = (x <= y).
Proof.
move=> xz0; apply/idP/idP=> xy; last by rewrite lexU2 ?xy.
by apply: (@leU2l_le x z); rewrite ?joinxx.
Qed.

Lemma disjoint_lexUr z x y : x `&` z = 0 -> (x <= z `|` y) = (x <= y).
Proof. by move=> xz0; rewrite joinC; rewrite disjoint_lexUl. Qed.

Lemma leU2E x y z t : x `&` t = 0 -> y `&` z = 0 ->
  (x `|` y <= z `|` t) = (x <= z) && (y <= t).
Proof.
move=> dxt dyz; apply/idP/andP; last by case=> ? ?; exact: leU2.
by move=> lexyzt; rewrite (leU2l_le _ lexyzt) // (leU2r_le _ lexyzt).
Qed.

Lemma joins_disjoint I (d : L) (P : {pred I}) (F : I -> L) :
   (forall i : I, P i -> d `&` F i = 0) -> d `&` \big[join/0]_(i | P i) F i = 0.
Proof.
move=> d_Fi_disj; have : \big[andb/true]_(i | P i) (d `&` F i == 0).
  rewrite big_all_cond; apply/allP => i _ /=.
  by apply/implyP => /d_Fi_disj ->.
elim/big_rec2: _ => [|i y]; first by rewrite meetx0.
case; rewrite (andbF, andbT) // => Pi /(_ isT) dy /eqP dFi.
by rewrite meetUr dy dFi joinxx.
Qed.

End BDistrLatticeTheory.
End BDistrLatticeTheory.

Module Import TDistrLatticeTheory.
Section TDistrLatticeTheory.
Context {L : eqType} {ord : {tDistrLattice L}}.
Let ord_dual := [bDistrLattice of dual_rel <=:ord].
Implicit Types (I : finType) (T : eqType) (x y z : L).

Local Notation meet := (meet ord).
Local Notation join := (join ord).

Local Notation "x <= y" := (x <=_ord y).
Local Notation "x `&` y" := (meet x y).
Local Notation "x `|` y" := (join x y).
Local Notation "1" := (top ord).
(* Distributive lattice theory with 1 *)

Canonical meet_addoid := Monoid.AddLaw (@joinIl _ ord) (@joinIr _ _).

Lemma leI2l_le y t x z : y `|` z = 1 -> x `&` y <= z `&` t -> x <= z.
Proof. rewrite joinC; exact: (@leU2l_le _ ord_dual). Qed.

Lemma leI2r_le y t x z : y `|` z = 1 -> y `&` x <= t `&` z -> x <= z.
Proof. rewrite joinC; exact: (@leU2r_le _ ord_dual). Qed.

Lemma cover_leIxl z x y : z `|` y = 1 -> (x `&` z <= y) = (x <= y).
Proof. rewrite joinC; exact: (@disjoint_lexUl _ ord_dual). Qed.

Lemma cover_leIxr z x y : z `|` y = 1 -> (z `&` x <= y) = (x <= y).
Proof. rewrite joinC; exact: (@disjoint_lexUr _ ord_dual). Qed.

Lemma leI2E x y z t : x `|` t = 1 -> y `|` z = 1 ->
  (x `&` y <= z `&` t) = (x <= z) && (y <= t).
Proof. by move=> ? ?; apply: (@leU2E _ ord_dual); rewrite meetC. Qed.

Lemma meets_total I (d : L) (P : {pred I}) (F : I -> L) :
   (forall i : I, P i -> d `|` F i = 1) -> d `|` \big[meet/1]_(i | P i) F i = 1.
Proof. exact: (@joins_disjoint _ ord_dual). Qed.

End TDistrLatticeTheory.
End TDistrLatticeTheory.

Module Import TotalTheory.
Section TotalTheory.
Context {T : eqType} {ord : {totalOrder T}}.
Implicit Types (x y z t : T) (s : seq T).

Local Notation le := (le ord).
Local Notation lt := (lt ord).
Local Notation ge := (ge ord).
Local Notation min := (min ord).
Local Notation max := (max ord).
Local Notation arg_min := (arg_min ord).
Local Notation arg_max := (arg_max ord).

Local Notation "x <= y" := (x <=_ord y).
Local Notation "x < y" := (x <_ord y).
Local Notation "x >= y" := (x >=_ord y) (only parsing).
Local Notation "x > y" := (x >_ord y) (only parsing).
Local Notation "x >=< y" := (comparable ord x y).
Local Notation "x < y ?<= 'if' C" := (lteif ord x y C).
Local Notation "x `&` y" := (meet ord x y).
Local Notation "x `|` y" := (join ord x y).

Lemma le_total : total le. Proof. by case: ord => ? ? ? ? []. Qed.
Hint Resolve le_total : core.

Lemma ge_total : total ge. Proof. by move=> ? ?; apply: le_total. Qed.
Hint Resolve ge_total : core.

Lemma comparableT x y : x >=< y. Proof. exact: le_total. Qed.
Hint Resolve comparableT : core.

Lemma leNgt x y : (x <= y) = ~~ (y < x). Proof. exact: comparable_leNgt. Qed.

Lemma ltNge x y : (x < y) = ~~ (y <= x). Proof. exact: comparable_ltNge. Qed.

Definition ltgtP x y := LatticeTheory.lcomparable_ltgtP (comparableT x y).
Definition leP x y := LatticeTheory.lcomparable_leP (comparableT x y).
Definition ltP x y := LatticeTheory.lcomparable_ltP (comparableT x y).

Lemma wlog_le P :
     (forall x y, P y x -> P x y) -> (forall x y, x <= y -> P x y) ->
   forall x y, P x y.
Proof. by move=> sP hP x y; case: (leP x y) => [| /ltW] /hP // /sP. Qed.

Lemma wlog_lt P :
    (forall x, P x x) ->
    (forall x y, (P y x -> P x y)) -> (forall x y, x < y -> P x y) ->
  forall x y, P x y.
Proof. by move=> rP sP hP x y; case: (ltgtP x y) => [||->] // /hP // /sP. Qed.

Lemma neq_lt x y : (x != y) = (x < y) || (y < x). Proof. by case: ltgtP. Qed.

Lemma lt_total x y : x != y -> (x < y) || (y < x). Proof. by case: ltgtP. Qed.

Lemma eq_leLR x y z t :
  (x <= y -> z <= t) -> (y < x -> t < z) -> (x <= y) = (z <= t).
Proof. by rewrite !ltNge => ? /contraTT ?; apply/idP/idP. Qed.

Lemma eq_leRL x y z t :
  (x <= y -> z <= t) -> (y < x -> t < z) -> (z <= t) = (x <= y).
Proof. by move=> *; symmetry; apply: eq_leLR. Qed.

Lemma eq_ltLR x y z t :
  (x < y -> z < t) -> (y <= x -> t <= z) -> (x < y) = (z < t).
Proof. by rewrite !leNgt => ? /contraTT ?; apply/idP/idP. Qed.

Lemma eq_ltRL x y z t :
  (x < y -> z < t) -> (y <= x -> t <= z) -> (z < t) = (x < y).
Proof. by move=> *; symmetry; apply: eq_ltLR. Qed.

Lemma sort_le_sorted s : sorted le (sort le s).
Proof. exact: sort_sorted. Qed.
Hint Resolve sort_le_sorted : core.

Lemma sort_lt_sorted s : sorted lt (sort le s) = uniq s.
Proof. by rewrite lt_sorted_uniq_le sort_uniq sort_le_sorted andbT. Qed.

Lemma count_le_gt x s :
  count (fun y => y <= x) s = size s - count (fun y => y > x) s.
Proof.
rewrite -(count_predC (fun y => y > x)) addKn.
by apply: eq_count => y; rewrite /= leNgt.
Qed.

Lemma count_lt_ge x s :
  count (fun y => y < x) s = size s - count (fun y => y >= x) s.
Proof.
rewrite -(count_predC (fun y => y >= x)) addKn.
by apply: eq_count => y; rewrite /= ltNge.
Qed.

Lemma sorted_filter_gt x s :
  sorted <=:ord s -> [seq y <- s | x < y] = drop (count (le^~ x) s) s.
Proof.
move=> s_sorted; rewrite count_le_gt -[LHS]revK -filter_rev.
rewrite (@sorted_filter_lt _ [totalOrder of dual_rel <=:ord]).
  by rewrite take_rev revK count_rev.
by rewrite rev_sorted.
Qed.

Lemma sorted_filter_ge x s :
  sorted <=:ord s -> [seq y <- s | x <= y] = drop (count (lt^~ x) s) s.
Proof.
move=> s_sorted; rewrite count_lt_ge -[LHS]revK -filter_rev.
rewrite (@sorted_filter_le _ [totalOrder of dual_rel <=:ord]).
  by rewrite take_rev revK count_rev.
by rewrite rev_sorted.
Qed.

Lemma nth_count_ge x x0 s i : sorted <=:ord s ->
  (count (lt^~ x) s <= i < size s)%N -> x <= nth x0 s i.
Proof.
move=> ss /andP[ige ilt]; rewrite -(subnKC ige) -nth_drop -sorted_filter_ge //.
apply/(all_nthP _ (filter_all _ _)).
by rewrite size_filter ltn_subLR // count_lt_ge subnK // count_size.
Qed.

Lemma nth_count_gt x x0 s i : sorted <=:ord s ->
  (count (le^~ x) s <= i < size s)%N -> x < nth x0 s i.
Proof.
move=> ss /andP[ige ilt]; rewrite -(subnKC ige) -nth_drop -sorted_filter_gt //.
apply/(all_nthP _ (filter_all _ _)).
by rewrite size_filter ltn_subLR // count_le_gt subnK // count_size.
Qed.

Lemma nth_count_eq x x0 s i : sorted <=:ord s ->
  (count (lt^~ x) s <= i < count (le^~ x) s)%N -> nth x0 s i = x.
Proof.
move=> ss /andP[ige ilt]; apply/(@le_anti _ ord).
by rewrite nth_count_le// nth_count_ge// ige (leq_trans ilt (count_size _ _)).
Qed.

(* max and min is join and meet *)

Lemma meetEtotal x y : x `&` y = min x y. Proof. by case: leP. Qed.
Lemma joinEtotal x y : x `|` y = max x y. Proof. by case: leP. Qed.

(* max and min theory *)

Lemma minEgt x y : min x y = if x > y then y else x. Proof. by case: ltP. Qed.
Lemma maxEgt x y : max x y = if x > y then x else y. Proof. by case: ltP. Qed.
Lemma minEge x y : min x y = if x >= y then y else x. Proof. by case: leP. Qed.
Lemma maxEge x y : max x y = if x >= y then x else y. Proof. by case: leP. Qed.

Lemma minC : commutative min. Proof. by move=> x y; apply: comparable_minC. Qed.

Lemma maxC : commutative max. Proof. by move=> x y; apply: comparable_maxC. Qed.

Lemma minA : associative min.
Proof. by move=> x y z; apply: comparable_minA. Qed.

Lemma maxA : associative max.
Proof. by move=> x y z; apply: comparable_maxA. Qed.

Lemma minAC : right_commutative min.
Proof. by move=> x y z; apply: comparable_minAC. Qed.

Lemma maxAC : right_commutative max.
Proof. by move=> x y z; apply: comparable_maxAC. Qed.

Lemma minCA : left_commutative min.
Proof. by move=> x y z; apply: comparable_minCA. Qed.

Lemma maxCA : left_commutative max.
Proof. by move=> x y z; apply: comparable_maxCA. Qed.

Lemma minACA : interchange min min.
Proof. by move=> x y z t; apply: comparable_minACA. Qed.

Lemma maxACA : interchange max max.
Proof. by move=> x y z t; apply: comparable_maxACA. Qed.

Lemma eq_minr x y : (min x y == y) = (y <= x).
Proof. exact: comparable_eq_minr. Qed.

Lemma eq_maxl x y : (max x y == x) = (y <= x).
Proof. exact: comparable_eq_maxl. Qed.

Lemma min_idPr x y : reflect (min x y = y) (y <= x).
Proof. exact: comparable_min_idPr. Qed.

Lemma max_idPl x y : reflect (max x y = x) (y <= x).
Proof. exact: comparable_max_idPl. Qed.

Lemma le_minr z x y : (z <= min x y) = (z <= x) && (z <= y).
Proof. exact: comparable_le_minr. Qed.

Lemma le_minl z x y : (min x y <= z) = (x <= z) || (y <= z).
Proof. exact: comparable_le_minl. Qed.

Lemma lt_minr z x y : (z < min x y) = (z < x) && (z < y).
Proof. exact: comparable_lt_minr. Qed.

Lemma lt_minl z x y : (min x y < z) = (x < z) || (y < z).
Proof. exact: comparable_lt_minl. Qed.

Lemma le_maxr z x y : (z <= max x y) = (z <= x) || (z <= y).
Proof. exact: comparable_le_maxr. Qed.

Lemma le_maxl z x y : (max x y <= z) = (x <= z) && (y <= z).
Proof. exact: comparable_le_maxl. Qed.

Lemma lt_maxr z x y : (z < max x y) = (z < x) || (z < y).
Proof. exact: comparable_lt_maxr. Qed.

Lemma lt_maxl z x y : (max x y < z) = (x < z) && (y < z).
Proof. exact: comparable_lt_maxl. Qed.

Lemma minxK x y : max (min x y) y = y. Proof. exact: comparable_minxK. Qed.
Lemma minKx x y : max x (min x y) = x. Proof. exact: comparable_minKx. Qed.
Lemma maxxK x y : min (max x y) y = y. Proof. exact: comparable_maxxK. Qed.
Lemma maxKx x y : min x (max x y) = x. Proof. exact: comparable_maxKx. Qed.

Lemma max_minl : left_distributive max min.
Proof. by move=> x y z; apply: comparable_max_minl. Qed.

Lemma min_maxl : left_distributive min max.
Proof. by move=> x y z; apply: comparable_min_maxl. Qed.

Lemma max_minr : right_distributive max min.
Proof. by move=> x y z; apply: comparable_max_minr. Qed.

Lemma min_maxr : right_distributive min max.
Proof. by move=> x y z; apply: comparable_min_maxr. Qed.

Lemma leIx x y z : (y `&` z <= x) = (y <= x) || (z <= x).
Proof. by rewrite meetEtotal le_minl. Qed.

Lemma lexU x y z : (x <= y `|` z) = (x <= y) || (x <= z).
Proof. by rewrite joinEtotal le_maxr. Qed.

Lemma ltxI x y z : (x < y `&` z) = (x < y) && (x < z).
Proof. by rewrite !ltNge leIx negb_or. Qed.

Lemma ltIx x y z : (y `&` z < x) = (y < x) || (z < x).
Proof. by rewrite !ltNge lexI negb_and. Qed.

Lemma ltxU x y z : (x < y `|` z) = (x < y) || (x < z).
Proof. by rewrite !ltNge leUx negb_and. Qed.

Lemma ltUx x y z : (y `|` z < x) = (y < x) && (z < x).
Proof. by rewrite !ltNge lexU negb_or. Qed.

Definition ltexI := (@lexI _ ord, ltxI).
Definition lteIx := (leIx, ltIx).
Definition ltexU := (lexU, ltxU).
Definition lteUx := (@leUx _ ord, ltUx).

(* lteif *)

Lemma lteifNE x y C : x < y ?<= if ~~ C = ~~ (y < x ?<= if C).
Proof. by case: C => /=; case: leP. Qed.

Lemma lteif_minr z x y C :
  (z < min x y ?<= if C) = (z < x ?<= if C) && (z < y ?<= if C).
Proof. by case: C; rewrite /= (le_minr, lt_minr). Qed.

Lemma lteif_minl z x y C :
  (min x y < z ?<= if C) = (x < z ?<= if C) || (y < z ?<= if C).
Proof. by case: C; rewrite /= (le_minl, lt_minl). Qed.

Lemma lteif_maxr z x y C :
  (z < max x y ?<= if C) = (z < x ?<= if C) || (z < y ?<= if C).
Proof. by case: C; rewrite /= (le_maxr, lt_maxr). Qed.

Lemma lteif_maxl z x y C :
  (max x y < z ?<= if C) = (x < z ?<= if C) && (y < z ?<= if C).
Proof. by case: C; rewrite /= (le_maxl, lt_maxl). Qed.

Section ArgExtremum.

Context (I : finType) (i0 : I) (P : {pred I}) (F : I -> T) (Pi0 : P i0).

Lemma arg_minP: extremum_spec le P F (arg_min i0 P F).
Proof. by apply: extremumP => //; apply: le_trans. Qed.

Lemma arg_maxP: extremum_spec ge P F (arg_max i0 P F).
Proof. by apply: extremumP => //; [apply: ge_refl | apply: ge_trans]. Qed.

End ArgExtremum.

End TotalTheory.

#[global] Hint Resolve le_total : core.
#[global] Hint Resolve ge_total : core.
#[global] Hint Resolve comparableT : core.
#[global] Hint Resolve sort_le_sorted : core.

Arguments min_idPr {T ord x y}.
Arguments max_idPl {T ord x y}.

(* contra lemmas *)

Section ContraTheory.

Context {T1 T2 : eqType} {ord1 : {pOrder T1}} {ord2 : {totalOrder T2}}.
Implicit Types (x y : T1) (z t : T2) (b : bool) (m n : nat) (P : Prop).

Local Notation "x <= y" := (x <=_ord2 y).
Local Notation "x < y" := (x <_ord2 y).

Lemma contraTle b z t : (t < z -> ~~ b) -> (b -> z <= t).
Proof. exact: comparable_contraTle. Qed.

Lemma contraTlt b z t : (t <= z -> ~~ b) -> (b -> z < t).
Proof. exact: comparable_contraTlt. Qed.

Lemma contraPle P z t : (t < z -> ~ P) -> (P -> z <= t).
Proof. exact: comparable_contraPle. Qed.

Lemma contraPlt P z t : (t <= z -> ~ P) -> (P -> z < t).
Proof. exact: comparable_contraPlt. Qed.

Lemma contraNle b z t : (t < z -> b) -> (~~ b -> z <= t).
Proof. exact: comparable_contraNle. Qed.

Lemma contraNlt b z t : (t <= z -> b) -> (~~ b -> z < t).
Proof. exact: comparable_contraNlt. Qed.

Lemma contra_not_le P z t : (t < z -> P) -> (~ P -> z <= t).
Proof. exact: comparable_contra_not_le. Qed.

Lemma contra_not_lt P z t : (t <= z -> P) -> (~ P -> z < t).
Proof. exact: comparable_contra_not_lt. Qed.

Lemma contraFle b z t : (t < z -> b) -> (b = false -> z <= t).
Proof. exact: comparable_contraFle. Qed.

Lemma contraFlt b z t : (t <= z -> b) -> (b = false -> z < t).
Proof. exact: comparable_contraFlt. Qed.

Lemma contra_leq_le m n z t : (t < z -> (n < m)%N) -> ((m <= n)%N -> z <= t).
Proof. exact: comparable_contra_leq_le. Qed.

Lemma contra_leq_lt m n z t : (t <= z -> (n < m)%N) -> ((m <= n)%N -> z < t).
Proof. exact: comparable_contra_leq_lt. Qed.

Lemma contra_ltn_le m n z t : (t < z -> (n <= m)%N) -> ((m < n)%N -> z <= t).
Proof. exact: comparable_contra_ltn_le. Qed.

Lemma contra_ltn_lt m n z t : (t <= z -> (n <= m)%N) -> ((m < n)%N -> z < t).
Proof. exact: comparable_contra_ltn_lt. Qed.

Lemma contra_le x y z t : (t < z -> y <_ord1 x) -> (x <=_ord1 y -> z <= t).
Proof. exact: comparable_contra_le. Qed.

Lemma contra_le_lt x y z t : (t <= z -> y <_ord1 x) -> (x <=_ord1 y -> z < t).
Proof. exact: comparable_contra_le_lt. Qed.

Lemma contra_lt_le x y z t : (t < z -> y <=_ord1 x) -> (x <_ord1 y -> z <= t).
Proof. exact: comparable_contra_lt_le. Qed.

Lemma contra_lt x y z t : (t <= z -> y <=_ord1 x) -> (x <_ord1 y -> z < t).
Proof. exact: comparable_contra_lt. Qed.

End ContraTheory.

Section TotalMonotonyTheory.

Context {T T' : eqType} {ord : {totalOrder T}} {ord' : {pOrder T'}}.
Variables (D : {pred T}) (f : T -> T').

Let leT'_anti   := @le_anti _ ord'.
Let ltT_neqAle  := @lt_neqAle _ ord.
Let ltT'_neqAle := @lt_neqAle _ ord'.
Let ltT_def     := @lt_def _ ord.
Let leT_total   := @le_total _ ord.

Lemma le_mono : {homo f : x y / x <_ord y >-> x <_ord' y} ->
                {mono f : x y / x <=_ord y >-> x <=_ord' y}.
Proof. exact: total_homo_mono. Qed.

Lemma le_nmono : {homo f : x y / y <_ord x >-> x <_ord' y} ->
                 {mono f : x y / y <=_ord x >-> x <=_ord' y}.
Proof. exact: total_homo_mono. Qed.

Lemma le_mono_in : {in D &, {homo f : x y / x <_ord y >-> x <_ord' y}} ->
                   {in D &, {mono f : x y / x <=_ord y >-> x <=_ord' y}}.
Proof. exact: total_homo_mono_in. Qed.

Lemma le_nmono_in : {in D &, {homo f : x y / y <_ord x >-> x <_ord' y}} ->
                    {in D &, {mono f : x y / y <=_ord x >->  x <=_ord' y}}.
Proof. exact: total_homo_mono_in. Qed.

End TotalMonotonyTheory.
End TotalTheory.

(*************)
(* FACTORIES *)
(*************)

Module LePOrderMixin.
Section LePOrderMixin.
(* TODO: use a phantom type to get rid of an explicit eqType. *)
Variable (T : eqType).

Record of_ := Build {
  le       : rel T;
  lt       : rel T;
  lt_def   : forall x y, lt x y = (y != x) && (le x y);
  lexx     : reflexive     le;
  le_anti  : antisymmetric le;
  le_trans : transitive    le;
}.

Variable (m : of_).

Lemma lt_def' (x y : T) : lt m y x = (y != x) && le m y x.
Proof. by rewrite (lt_def m) eq_sym. Qed.

Lemma le_anti' x y : le m x y -> le m y x -> x = y.
Proof. by move=> xy yx; apply/(@le_anti m)/andP. Qed.

Definition porderMixin :=
  POrder.Mixin (lt_def m) lt_def' (lexx m) le_anti' (@le_trans m).

End LePOrderMixin.

Module Exports.
Notation lePOrderMixin := of_.
Notation LePOrderMixin := Build.
Coercion porderMixin : of_ >-> POrder.mixin_of.
End Exports.

End LePOrderMixin.
Import LePOrderMixin.Exports.

Module BottomRelMixin.
Section BottomRelMixin.
Variable (T : eqType) (ord : {pOrder T}).

Record of_ := Build {
  bottom : T;
  le0x : forall x, bottom <=_ord x;
}.

Definition bPOrderMixin (m : of_) : BPOrder.mixin_of ord (bottom m) := le0x m.

End BottomRelMixin.

Module Exports.
Notation bottomRelMixin := of_.
Notation BottomRelMixin := Build.
Coercion bPOrderMixin : of_ >-> BPOrder.mixin_of.
End Exports.

End BottomRelMixin.
Import BottomRelMixin.Exports.

Module TopRelMixin.
Section TopRelMixin.
Variable (T : eqType) (ord : {pOrder T}).

Record of_ := Build {
  top : T;
  lex1 : forall x, x <=_ord top;
}.

Definition tPOrderMixin (m : of_) : TPOrder.mixin_of ord (top m) := lex1 m.

End TopRelMixin.

Module Exports.
Notation topRelMixin := of_.
Notation TopRelMixin := Build.
Coercion tPOrderMixin : of_ >-> TPOrder.mixin_of.
End Exports.

End TopRelMixin.
Import TopRelMixin.Exports.

Module MeetRelMixin.
Section MeetRelMixin.
Variable (T : eqType) (ord : {pOrder T}).

Record of_ := Build {
  meet : T -> T -> T;
  meetC   : commutative meet;
  meetA   : associative meet;
  leEmeet : forall x y, (x <=_ord y) = (meet x y == x);
}.

Definition meetMixin (m : of_) : Meet.mixin_of ord (meet m) :=
  Meet.Mixin (meetC m) (meetA m) (leEmeet m).

End MeetRelMixin.

Module Exports.
Notation meetRelMixin := of_.
Notation MeetRelMixin := Build.
Coercion meetMixin : of_ >-> Meet.mixin_of.
End Exports.

End MeetRelMixin.
Import MeetRelMixin.Exports.

Module JoinRelMixin.
Section JoinRelMixin.
Variable (T : eqType) (ord : {pOrder T}).

Record of_ := Build {
  join : T -> T -> T;
  joinC   : commutative join;
  joinA   : associative join;
  leEjoin : forall x y, (y <=_ord x) = (join x y == x);
}.

Definition joinMixin (m : of_) : Join.mixin_of ord (join m) :=
  @Meet.Mixin _ (dual_pOrder ord) _ (joinC m) (joinA m) (leEjoin m).

End JoinRelMixin.

Module Exports.
Notation joinRelMixin := of_.
Notation JoinRelMixin := Build.
Coercion joinMixin : of_ >-> Join.mixin_of.
End Exports.

End JoinRelMixin.
Import JoinRelMixin.Exports.

Module DistrLatticeRelMixin.
Section DistrLatticeRelMixin.
Variable (T : eqType) (ord : {lattice T}).

Record of_ := Build { meetUl : left_distributive (meet ord) (join ord) }.

Variable (m : of_).

Lemma meetUr : right_distributive (meet ord) (join ord).
Proof. by move=> x y z; rewrite ![meet _ x _]meetC meetUl. Qed.

Lemma joinIl : left_distributive (join ord) (meet ord).
Proof. by move=> x y z; rewrite meetUr joinIK meetUl // -joinA meetUKC. Qed.

Definition distrLatticeMixin := DistrLattice.Mixin (meetUl m) joinIl.

End DistrLatticeRelMixin.

Module Exports.
Notation distrLatticeRelMixin := of_.
Notation DistrLatticeRelMixin := Build.
Coercion distrLatticeMixin : of_ >-> DistrLattice.mixin_of.
End Exports.

End DistrLatticeRelMixin.
Import DistrLatticeRelMixin.Exports.

Module LatticePOrderRelMixin.
Section LatticePOrderRelMixin.
Variable (T : eqType) (ord : {pOrder T}).

Record of_ := Build {
  meet : T -> T -> T;
  join : T -> T -> T;
  meetC : commutative meet;
  joinC : commutative join;
  meetA : associative meet;
  joinA : associative join;
  joinKI : forall y x, meet x (join x y) = x;
  meetKU : forall y x, join x (meet x y) = x;
  leEmeet : forall x y, (x <=_ord y) = (meet x y == x);
}.

Variable (m : of_).

Definition meetMixin := MeetRelMixin (meetC m) (meetA m) (leEmeet m).

Lemma leEjoin x y : (y <=_ord x) = (join m x y == x).
Proof.
rewrite (leEmeet m); apply/eqP/eqP => <-.
  by rewrite meetC // meetKU.
by rewrite joinC // joinKI.
Qed.

Definition joinMixin := JoinRelMixin (joinC m) (joinA m) leEjoin.

End LatticePOrderRelMixin.

Module Exports.
Notation latticePOrderRelMixin := of_.
Notation LatticePOrderRelMixin := Build.
Coercion meetMixin : of_ >-> meetRelMixin.
Coercion joinMixin : of_ >-> joinRelMixin.
Definition LatticeOfPOrder T ord (m : @of_ T ord) : {lattice T} :=
  [lattice of <=:(JoinOrder <=:(MeetOrder _ _ _ m) _ _ m)].
End Exports.

End LatticePOrderRelMixin.
Import LatticePOrderRelMixin.Exports.

Module DistrLatticePOrderRelMixin.
Section DistrLatticePOrderRelMixin.
Variable (T : eqType) (ord : {pOrder T}).

Record of_ := Build {
  meet : T -> T -> T;
  join : T -> T -> T;
  meetC : commutative meet;
  joinC : commutative join;
  meetA : associative meet;
  joinA : associative join;
  joinKI : forall y x, meet x (join x y) = x;
  meetKU : forall y x, join x (meet x y) = x;
  leEmeet : forall x y, (x <=_ord y) = (meet x y == x);
  meetUl : left_distributive meet join;
}.

Variable (m : of_).

Definition latticeMixin : latticePOrderRelMixin ord :=
  LatticePOrderRelMixin
    (meetC m) (joinC m) (meetA m) (joinA m) (joinKI m) (meetKU m) (leEmeet m).

Definition distrLatticeMixin :=
  @DistrLatticeRelMixin _ (LatticeOfPOrder latticeMixin) (meetUl m).

End DistrLatticePOrderRelMixin.

Module Exports.
Notation distrLatticePOrderRelMixin := of_.
Notation DistrLatticePOrderRelMixin := Build.
Coercion latticeMixin : of_ >-> latticePOrderRelMixin.
Coercion distrLatticeMixin : of_ >-> distrLatticeRelMixin.
End Exports.

End DistrLatticePOrderRelMixin.
Import DistrLatticePOrderRelMixin.Exports.

Module TotalLatticeRelMixin.
Section TotalLatticeRelMixin.
Variable (T : eqType) (ord : {lattice T}).
Definition of_ := total <=:ord.

Variable (m : of_).
Implicit Types (x y z : T).

Let comparableT x y : x >=<_ord y := m x y.

Fact meetUl : left_distributive (meet ord) (join ord).
Proof.
pose leP x y := lcomparable_leP (comparableT x y).
move=> x y z; case: (leP x z); case: (leP y z); case: (leP x y);
  case: (leP x z); case: (leP y z); case: (leP x y) => //= xy yz xz _ _ _;
  rewrite ?joinxx //.
- by move: (le_lt_trans xz (lt_trans yz xy)); rewrite ltxx.
- by move: (lt_le_trans xz (le_trans xy yz)); rewrite ltxx.
Qed.

Definition distrLatticeMixin := DistrLatticeRelMixin meetUl.

Definition totalMixin : Total.mixin_of ord := m.

End TotalLatticeRelMixin.

Module Exports.
Notation totalLatticeRelMixin := of_.
Coercion distrLatticeMixin : of_ >-> distrLatticeRelMixin.
Coercion totalMixin : of_ >-> Total.mixin_of.
Definition OrderOfLattice T ord (m : @of_ T ord) : {totalOrder T} :=
  TotalOrder <=:(DistrLattice _ _ _ _ m) _ _ _ m.
End Exports.

End TotalLatticeRelMixin.
Import TotalLatticeRelMixin.Exports.

Module TotalPOrderRelMixin.
Section TotalPOrderRelMixin.
Variable (T : eqType) (ord : {pOrder T}).
Definition of_ := total <=:ord.

Variable (m : of_).
Implicit Types (x y z : T).

Let meet := min ord.
Let join := max ord.

Let comparableT x y : x >=<_ord y := m x y.

Fact meetC : commutative meet. Proof. by move=> *; apply: comparable_minC. Qed.
Fact joinC : commutative join. Proof. by move=> *; apply: comparable_maxC. Qed.
Fact meetA : associative meet. Proof. by move=> *; apply: comparable_minA. Qed.
Fact joinA : associative join. Proof. by move=> *; apply: comparable_maxA. Qed.
Fact joinKI y x : meet x (join x y) = x. Proof. exact: comparable_maxKx. Qed.
Fact meetKU y x : join x (meet x y) = x. Proof. exact: comparable_minKx. Qed.

Fact leEmeet x y : (x <=_ord y) = (meet x y == x).
Proof. by rewrite eq_minl. Qed.

Definition latticeMixin : latticePOrderRelMixin ord :=
  LatticePOrderRelMixin meetC joinC meetA joinA joinKI meetKU leEmeet.

Definition totalMixin : totalLatticeRelMixin (LatticeOfPOrder latticeMixin) :=
  m.

End TotalPOrderRelMixin.

Module Exports.
Notation totalPOrderRelMixin := of_.
Coercion latticeMixin : of_ >-> latticePOrderRelMixin.
Coercion totalMixin : of_ >-> totalLatticeRelMixin.
End Exports.

End TotalPOrderRelMixin.
Import TotalPOrderRelMixin.Exports.

Module TotalMeetOrderRelMixin.
Section TotalMeetOrderRelMixin.
Variable (T : eqType) (ord : {meetOrder T}).
Definition of_ := total <=:ord.

Variable (m : of_).

Definition joinMixin : joinRelMixin ord := (m : totalPOrderRelMixin ord).

Let ord_lattice := [lattice of <=:(JoinOrder _ _ _ joinMixin)].

Definition totalMixin : totalLatticeRelMixin ord_lattice := m.

End TotalMeetOrderRelMixin.

Module Exports.
Notation totalMeetOrderRelMixin := of_.
Coercion joinMixin : of_ >-> joinRelMixin.
Coercion totalMixin : of_ >-> totalLatticeRelMixin.
End Exports.

End TotalMeetOrderRelMixin.
Import TotalMeetOrderRelMixin.Exports.

Module TotalJoinOrderRelMixin.
Section TotalJoinOrderRelMixin.
Variable (T : eqType) (ord : {joinOrder T}).
Definition of_ := total <=:ord.

Variable (m : of_).

Definition meetMixin : meetRelMixin ord := (m : totalPOrderRelMixin ord).

Let ord_lattice := [lattice of <=:(MeetOrder _ _ _ meetMixin)].

Definition totalMixin : totalLatticeRelMixin ord_lattice := m.

End TotalJoinOrderRelMixin.

Module Exports.
Notation totalJoinOrderRelMixin := of_.
Coercion meetMixin : of_ >-> meetRelMixin.
Coercion totalMixin : of_ >-> totalLatticeRelMixin.
End Exports.

End TotalJoinOrderRelMixin.
Import TotalJoinOrderRelMixin.Exports.

Module LtPOrderMixin.
Section LtPOrderMixin.
Variable (T : eqType).

Record of_ := Build {
  le       : rel T;
  lt       : rel T;
  le_def   : forall x y, le x y = (x == y) || lt x y;
  lt_irr   : irreflexive lt;
  lt_trans : transitive lt;
}.

Variable (m : of_).

Fact lt_asym x y : (lt m x y && lt m y x) = false.
Proof. by apply/negP => /andP [] xy /(lt_trans xy); rewrite (lt_irr m x). Qed.

Fact lt_def x y : lt m x y = (y != x) && le m x y.
Proof. by rewrite le_def //; case: eqVneq => //= ->; rewrite lt_irr. Qed.

Fact le_refl : reflexive (le m).
Proof. by move=> ?; rewrite le_def // eqxx. Qed.

Fact le_anti : antisymmetric (le m).
Proof.
by move=> ? ?; rewrite !le_def // eq_sym -orb_andr lt_asym; case: eqP.
Qed.

Fact le_trans : transitive (le m).
Proof.
by move=> y x z; rewrite !le_def // => /predU1P [-> //|ltxy] /predU1P [<-|ltyz];
  rewrite ?ltxy ?(lt_trans ltxy ltyz) ?orbT.
Qed.

Definition porderMixin : lePOrderMixin T :=
  LePOrderMixin lt_def le_refl le_anti le_trans.

End LtPOrderMixin.

Module Exports.
Notation ltPOrderMixin := of_.
Notation LtPOrderMixin := Build.
Coercion porderMixin : of_ >-> lePOrderMixin.
End Exports.

End LtPOrderMixin.
Import LtPOrderMixin.Exports.

Module MeetJoinMixin.
Section MeetJoinMixin.
Variable (T : eqType).

Record of_ := Build {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  join : T -> T -> T;
  le_def : forall x y : T, le x y = (meet x y == x);
  lt_def : forall x y : T, lt x y = (y != x) && le x y;
  meetC : commutative meet;
  joinC : commutative join;
  meetA : associative meet;
  joinA : associative join;
  joinKI : forall y x : T, meet x (join x y) = x;
  meetKU : forall y x : T, join x (meet x y) = x;
  meetxx : idempotent meet;
}.

Variable (m : of_).

Fact le_refl : reflexive (le m).
Proof. by move=> x; rewrite le_def ?meetxx. Qed.

Fact le_anti : antisymmetric (le m).
Proof. by move=> x y; rewrite !le_def // meetC // => /andP [] /eqP -> /eqP. Qed.

Fact le_trans : transitive (le m).
Proof.
move=> y x z; rewrite !le_def // => /eqP lexy /eqP leyz; apply/eqP.
by rewrite -[in LHS]lexy -meetA // leyz.
Qed.

Definition porderMixin : lePOrderMixin T :=
  LePOrderMixin (lt_def m) le_refl le_anti le_trans.

Definition latticeMixin :
  latticePOrderRelMixin (POrder (le m) (lt m) porderMixin) :=
  @LatticePOrderRelMixin
    _ (POrder (le m) (lt m) porderMixin) (meet m) (join m)
    (meetC m) (joinC m) (meetA m) (joinA m) (joinKI m) (meetKU m) (le_def m).

End MeetJoinMixin.

Module Exports.
Notation meetJoinMixin := of_.
Notation MeetJoinMixin := Build.
Coercion porderMixin : of_ >-> lePOrderMixin.
Coercion latticeMixin : of_ >-> latticePOrderRelMixin.
End Exports.

End MeetJoinMixin.
Import MeetJoinMixin.Exports.

Module DistrMeetJoinMixin.
Section DistrMeetJoinMixin.
Variable (T : eqType).

Record of_ := Build {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  join : T -> T -> T;
  le_def : forall x y : T, le x y = (meet x y == x);
  lt_def : forall x y : T, lt x y = (y != x) && le x y;
  meetC : commutative meet;
  joinC : commutative join;
  meetA : associative meet;
  joinA : associative join;
  joinKI : forall y x : T, meet x (join x y) = x;
  meetKU : forall y x : T, join x (meet x y) = x;
  meetUl : left_distributive meet join;
  meetxx : idempotent meet;
}.

Variable (m : of_).

Definition latticeMixin : meetJoinMixin T :=
  MeetJoinMixin (le_def m) (lt_def m) (meetC m) (joinC m) (meetA m) (joinA m)
                (joinKI m) (meetKU m) (meetxx m).

Let le_lattice := LatticeOfPOrder latticeMixin.

Definition distrLatticeMixin : distrLatticeRelMixin le_lattice :=
  @DistrLatticeRelMixin _ le_lattice (meetUl m).

End DistrMeetJoinMixin.

Module Exports.
Notation distrMeetJoinMixin := of_.
Notation DistrMeetJoinMixin := Build.
Coercion latticeMixin : of_ >-> meetJoinMixin.
Coercion distrLatticeMixin : of_ >-> DistrLatticeRelMixin.of_.
End Exports.

End DistrMeetJoinMixin.
Import DistrMeetJoinMixin.Exports.

Module LeOrderMixin.
Section LeOrderMixin.
Variables (T : eqType).

Record of_ := Build {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  join : T -> T -> T;
  lt_def : forall x y, lt x y = (y != x) && le x y;
  meet_def : forall x y, meet x y = if lt x y then x else y;
  join_def : forall x y, join x y = if lt x y then y else x;
  le_anti : antisymmetric le;
  le_trans : transitive le;
  le_total : total le;
}.

Variables (m : of_).

Fact le_refl : reflexive (le m).
Proof. by move=> x; case: (le m x x) (le_total m x x). Qed.

Definition porderMixin :=
  LePOrderMixin (lt_def m) le_refl (@le_anti m) (@le_trans m).

Let le_order :=
  OrderOfLattice
    (le_total m : totalPOrderRelMixin (POrder (le m) (lt m) porderMixin)).

Let meetE x y : meet m x y = RelOrder.meet le_order x y := meet_def m x y.
Let joinE x y : join m x y = RelOrder.join le_order x y := join_def m x y.

Fact meetC : commutative (meet m).
Proof. by move=> *; rewrite !meetE meetC. Qed.

Fact joinC : commutative (join m).
Proof. by move=> *; rewrite !joinE joinC. Qed.

Fact meetA : associative (meet m).
Proof. by move=> *; rewrite !meetE meetA. Qed.

Fact joinA : associative (join m).
Proof. by move=> *; rewrite !joinE joinA. Qed.

Fact joinKI y x : meet m x (join m x y) = x.
Proof. by rewrite meetE joinE joinKI. Qed.

Fact meetKU y x : join m x (meet m x y) = x.
Proof. by rewrite meetE joinE meetKU. Qed.

Fact meetxx : idempotent (meet m).
Proof. by move=> *; rewrite meetE meetxx. Qed.

Fact le_def x y : le m x y = (meet m x y == x).
Proof. by rewrite meetE eq_meetl. Qed.

Definition latticeMixin : meetJoinMixin T :=
  MeetJoinMixin
    le_def (lt_def m) meetC joinC meetA joinA joinKI meetKU meetxx.

Definition totalMixin : totalLatticeRelMixin (LatticeOfPOrder latticeMixin) :=
  le_total m.

End LeOrderMixin.

Module Exports.
Notation leOrderMixin := of_.
Notation LeOrderMixin := Build.
Coercion latticeMixin : of_ >-> meetJoinMixin.
Coercion totalMixin : of_ >-> totalLatticeRelMixin.
End Exports.

End LeOrderMixin.
Import LeOrderMixin.Exports.

Module LtOrderMixin.
Section LtOrderMixin.
Variables (T : eqType).

Record of_ := Build {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  join : T -> T -> T;
  le_def   : forall x y, le x y = (x == y) || lt x y;
  meet_def : forall x y, meet x y = if lt x y then x else y;
  join_def : forall x y, join x y = if lt x y then y else x;
  lt_irr   : irreflexive lt;
  lt_trans : transitive lt;
  lt_total : forall x y, x != y -> lt x y || lt y x;
}.

Variables (m : of_).

Fact lt_def x y : lt m x y = (y != x) && le m x y.
Proof. by rewrite le_def //; case: eqVneq => //= ->; rewrite lt_irr. Qed.

Fact meet_def_le x y : meet m x y = if lt m x y then x else y.
Proof. by rewrite meet_def // lt_def; case: eqP. Qed.

Fact join_def_le x y : join m x y = if lt m x y then y else x.
Proof. by rewrite join_def // lt_def; case: eqP. Qed.

Fact le_anti : antisymmetric (le m).
Proof.
move=> x y; rewrite !le_def //.
by case: eqVneq => //= _ /andP [] hxy /(lt_trans hxy); rewrite lt_irr.
Qed.

Fact le_trans : transitive (le m).
Proof.
move=> y x z; rewrite !le_def //; case: eqVneq => [->|_] //=.
by case: eqVneq => [-> ->|_ hxy /(lt_trans hxy) ->]; rewrite orbT.
Qed.

Fact le_total : total (le m).
Proof.
by move=> x y; rewrite !le_def //; case: eqVneq => //=; exact: lt_total.
Qed.

Definition orderMixin : leOrderMixin T :=
  LeOrderMixin lt_def meet_def_le join_def_le le_anti le_trans le_total.

End LtOrderMixin.

Module Exports.
Notation ltOrderMixin := of_.
Notation LtOrderMixin := Build.
Coercion orderMixin : of_ >-> leOrderMixin.
End Exports.

End LtOrderMixin.
Import LtOrderMixin.Exports.

(*************)
(* INSTANCES *)
(*************)

Module NatOrder.

Lemma ltn_def x y : (x < y)%N = (y != x)%N && (x <= y)%N.
Proof. by case: ltngtP. Qed.

Definition nat_pOrderMixin := LePOrderMixin ltn_def leqnn anti_leq leq_trans.

Local Canonical nat_pOrder := POrder leq ltn nat_pOrderMixin.
(* BUG, TODO: the packager [BPOrder] can infer the [pOrder] instance only     *)
(* from the symbol [leq]. If [leq] is replaced with [nosimpl leq] above, the  *)
(* following declaration fails.                                               *)
Local Canonical nat_bPOrder := BPOrder leq ltn 0 leq0n.

Definition nat_totalMixin : totalPOrderRelMixin nat_pOrder := leq_total.

Local Canonical nat_meetOrder := MeetOrder leq ltn minn nat_totalMixin.
Local Canonical nat_bMeetOrder := [bMeetOrder of leq].
Local Canonical nat_joinOrder := JoinOrder leq ltn maxn nat_totalMixin.
Local Canonical nat_bJoinOrder := [bJoinOrder of leq].
Local Canonical nat_lattice := [lattice of leq].
Local Canonical nat_bLattice := [bLattice of leq].
Local Canonical nat_distrLattice :=
  DistrLattice leq ltn minn maxn nat_totalMixin.
Local Canonical nat_bDistrLattice := [bDistrLattice of leq].
Local Canonical nat_totalOrder := TotalOrder leq ltn minn maxn nat_totalMixin.
Local Canonical nat_bTotalOrder := [bTotalOrder of leq].

End NatOrder.

(* ================================================================== *)

Module Theory.
Export RelOrder.POrderTheory.
Export RelOrder.BPOrderTheory.
Export RelOrder.TPOrderTheory.
Export RelOrder.MeetTheory.
Export RelOrder.BMeetTheory.
Export RelOrder.TMeetTheory.
Export RelOrder.JoinTheory.
Export RelOrder.BJoinTheory.
Export RelOrder.TJoinTheory.
Export RelOrder.LatticeTheory.
Export RelOrder.DistrLatticeTheory.
Export RelOrder.BDistrLatticeTheory.
Export RelOrder.TDistrLatticeTheory.
Export RelOrder.TotalTheory.
End Theory.

End RelOrder.

(* ==================================================================== *)

Export RelOrder.Syntax.
Export RelOrder.POrder.Exports RelOrder.BPOrder.Exports.
Export RelOrder.TPOrder.Exports RelOrder.TBPOrder.Exports.
Export RelOrder.Meet.Exports RelOrder.BMeet.Exports.
Export RelOrder.TMeet.Exports RelOrder.TBMeet.Exports.
Export RelOrder.Join.Exports RelOrder.BJoin.Exports.
Export RelOrder.TJoin.Exports RelOrder.TBJoin.Exports.
Export RelOrder.Lattice.Exports RelOrder.BLattice.Exports.
Export RelOrder.TLattice.Exports RelOrder.TBLattice.Exports.
Export RelOrder.DistrLattice.Exports RelOrder.BDistrLattice.Exports.
Export RelOrder.TDistrLattice.Exports RelOrder.TBDistrLattice.Exports.
Export RelOrder.Total.Exports RelOrder.BTotal.Exports.
Export RelOrder.TTotal.Exports RelOrder.TBTotal.Exports.
Export RelOrder.LePOrderMixin.Exports.
Export RelOrder.BottomRelMixin.Exports.
Export RelOrder.TopRelMixin.Exports.
Export RelOrder.MeetRelMixin.Exports.
Export RelOrder.JoinRelMixin.Exports.
Export RelOrder.DistrLatticeRelMixin.Exports.
Export RelOrder.LatticePOrderRelMixin.Exports.
Export RelOrder.DistrLatticePOrderRelMixin.Exports.
Export RelOrder.TotalLatticeRelMixin.Exports.
Export RelOrder.TotalPOrderRelMixin.Exports.
Export RelOrder.TotalMeetOrderRelMixin.Exports.
Export RelOrder.TotalJoinOrderRelMixin.Exports.
Export RelOrder.LtPOrderMixin.Exports.
Export RelOrder.MeetJoinMixin.Exports.
Export RelOrder.DistrMeetJoinMixin.Exports.
Export RelOrder.LeOrderMixin.Exports.
Export RelOrder.LtOrderMixin.Exports.
