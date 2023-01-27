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

Definition rdual_rel (T : Type) (r : rel T) := fun y x => r x y.
Definition rdual_bottom (T : Type) (top : T) := top.
Definition rdual_top (T : Type) (bottom : T) := bottom.
Definition rdual_meet (T : Type) (join : T -> T -> T) := join.
Definition rdual_join (T : Type) (meet : T -> T -> T) := meet.

Module RelOrder.

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
  rlt_def : forall x y, lt x y = (y != x) && le x y;
  dlt_def : forall x y, lt y x = (y != x) && le y x;
  rlexx : reflexive le;
  rle_anti : forall x y, le x y -> le y x -> x = y;
  rle_trans : transitive le;
}.

Notation class_of := mixin_of (only parsing).

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  class : class_of le lt;
}.

Unset Primitive Projections.

Variable (phT : phant T) (ord : order phT) (leT ltT : rel T).

Let cls := unkeyed (class ord).

Definition clone c of phant_id cls c := @Pack phT leT ltT (unkeyed c).

End ClassDef.

Notation class_of := mixin_of (only parsing).

Module Exports.
Notation "{ 'pOrder' T }" := (order (Phant T))
  (at level 0, format "{ 'pOrder'  T }").
Notation POrder le lt mixin := (@Pack _ (Phant _) le lt (unkeyed mixin)).
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
    (rdual_rel (le ord)) (rdual_rel (lt ord))
    (let mixin := POrder.class ord in
     @POrder.Mixin
       T (rdual_rel (le ord)) (rdual_rel (lt ord))
       (POrder.dlt_def mixin) (POrder.rlt_def mixin) (POrder.rlexx mixin)
       (fun x y yx xy => POrder.rle_anti mixin xy yx)
       (fun y x z xy yz => POrder.rle_trans mixin yz xy)).

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
  class : class_of le lt bottom;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> POrder.class_of.

Variable (phT : phant T) (ord : order phT).

Let cls := unkeyed (class ord).

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) cls.

Variable (leT ltT : rel T) (bottomT : T).

Definition clone c of phant_id cls c := @Pack phT leT ltT bottomT (unkeyed c).

Definition pack (b0 : POrder.class_of leT ltT)
                (m0 : mixin_of (POrder.Pack _ b0) bottomT) :=
  fun (b : POrder.class_of leT ltT)            & phant_id b0 b =>
  fun (m : mixin_of (POrder.Pack _ b) bottomT) & phant_id m0 m =>
  @Pack phT leT ltT bottomT (unkeyed (Class m)).

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
  (@clone _ (Phant _) _ le (unkeyed _) (unkeyed _) _ id)
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
  class : class_of le lt top;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> POrder.class_of.

Variable (phT : phant T) (ord : order phT).

Let cls := unkeyed (class ord).

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) cls.

Variable (leT ltT : rel T) (topT : T).

Definition clone c of phant_id cls c := @Pack phT leT ltT topT (unkeyed c).

Definition pack (b0 : POrder.class_of leT ltT)
                (m0 : mixin_of (POrder.Pack _ b0) topT) :=
  fun (b : POrder.class_of leT ltT)         & phant_id b0 b =>
  fun (m : mixin_of (POrder.Pack _ b) topT) & phant_id m0 m =>
  @Pack phT leT ltT topT (unkeyed (Class m)).

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
  (@clone _ (Phant _) _ le (unkeyed _) (unkeyed _) _ id)
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
  class : class_of le lt bottom top;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> BPOrder.class_of.
Local Coercion base2 le lt bottom top (c : class_of le lt bottom top) :
  TPOrder.class_of le lt top := TPOrder.Class (mixin c).

Variable (phT : phant T) (ord : order phT).

Let cls := unkeyed (class ord).

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) cls.
Definition bPOrder := @BPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) cls.
Definition tPOrder := @TPOrder.Pack _ phT (le ord) (lt ord) (top ord) cls.
(* NB: [unkeyed] is needed to let the [Canonical] command ignore a field.     *)
Definition bP_tPOrder :=
  @TPOrder.Pack _ phT (BPOrder.le bPOrder) (BPOrder.lt bPOrder)
                ((* hack! *) unkeyed (top ord)) cls.

Variable (leT ltT : rel T) (bottomT topT : T).

Definition pack :=
  fun (bord : BPOrder.order phT) (b : BPOrder.class_of leT ltT bottomT)
      & phant_id (BPOrder.class bord) b =>
  fun (mord : TPOrder.order phT) m
      & phant_id (TPOrder.class mord) (TPOrder.Class (base := b) m) =>
  @Pack phT leT ltT bottomT topT (unkeyed (Class (base := b) m)).

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
  (@pack _ (Phant _) le (unkeyed _) (unkeyed _) (unkeyed _) _ _ id _ _ id)
  (at level 0, format "[ 'tbPOrder'  'of'  le ]").
End Exports.

End TBPOrder.
Import TBPOrder.Exports.

Module Meet.

Section ClassDef.

Variable T : eqType.

Set Primitive Projections.

Record mixin_of (ord : {pOrder T}) (meet : T -> T -> T) := Mixin {
  rmeetC : commutative meet;
  rmeetA : associative meet;
  rleEmeet : forall x y, (le ord x y) = (meet x y == x);
}.

Record class_of (le lt : rel T) (meet : T -> T -> T) := Class {
  base : POrder.class_of le lt;
  mixin : mixin_of (POrder.Pack _ base) meet;
}.

Structure order (phT : phant T) := Pack {
  le : rel T;
  lt : rel T;
  meet : T -> T -> T;
  class : class_of le lt meet;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> POrder.class_of.

Variable (phT : phant T) (ord : order phT).

Let cls := unkeyed (class ord).

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) cls.

Variable (leT ltT : rel T) (meetT : T -> T -> T).

Definition clone c of phant_id cls c := @Pack phT leT ltT meetT (unkeyed c).

Definition pack (b0 : POrder.class_of leT ltT)
                (m0 : mixin_of (POrder.Pack _ b0) meetT) :=
  fun (b : POrder.class_of leT ltT)          & phant_id b0 b =>
  fun (m : mixin_of (POrder.Pack _ b) meetT) & phant_id m0 m =>
  @Pack phT leT ltT meetT (unkeyed (Class m)).

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
  (@clone _ (Phant _) _ le (unkeyed _) (unkeyed _) _ id)
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
  class : class_of le lt meet bottom;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> Meet.class_of.
Local Coercion base2 le lt meet bottom (c : class_of le lt meet bottom) :
  BPOrder.class_of le lt bottom := BPOrder.Class (mixin c).

Variable (phT : phant T) (ord : order phT).

Let cls := unkeyed (class ord).

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) cls.
Definition bPOrder := @BPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) cls.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) cls.
Definition bP_meetOrder :=
  @Meet.Pack
    _ phT (BPOrder.le bPOrder) (BPOrder.lt bPOrder) (unkeyed (meet ord)) cls.

Variable (leT ltT : rel T) (meetT : T -> T -> T) (bottomT : T).

Definition pack :=
  fun (bord : Meet.order phT) (b : Meet.class_of leT ltT meetT)
      & phant_id (Meet.class bord) b =>
  fun (mord : BPOrder.order phT) m
      & phant_id (BPOrder.class mord) (BPOrder.Class (base := b) m) =>
  @Pack phT leT ltT meetT bottomT (unkeyed (Class (base := b) m)).

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
  (@pack _ (Phant _) le (unkeyed _) (unkeyed _) (unkeyed _) _ _ id _ _ id)
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
  class : class_of le lt meet top;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> Meet.class_of.
Local Coercion base2 le lt meet top (c : class_of le lt meet top) :
  TPOrder.class_of le lt top := TPOrder.Class (mixin c).

Variable (phT : phant T) (ord : order phT).

Let cls := unkeyed (class ord).

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) cls.
Definition tPOrder := @TPOrder.Pack _ phT (le ord) (lt ord) (top ord) cls.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) cls.
Definition tP_meetOrder :=
  @Meet.Pack
    _ phT (TPOrder.le tPOrder) (TPOrder.lt tPOrder) (unkeyed (meet ord)) cls.

Variable (leT ltT : rel T) (meetT : T -> T -> T) (topT : T).

Definition pack :=
  fun (bord : Meet.order phT) (b : Meet.class_of leT ltT meetT)
      & phant_id (Meet.class bord) b =>
  fun (mord : TPOrder.order phT) m
      & phant_id (TPOrder.class mord) (TPOrder.Class (base := b) m) =>
  @Pack phT leT ltT meetT topT (unkeyed (Class (base := b) m)).

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
  (@pack _ (Phant _) le (unkeyed _) (unkeyed _) (unkeyed _) _ _ id _ _ id)
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
  class : class_of le lt meet bottom top;
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

Let cls := unkeyed (class ord).

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) cls.
Definition bPOrder := @BPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) cls.
Definition tPOrder := @TPOrder.Pack _ phT (le ord) (lt ord) (top ord) cls.
Definition tbPOrder :=
  @TBPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) (top ord) cls.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) cls.
Definition bMeetOrder :=
  @BMeet.Pack _ phT (le ord) (lt ord) (meet ord) (bottom ord) cls.
Definition tMeetOrder :=
  @TMeet.Pack _ phT (le ord) (lt ord) (meet ord) (top ord) cls.
Definition bP_tMeetOrder :=
  @TMeet.Pack _ phT (BPOrder.le bPOrder) (BPOrder.lt bPOrder)
              (unkeyed (meet ord)) (unkeyed (top ord)) cls.
Definition tP_bMeetOrder :=
  @BMeet.Pack _ phT (TPOrder.le tPOrder) (TPOrder.lt tPOrder)
              (unkeyed (meet ord)) (unkeyed (bottom ord)) cls.
Definition tbP_meetOrder :=
  @Meet.Pack _ phT (TBPOrder.le tbPOrder) (TBPOrder.lt tbPOrder)
             (unkeyed (meet ord)) cls.
Definition tbP_bMeetOrder :=
  @BMeet.Pack _ phT (TBPOrder.le tbPOrder) (TBPOrder.lt tbPOrder)
              (unkeyed (meet ord)) (TBPOrder.bottom tbPOrder) cls.
Definition tbP_tMeetOrder :=
  @TMeet.Pack _ phT (TBPOrder.le tbPOrder) (TBPOrder.lt tbPOrder)
              (unkeyed (meet ord)) (TBPOrder.top tbPOrder) cls.
Definition bMeet_tMeetOrder :=
  @TMeet.Pack _ phT (BMeet.le bMeetOrder) (BMeet.lt bMeetOrder)
              (BMeet.meet bMeetOrder) (unkeyed (top ord)) cls.

Variable (leT ltT : rel T) (meetT : T -> T -> T) (bottomT topT : T).

Definition pack :=
  fun (bord : BMeet.order phT) (b : BMeet.class_of leT ltT meetT bottomT)
      & phant_id (BMeet.class bord) b =>
  fun (mord : TPOrder.order phT) m
      & phant_id (TPOrder.class mord) (TPOrder.Class (base := b) m) =>
  @Pack phT leT ltT meetT bottomT topT (unkeyed (Class (base := b) m)).

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
  (@pack _ (Phant _) le (unkeyed _) (unkeyed _) (unkeyed _) (unkeyed _)
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
  class : class_of le lt join;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> POrder.class_of.

Variable (phT : phant T) (ord : order phT).

Let cls := unkeyed (class ord).

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) cls.

Variable (leT ltT : rel T) (joinT : T -> T -> T).

Definition clone c of phant_id cls c := @Pack phT leT ltT joinT (unkeyed c).

Definition pack (b0 : POrder.class_of leT ltT)
                (m0 : mixin_of (POrder.Pack _ b0) joinT) :=
  fun (b : POrder.class_of leT ltT)          & phant_id b0 b =>
  fun (m : mixin_of (POrder.Pack _ b) joinT) & phant_id m0 m =>
  @Pack phT leT ltT joinT (unkeyed (Class m)).

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
  (@clone _ (Phant _) _ le (unkeyed _) (unkeyed _) _ id)
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
  class : class_of le lt join bottom;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> Join.class_of.
Local Coercion base2 le lt join bottom (c : class_of le lt join bottom) :
  BPOrder.class_of le lt bottom := BPOrder.Class (mixin c).

Variable (phT : phant T) (ord : order phT).

Let cls := unkeyed (class ord).

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) cls.
Definition bPOrder := @BPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) cls.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) cls.
Definition bP_joinOrder :=
  @Join.Pack
    _ phT (BPOrder.le bPOrder) (BPOrder.lt bPOrder) (unkeyed (join ord)) cls.

Variable (leT ltT : rel T) (joinT : T -> T -> T) (bottomT : T).

Definition pack :=
  fun (bord : Join.order phT) (b : Join.class_of leT ltT joinT)
      & phant_id (Join.class bord) b =>
  fun (mord : BPOrder.order phT) m
      & phant_id (BPOrder.class mord) (BPOrder.Class (base := b) m) =>
  @Pack phT leT ltT joinT bottomT (unkeyed (Class (base := b) m)).

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
  (@pack _ (Phant _) le (unkeyed _) (unkeyed _) (unkeyed _) _ _ id _ _ id)
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
  class : class_of le lt join top;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> Join.class_of.
Local Coercion base2 le lt join top (c : class_of le lt join top) :
  TPOrder.class_of le lt top := TPOrder.Class (mixin c).

Variable (phT : phant T) (ord : order phT).

Let cls := unkeyed (class ord).

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) cls.
Definition tPOrder := @TPOrder.Pack _ phT (le ord) (lt ord) (top ord) cls.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) cls.
Definition tP_joinOrder :=
  @Join.Pack
    _ phT (TPOrder.le tPOrder) (TPOrder.lt tPOrder) (unkeyed (join ord)) cls.

Variable (leT ltT : rel T) (joinT : T -> T -> T) (topT : T).

Definition pack :=
  fun (bord : Join.order phT) (b : Join.class_of leT ltT joinT)
      & phant_id (Join.class bord) b =>
  fun (mord : TPOrder.order phT) m
      & phant_id (TPOrder.class mord) (TPOrder.Class (base := b) m) =>
  @Pack phT leT ltT joinT topT (unkeyed (Class (base := b) m)).

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
  (@pack _ (Phant _) le (unkeyed _) (unkeyed _) (unkeyed _) _ _ id _ _ id)
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
  class : class_of le lt join bottom top;
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

Let cls := unkeyed (class ord).

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) cls.
Definition bPOrder := @BPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) cls.
Definition tPOrder := @TPOrder.Pack _ phT (le ord) (lt ord) (top ord) cls.
Definition tbPOrder :=
  @TBPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) (top ord) cls.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) cls.
Definition bJoinOrder :=
  @BJoin.Pack _ phT (le ord) (lt ord) (join ord) (bottom ord) cls.
Definition tJoinOrder :=
  @TJoin.Pack _ phT (le ord) (lt ord) (join ord) (top ord) cls.
Definition bP_tJoinOrder :=
  @TJoin.Pack _ phT (BPOrder.le bPOrder) (BPOrder.lt bPOrder)
              (unkeyed (join ord)) (unkeyed (top ord)) cls.
Definition tP_bJoinOrder :=
  @BJoin.Pack _ phT (TPOrder.le tPOrder) (TPOrder.lt tPOrder)
              (unkeyed (join ord)) (unkeyed (bottom ord)) cls.
Definition tbP_joinOrder :=
  @Join.Pack _ phT (TBPOrder.le tbPOrder) (TBPOrder.lt tbPOrder)
             (unkeyed (join ord)) cls.
Definition tbP_bJoinOrder :=
  @BJoin.Pack _ phT (TBPOrder.le tbPOrder) (TBPOrder.lt tbPOrder)
              (unkeyed (join ord)) (TBPOrder.bottom tbPOrder) cls.
Definition tbP_tJoinOrder :=
  @TJoin.Pack _ phT (TBPOrder.le tbPOrder) (TBPOrder.lt tbPOrder)
              (unkeyed (join ord)) (TBPOrder.top tbPOrder) cls.
Definition bJoin_tJoinOrder :=
  @TJoin.Pack _ phT (BJoin.le bJoinOrder) (BJoin.lt bJoinOrder)
              (BJoin.join bJoinOrder) (unkeyed (top ord)) cls.

Variable (leT ltT : rel T) (joinT : T -> T -> T) (bottomT topT : T).

Definition pack :=
  fun (bord : BJoin.order phT) (b : BJoin.class_of leT ltT joinT bottomT)
      & phant_id (BJoin.class bord) b =>
  fun (mord : TPOrder.order phT) m
      & phant_id (TPOrder.class mord) (TPOrder.Class (base := b) m) =>
  @Pack phT leT ltT joinT bottomT topT (unkeyed (Class (base := b) m)).

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
  (@pack _ (Phant _) le (unkeyed _) (unkeyed _) (unkeyed _) (unkeyed _)
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
  class : class_of le lt meet join;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> Meet.class_of.
Local Coercion base2 le lt meet join (c : class_of le lt meet join) :
  Join.class_of le lt join := Join.Class (mixin c).

Variable (phT : phant T) (ord : order phT).

Let cls := unkeyed (class ord).

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) cls.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) cls.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) cls.
Definition meet_joinOrder :=
  @Join.Pack
    _ phT (Meet.le meetOrder) (Meet.lt meetOrder) (unkeyed (join ord)) cls.

Variable (leT ltT : rel T) (meetT joinT : T -> T -> T).

Definition pack :=
  fun (bord : Meet.order phT) (b : Meet.class_of leT ltT meetT)
      & phant_id (Meet.class bord) b =>
  fun (mord : Join.order phT) m
      & phant_id (Join.class mord) (Join.Class (base := b) m) =>
  @Pack phT leT ltT meetT joinT (unkeyed (Class (base := b) m)).

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
  (@pack _ (Phant _) le (unkeyed _) (unkeyed _) (unkeyed _) _ _ id _ _ id)
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
  class : class_of le lt meet join bottom;
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

Let cls := unkeyed (class ord).

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) cls.
Definition bPOrder := @BPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) cls.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) cls.
Definition bMeetOrder :=
  @BMeet.Pack _ phT (le ord) (lt ord) (meet ord) (bottom ord) cls.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) cls.
Definition bJoinOrder :=
  @BJoin.Pack _ phT (le ord) (lt ord) (join ord) (bottom ord) cls.
Definition lattice :=
  @Lattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) cls.
Definition meet_bJoinOrder :=
  @BJoin.Pack _ phT (Meet.le meetOrder) (Meet.lt meetOrder)
              (unkeyed (join ord)) (unkeyed (bottom ord)) cls.
Definition join_bMeetOrder :=
  @BMeet.Pack _ phT (Join.le joinOrder) (Join.lt joinOrder)
              (unkeyed (meet ord)) (unkeyed (bottom ord)) cls.
Definition bMeet_bJoinOrder :=
  @BJoin.Pack _ phT (BMeet.le bMeetOrder) (BMeet.lt bMeetOrder)
              (unkeyed (join ord)) (BMeet.bottom bMeetOrder) cls.
Definition lattice_bPOrder :=
  @BPOrder.Pack _ phT (Lattice.le lattice) (Lattice.lt lattice)
                (unkeyed (bottom ord)) cls.
Definition lattice_bMeetOrder :=
  @BMeet.Pack _ phT (Lattice.le lattice) (Lattice.lt lattice)
              (Lattice.meet lattice) (unkeyed (bottom ord)) cls.
Definition lattice_bJoinOrder :=
  @BJoin.Pack _ phT (Lattice.le lattice) (Lattice.lt lattice)
              (Lattice.join lattice) (unkeyed (bottom ord)) cls.

Variable (leT ltT : rel T) (meetT joinT : T -> T -> T) (bottomT : T).

Definition pack :=
  fun (bord : Lattice.order phT) (b : Lattice.class_of leT ltT meetT joinT)
      & phant_id (Lattice.class bord) b =>
  fun (mord : BPOrder.order phT) m
      & phant_id (BPOrder.class mord) (BPOrder.Class (base := b) m) =>
  @Pack phT leT ltT meetT joinT bottomT (unkeyed (Class (base := b) m)).

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
  (@pack _ (Phant _) le (unkeyed _) (unkeyed _) (unkeyed _) (unkeyed _)
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
  class : class_of le lt meet join top;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> Lattice.class_of.
Local Coercion base2 le lt meet join top (c : class_of le lt meet join top) :
  TMeet.class_of le lt meet top := TMeet.Class (mixin c).
Local Coercion base3 le lt meet join top (c : class_of le lt meet join top) :
  TJoin.class_of le lt join top := TJoin.Class (base := c) (mixin c).

Variable (phT : phant T) (ord : order phT).

Let cls := unkeyed (class ord).

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) cls.
Definition tPOrder := @TPOrder.Pack _ phT (le ord) (lt ord) (top ord) cls.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) cls.
Definition tMeetOrder :=
  @TMeet.Pack _ phT (le ord) (lt ord) (meet ord) (top ord) cls.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) cls.
Definition tJoinOrder :=
  @TJoin.Pack _ phT (le ord) (lt ord) (join ord) (top ord) cls.
Definition lattice :=
  @Lattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) cls.
Definition meet_tJoinOrder :=
  @TJoin.Pack _ phT (Meet.le meetOrder) (Meet.lt meetOrder)
              (unkeyed (join ord)) (unkeyed (top ord)) cls.
Definition join_tMeetOrder :=
  @TMeet.Pack _ phT (Join.le joinOrder) (Join.lt joinOrder)
              (unkeyed (meet ord)) (unkeyed (top ord)) cls.
Definition tMeet_tJoinOrder :=
  @TJoin.Pack _ phT (TMeet.le tMeetOrder) (TMeet.lt tMeetOrder)
              (unkeyed (join ord)) (TMeet.top tMeetOrder) cls.
Definition lattice_tPOrder :=
  @TPOrder.Pack _ phT (Lattice.le lattice) (Lattice.lt lattice)
                (unkeyed (top ord)) cls.
Definition lattice_tMeetOrder :=
  @TMeet.Pack _ phT (Lattice.le lattice) (Lattice.lt lattice)
              (Lattice.meet lattice) (unkeyed (top ord)) cls.
Definition lattice_tJoinOrder :=
  @TJoin.Pack _ phT (Lattice.le lattice) (Lattice.lt lattice)
              (Lattice.join lattice) (unkeyed (top ord)) cls.

Variable (leT ltT : rel T) (meetT joinT : T -> T -> T) (topT : T).

Definition pack :=
  fun (bord : Lattice.order phT) (b : Lattice.class_of leT ltT meetT joinT)
      & phant_id (Lattice.class bord) b =>
  fun (mord : TPOrder.order phT) m
      & phant_id (TPOrder.class mord) (TPOrder.Class (base := b) m) =>
  @Pack phT leT ltT meetT joinT topT (unkeyed (Class (base := b) m)).

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
  (@pack _ (Phant _) le (unkeyed _) (unkeyed _) (unkeyed _) (unkeyed _)
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
  class : class_of le lt meet join bottom top;
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

Let cls := unkeyed (class ord).

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) cls.
Definition bPOrder := @BPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) cls.
Definition tPOrder := @TPOrder.Pack _ phT (le ord) (lt ord) (top ord) cls.
Definition tbPOrder :=
  @TBPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) (top ord) cls.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) cls.
Definition bMeetOrder :=
  @BMeet.Pack _ phT (le ord) (lt ord) (meet ord) (bottom ord) cls.
Definition tMeetOrder :=
  @TMeet.Pack _ phT (le ord) (lt ord) (meet ord) (top ord) cls.
Definition tbMeetOrder :=
  @TBMeet.Pack _ phT (le ord) (lt ord) (meet ord) (bottom ord) (top ord) cls.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) cls.
Definition bJoinOrder :=
  @BJoin.Pack _ phT (le ord) (lt ord) (join ord) (bottom ord) cls.
Definition tJoinOrder :=
  @TJoin.Pack _ phT (le ord) (lt ord) (join ord) (top ord) cls.
Definition tbJoinOrder :=
  @TBJoin.Pack _ phT (le ord) (lt ord) (join ord) (bottom ord) (top ord) cls.
Definition lattice :=
  @Lattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) cls.
Definition bLattice :=
  @BLattice.Pack
    _ phT (le ord) (lt ord) (meet ord) (join ord) (bottom ord) cls.
Definition tLattice :=
  @TLattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) (top ord) cls.
(* TODO: non-trivial joins are missing below. *)

Variable (leT ltT : rel T) (meetT joinT : T -> T -> T) (bottomT topT : T).

Definition pack :=
  fun (bord : BLattice.order phT)
      (b : BLattice.class_of leT ltT meetT joinT bottomT)
      & phant_id (BLattice.class bord) b =>
  fun (mord : TPOrder.order phT) m
      & phant_id (TPOrder.class mord) (TPOrder.Class (base := b) m) =>
  @Pack phT leT ltT meetT joinT bottomT topT (unkeyed (Class (base := b) m)).

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
  (@pack _ (Phant _) le (unkeyed _) (unkeyed _) (unkeyed _) (unkeyed _)
         (unkeyed _) _ _ id _ _ id)
  (at level 0, format "[ 'tbLattice'  'of'  le ]").
End Exports.

End TBLattice.
Import TBLattice.Exports.

Module DistrLattice.

Section ClassDef.

Variable T : eqType.

Set Primitive Projections.

Record mixin_of (ord : {lattice T}) := Mixin {
  rmeetUl : left_distributive (meet ord) (join ord);
  rjoinIl : left_distributive (join ord) (meet ord);
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
  class : class_of le lt meet join;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> Lattice.class_of.

Variable (phT : phant T) (ord : order phT).

Let cls := unkeyed (class ord).

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) cls.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) cls.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) cls.
Definition lattice :=
  @Lattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) cls.

Variable (leT ltT : rel T) (meetT joinT : T -> T -> T).

Definition clone c of phant_id cls c :=
  @Pack phT leT ltT meetT joinT (unkeyed c).

Definition pack (b0 : Lattice.class_of leT ltT meetT joinT)
                (m0 : mixin_of (Lattice.Pack _ b0)) :=
  fun (b : Lattice.class_of leT ltT meetT joinT) & phant_id b0 b =>
  fun (m : mixin_of (Lattice.Pack _ b))          & phant_id m0 m =>
  @Pack phT leT ltT meetT joinT (unkeyed (Class m)).

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
  (@clone _ (Phant _) _ le (unkeyed _) (unkeyed _) (unkeyed _) _ id)
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
  class : class_of le lt meet join bottom;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> DistrLattice.class_of.
Local Coercion base2 le lt meet join bottom
                     (c : class_of le lt meet join bottom) :
  BLattice.class_of le lt meet join bottom := BLattice.Class (mixin c).

Variable (phT : phant T) (ord : order phT).

Let cls := unkeyed (class ord).

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) cls.
Definition bPOrder := @BPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) cls.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) cls.
Definition bMeetOrder :=
  @BMeet.Pack _ phT (le ord) (lt ord) (meet ord) (bottom ord) cls.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) cls.
Definition bJoinOrder :=
  @BJoin.Pack _ phT (le ord) (lt ord) (join ord) (bottom ord) cls.
Definition lattice :=
  @Lattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) cls.
Definition bLattice :=
  @BLattice.Pack
    _ phT (le ord) (lt ord) (meet ord) (join ord) (bottom ord) cls.
Definition distrLattice :=
  @DistrLattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) cls.

Variable (leT ltT : rel T) (meetT joinT : T -> T -> T) (bottomT : T).

Definition pack :=
  fun (bord : DistrLattice.order phT)
      (b : DistrLattice.class_of leT ltT meetT joinT)
      & phant_id (DistrLattice.class bord) b =>
  fun (mord : BPOrder.order phT) m
      & phant_id (BPOrder.class mord) (BPOrder.Class (base := b) m) =>
  @Pack phT leT ltT meetT joinT bottomT (unkeyed (Class (base := b) m)).

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
  (@pack _ (Phant _) le (unkeyed _) (unkeyed _) (unkeyed _) (unkeyed _)
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
  class : class_of le lt meet join top;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> DistrLattice.class_of.
Local Coercion base2 le lt meet join top (c : class_of le lt meet join top) :
  TLattice.class_of le lt meet join top := TLattice.Class (mixin c).

Variable (phT : phant T) (ord : order phT).

Let cls := unkeyed (class ord).

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) cls.
Definition tPOrder := @TPOrder.Pack _ phT (le ord) (lt ord) (top ord) cls.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) cls.
Definition tMeetOrder :=
  @TMeet.Pack _ phT (le ord) (lt ord) (meet ord) (top ord) cls.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) cls.
Definition tJoinOrder :=
  @TJoin.Pack _ phT (le ord) (lt ord) (join ord) (top ord) cls.
Definition lattice :=
  @Lattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) cls.
Definition tLattice :=
  @TLattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) (top ord) cls.
Definition distrLattice :=
  @DistrLattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) cls.

Variable (leT ltT : rel T) (meetT joinT : T -> T -> T) (topT : T).

Definition pack :=
  fun (bord : DistrLattice.order phT)
      (b : DistrLattice.class_of leT ltT meetT joinT)
      & phant_id (DistrLattice.class bord) b =>
  fun (mord : TPOrder.order phT) m
      & phant_id (TPOrder.class mord) (TPOrder.Class (base := b) m) =>
  @Pack phT leT ltT meetT joinT topT (unkeyed (Class (base := b) m)).

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
  (@pack _ (Phant _) le (unkeyed _) (unkeyed _) (unkeyed _) (unkeyed _)
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
  class : class_of le lt meet join bottom top;
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

Let cls := unkeyed (class ord).

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) cls.
Definition bPOrder := @BPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) cls.
Definition tPOrder := @TPOrder.Pack _ phT (le ord) (lt ord) (top ord) cls.
Definition tbPOrder :=
  @TBPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) (top ord) cls.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) cls.
Definition bMeetOrder :=
  @BMeet.Pack _ phT (le ord) (lt ord) (meet ord) (bottom ord) cls.
Definition tMeetOrder :=
  @TMeet.Pack _ phT (le ord) (lt ord) (meet ord) (top ord) cls.
Definition tbMeetOrder :=
  @TBMeet.Pack _ phT (le ord) (lt ord) (meet ord) (bottom ord) (top ord) cls.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) cls.
Definition bJoinOrder :=
  @BJoin.Pack _ phT (le ord) (lt ord) (join ord) (bottom ord) cls.
Definition tJoinOrder :=
  @TJoin.Pack _ phT (le ord) (lt ord) (join ord) (top ord) cls.
Definition tbJoinOrder :=
  @TBJoin.Pack _ phT (le ord) (lt ord) (join ord) (bottom ord) (top ord) cls.
Definition lattice :=
  @Lattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) cls.
Definition bLattice :=
  @BLattice.Pack
    _ phT (le ord) (lt ord) (meet ord) (join ord) (bottom ord) cls.
Definition tLattice :=
  @TLattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) (top ord) cls.
Definition tbLattice :=
  @TBLattice.Pack
    _ phT (le ord) (lt ord) (meet ord) (join ord) (bottom ord) (top ord) cls.
Definition distrLattice :=
  @DistrLattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) cls.
Definition bDistrLattice :=
  @BDistrLattice.Pack
    _ phT (le ord) (lt ord) (meet ord) (join ord) (bottom ord) cls.
Definition tDistrLattice :=
  @TDistrLattice.Pack
    _ phT (le ord) (lt ord) (meet ord) (join ord) (top ord) cls.

Variable (leT ltT : rel T) (meetT joinT : T -> T -> T) (bottomT topT : T).

Definition pack :=
  fun (bord : BDistrLattice.order phT)
      (b : BDistrLattice.class_of leT ltT meetT joinT bottomT)
      & phant_id (BDistrLattice.class bord) b =>
  fun (mord : TPOrder.order phT) m
      & phant_id (TPOrder.class mord) (TPOrder.Class (base := b) m) =>
  @Pack phT leT ltT meetT joinT bottomT topT (unkeyed (Class (base := b) m)).

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
  (@pack _ (Phant _) le (unkeyed _) (unkeyed _) (unkeyed _) (unkeyed _)
         (unkeyed _) _ _ id _ _ id)
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
  class : class_of le lt meet join;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> DistrLattice.class_of.

Variable (phT : phant T) (ord : order phT).

Let cls := unkeyed (class ord).

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) cls.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) cls.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) cls.
Definition lattice :=
  @Lattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) cls.
Definition distrLattice :=
  @DistrLattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) cls.

Variable (leT ltT : rel T) (meetT joinT : T -> T -> T).

Definition clone c of phant_id cls c :=
  @Pack phT leT ltT meetT joinT (unkeyed c).

Definition pack (m0 : total leT) :=
  fun (bord : DistrLattice.order phT) b
        & phant_id (DistrLattice.class bord) b =>
  fun m & phant_id m0 m =>
  @Pack phT leT ltT meetT joinT (unkeyed (@Class leT ltT meetT joinT b m)).

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
  (@clone _ (Phant _) _ le (unkeyed _) (unkeyed _) (unkeyed _) _ id)
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
  class : class_of le lt meet join bottom;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> Total.class_of.
Local Coercion base2 le lt meet join bottom
                     (c : class_of le lt meet join bottom) :
  BDistrLattice.class_of le lt meet join bottom :=
  BDistrLattice.Class (mixin c).

Variable (phT : phant T) (ord : order phT).

Let cls := unkeyed (class ord).

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) cls.
Definition bPOrder := @BPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) cls.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) cls.
Definition bMeetOrder :=
  @BMeet.Pack _ phT (le ord) (lt ord) (meet ord) (bottom ord) cls.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) cls.
Definition bJoinOrder :=
  @BJoin.Pack _ phT (le ord) (lt ord) (join ord) (bottom ord) cls.
Definition lattice :=
  @Lattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) cls.
Definition bLattice :=
  @BLattice.Pack
    _ phT (le ord) (lt ord) (meet ord) (join ord) (bottom ord) cls.
Definition distrLattice :=
  @DistrLattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) cls.
Definition bDistrLattice :=
  @BDistrLattice.Pack
    _ phT (le ord) (lt ord) (meet ord) (join ord) (bottom ord) cls.
Definition totalOrder :=
  @Total.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) cls.

Variable (leT ltT : rel T) (meetT joinT : T -> T -> T) (bottomT : T).

Definition pack :=
  fun (bord : Total.order phT) (b : Total.class_of leT ltT meetT joinT)
      & phant_id (Total.class bord) b =>
  fun (mord : BPOrder.order phT) m
      & phant_id (BPOrder.class mord) (BPOrder.Class (base := b) m) =>
  @Pack phT leT ltT meetT joinT bottomT (unkeyed (Class (base := b) m)).

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
  (@pack _ (Phant _) le (unkeyed _) (unkeyed _) (unkeyed _) (unkeyed _)
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
  class : class_of le lt meet join top;
}.

Unset Primitive Projections.

Local Coercion base : class_of >-> Total.class_of.
Local Coercion base2 le lt meet join top (c : class_of le lt meet join top) :
  TDistrLattice.class_of le lt meet join top :=
  TDistrLattice.Class (mixin c).

Variable (phT : phant T) (ord : order phT).

Let cls := unkeyed (class ord).

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) cls.
Definition tPOrder := @TPOrder.Pack _ phT (le ord) (lt ord) (top ord) cls.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) cls.
Definition tMeetOrder :=
  @TMeet.Pack _ phT (le ord) (lt ord) (meet ord) (top ord) cls.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) cls.
Definition tJoinOrder :=
  @TJoin.Pack _ phT (le ord) (lt ord) (join ord) (top ord) cls.
Definition lattice :=
  @Lattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) cls.
Definition tLattice :=
  @TLattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) (top ord) cls.
Definition distrLattice :=
  @DistrLattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) cls.
Definition tDistrLattice :=
  @TDistrLattice.Pack
    _ phT (le ord) (lt ord) (meet ord) (join ord) (top ord) cls.
Definition totalOrder :=
  @Total.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) cls.

Variable (leT ltT : rel T) (meetT joinT : T -> T -> T) (topT : T).

Definition pack :=
  fun (bord : Total.order phT) (b : Total.class_of leT ltT meetT joinT)
      & phant_id (Total.class bord) b =>
  fun (mord : TPOrder.order phT) m
      & phant_id (TPOrder.class mord) (TPOrder.Class (base := b) m) =>
  @Pack phT leT ltT meetT joinT topT (unkeyed (Class (base := b) m)).

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
  (@pack _ (Phant _) le (unkeyed _) (unkeyed _) (unkeyed _) (unkeyed _)
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
  class : class_of le lt meet join bottom top;
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

Let cls := unkeyed (class ord).

Definition pOrder := @POrder.Pack _ phT (le ord) (lt ord) cls.
Definition bPOrder := @BPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) cls.
Definition tPOrder := @TPOrder.Pack _ phT (le ord) (lt ord) (top ord) cls.
Definition tbPOrder :=
  @TBPOrder.Pack _ phT (le ord) (lt ord) (bottom ord) (top ord) cls.
Definition meetOrder := @Meet.Pack _ phT (le ord) (lt ord) (meet ord) cls.
Definition bMeetOrder :=
  @BMeet.Pack _ phT (le ord) (lt ord) (meet ord) (bottom ord) cls.
Definition tMeetOrder :=
  @TMeet.Pack _ phT (le ord) (lt ord) (meet ord) (top ord) cls.
Definition tbMeetOrder :=
  @TBMeet.Pack _ phT (le ord) (lt ord) (meet ord) (bottom ord) (top ord) cls.
Definition joinOrder := @Join.Pack _ phT (le ord) (lt ord) (join ord) cls.
Definition bJoinOrder :=
  @BJoin.Pack _ phT (le ord) (lt ord) (join ord) (bottom ord) cls.
Definition tJoinOrder :=
  @TJoin.Pack _ phT (le ord) (lt ord) (join ord) (top ord) cls.
Definition tbJoinOrder :=
  @TBJoin.Pack _ phT (le ord) (lt ord) (join ord) (bottom ord) (top ord) cls.
Definition lattice :=
  @Lattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) cls.
Definition bLattice :=
  @BLattice.Pack
    _ phT (le ord) (lt ord) (meet ord) (join ord) (bottom ord) cls.
Definition tLattice :=
  @TLattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) (top ord) cls.
Definition tbLattice :=
  @TBLattice.Pack
    _ phT (le ord) (lt ord) (meet ord) (join ord) (bottom ord) (top ord) cls.
Definition distrLattice :=
  @DistrLattice.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) cls.
Definition bDistrLattice :=
  @BDistrLattice.Pack
    _ phT (le ord) (lt ord) (meet ord) (join ord) (bottom ord) cls.
Definition tDistrLattice :=
  @TDistrLattice.Pack
    _ phT (le ord) (lt ord) (meet ord) (join ord) (top ord) cls.
Definition tbDistrLattice :=
  @TBDistrLattice.Pack
    _ phT (le ord) (lt ord) (meet ord) (join ord) (bottom ord) (top ord) cls.
Definition totalOrder :=
  @Total.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) cls.
Definition bTotalOrder :=
  @BTotal.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) (bottom ord) cls.
Definition tTotalOrder :=
  @TTotal.Pack _ phT (le ord) (lt ord) (meet ord) (join ord) (top ord) cls.

Variable (leT ltT : rel T) (meetT joinT : T -> T -> T) (bottomT topT : T).

Definition pack :=
  fun (bord : BTotal.order phT)
      (b : BTotal.class_of leT ltT meetT joinT bottomT)
      & phant_id (BTotal.class bord) b =>
  fun (mord : TPOrder.order phT) m
      & phant_id (TPOrder.class mord) (TPOrder.Class (base := b) m) =>
  @Pack phT leT ltT meetT joinT bottomT topT (unkeyed (Class (base := b) m)).

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
  (@pack _ (Phant _) le (unkeyed _) (unkeyed _) (unkeyed _) (unkeyed _)
         (unkeyed _) _ _ id _ _ id)
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

Definition rcomparable : rel T := fun x y => (x <= y) || (y <= x).

Local Notation "x >< y" := (~~ (rcomparable x y)).

Definition rge : simpl_rel T := [rel x y | y <= x].
Definition rgt : simpl_rel T := [rel x y | y < x].

Definition rleif x y C : Prop := ((x <= y) * ((x == y) = C))%type.

Definition rle_of_leif x y C (le_xy : rleif x y C) : x <= y := le_xy.1.

Definition rlteif x y C := if C then x <= y else x < y.

Definition rmin x y := if x < y then x else y.
Definition rmax x y := if x < y then y else x.

Definition rarg_min {I : finType} := @extremum T I le.
Definition rarg_max {I : finType} := @extremum T I rge.

End POrderDef.

Section LatticeDef.

Context {T: eqType} (ord : {lattice T}).
Implicit Types (x y : T).

Local Notation "x <= y" := (le ord x y).
Local Notation "x < y" := (lt ord x y).
Local Notation "x >< y" := (~~ (rcomparable ord x y)).
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
Notation "x >=<_ r y" := (rcomparable r x y)
  (at level 70, r at level 2, no associativity, format "x  >=<_ r  y").
Notation "x ><_ r y" := (~~ rcomparable r x y)
  (at level 70, r at level 2, no associativity, format "x  ><_ r  y").
Notation ">=<_ r y" :=
  [pred x | x >=<_r y] (at level 80, r at level 2, format ">=<_ r  y").
Notation "><_ r y" :=
  [pred x | x ><_r y] (at level 80, r at level 2, format "><_ r  y").

Notation "x <=_ r y ?= 'iff' C" := (rleif r x y C)
  (at level 70, C at level 1, r at level 2,
   format "x '[hv'  <=_ r '/'  y  ?=  'iff'  C ']'").

Notation "x <_ r y ?<= 'if' C" := (rlteif r x y C)
  (at level 71, C at level 1, r at level 1, y at next level,
   format "x '[hv'  <_ r '/'  y  ?<=  'if'  C ']'").

End Syntax.

(* ========================================================================== *)

Module DualOrder.
Section DualOrder.

Variable T : eqType.

Canonical dual_pOrder (ord : {pOrder T}) := dual_pOrder ord.

Canonical dual_bPOrder (ord : {tPOrder T}) :=
  BPOrder (rdual_rel <=:ord) (rdual_rel <:ord) (rdual_bottom (top ord))
          (TPOrder.mixin (TPOrder.class ord) :
             BPOrder.mixin_of (dual_pOrder ord) _).

Canonical dual_tPOrder (ord : {bPOrder T}) :=
  TPOrder (rdual_rel <=:ord) (rdual_rel <:ord) (rdual_top (bottom ord))
          (BPOrder.mixin (BPOrder.class ord) :
             TPOrder.mixin_of (dual_pOrder ord) _).

(* BUG, TODO: can we design better packagers to infer head symbols of         *)
(* operators from existing instances, or should operators other than [le] be  *)
(* specified (e.g., TBOrder le lt bottom top) to synthesize proper            *)
(* unification hints anyway? Clone notations have the same issue.             *)
Canonical dual_tbPOrder (ord : {tbPOrder T}) := [tbPOrder of rdual_rel <=:ord].

Canonical dual_meetOrder (ord : {joinOrder T}) :=
  MeetOrder (rdual_rel <=:ord) (rdual_rel <:ord) (rdual_meet (join ord))
            (Join.mixin (Join.class ord)).

Canonical dual_bMeetOrder (ord : {tJoinOrder T}) :=
  [bMeetOrder of rdual_rel <=:ord].

Canonical dual_tMeetOrder (ord : {bJoinOrder T}) :=
  [tMeetOrder of rdual_rel <=:ord].

Canonical dual_tbMeetOrder (ord : {tbJoinOrder T}) :=
  [tbMeetOrder of rdual_rel <=:ord].

Canonical dual_joinOrder (ord : {meetOrder T}) :=
  JoinOrder (rdual_rel <=:ord) (rdual_rel <:ord) (rdual_join (meet ord))
            (Meet.mixin (Meet.class ord) : Join.mixin_of (dual_pOrder ord) _).

Canonical dual_bJoinOrder (ord : {tMeetOrder T}) :=
  [bJoinOrder of rdual_rel <=:ord].

Canonical dual_tJoinOrder (ord : {bMeetOrder T}) :=
  [tJoinOrder of rdual_rel <=:ord].

Canonical dual_tbJoinOrder (ord : {tbMeetOrder T}) :=
  [tbJoinOrder of rdual_rel <=:ord].

Canonical dual_lattice (ord : {lattice T}) := [lattice of rdual_rel <=:ord].

Canonical dual_bLattice (ord : {tLattice T}) := [bLattice of rdual_rel <=:ord].

Canonical dual_tLattice (ord : {bLattice T}) := [tLattice of rdual_rel <=:ord].

Canonical dual_tbLattice (ord : {tbLattice T}) :=
  [tbLattice of rdual_rel <=:ord].

Canonical dual_distrLattice (ord : {distrLattice T}) :=
  DistrLattice
    (rdual_rel <=:ord) (rdual_rel <:ord)
    (rdual_meet (join ord)) (rdual_join (meet ord))
    (let mixin := DistrLattice.mixin (DistrLattice.class ord) in
     @DistrLattice.Mixin _ (dual_lattice ord)
       (DistrLattice.rjoinIl mixin) (DistrLattice.rmeetUl mixin)).

Canonical dual_bDistrLattice (ord : {tDistrLattice T}) :=
  [bDistrLattice of rdual_rel <=:ord].

Canonical dual_tDistrLattice (ord : {bDistrLattice T}) :=
  [tDistrLattice of rdual_rel <=:ord].

Canonical dual_tbDistrLattice (ord : {tbDistrLattice T}) :=
  [tbDistrLattice of rdual_rel <=:ord].

Canonical dual_totalOrder (ord : {totalOrder T}) :=
  TotalOrder
    (rdual_rel <=:ord) (rdual_rel <:ord)
    (rdual_meet (join ord)) (rdual_join (meet ord))
    (fun x y => Total.mixin (Total.class ord) y x).

Canonical dual_bTotalOrder (ord : {tTotalOrder T}) :=
  [bTotalOrder of rdual_rel <=:ord].

Canonical dual_tTotalOrder (ord : {bTotalOrder T}) :=
  [tTotalOrder of rdual_rel <=:ord].

Canonical dual_tbTotalOrder (ord : {tbTotalOrder T}) :=
  [tbTotalOrder of rdual_rel <=:ord].

End DualOrder.

Module Exports.

Canonical dual_pOrder.
Canonical dual_bPOrder.
Canonical dual_tPOrder.
Canonical dual_tbPOrder.
Canonical dual_meetOrder.
Canonical dual_bMeetOrder.
Canonical dual_tMeetOrder.
Canonical dual_tbMeetOrder.
Canonical dual_joinOrder.
Canonical dual_bJoinOrder.
Canonical dual_tJoinOrder.
Canonical dual_tbJoinOrder.
Canonical dual_lattice.
Canonical dual_bLattice.
Canonical dual_tLattice.
Canonical dual_tbLattice.
Canonical dual_distrLattice.
Canonical dual_bDistrLattice.
Canonical dual_tDistrLattice.
Canonical dual_tbDistrLattice.
Canonical dual_totalOrder.
Canonical dual_bTotalOrder.
Canonical dual_tTotalOrder.
Canonical dual_tbTotalOrder.

End Exports.
End DualOrder.
Import DualOrder.Exports.

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
Local Notation rge := (rge ord).
Local Notation rgt := (rgt ord).
Local Notation rcomparable := (rcomparable ord).
Local Notation rleif := (rleif ord).
Local Notation rlteif := (rlteif ord).
Local Notation rmin := (rmin ord).
Local Notation rmax := (rmax ord).
Local Notation le_xor_gt := (le_xor_gt le lt).
Local Notation lt_xor_ge := (lt_xor_ge le lt).
Local Notation compare := (compare lt).
Local Notation incompare := (incompare lt rcomparable).
Local Notation rarg_min := (rarg_min ord).
Local Notation rarg_max := (rarg_max ord).

Local Notation "x <= y" := (x <=_ord y).
Local Notation "x < y" := (x <_ord y).
Local Notation "x >= y" := (x >=_ord y) (only parsing).
Local Notation "x > y" := (x >_ord y) (only parsing).
Local Notation "x <= y <= z" := ((x <= y) && (y <= z)).
Local Notation "x < y < z"   := ((x < y) && (y < z)).
Local Notation "x < y <= z"  := ((x < y) && (y <= z)).
Local Notation "x <= y < z"  := ((x <= y) && (y < z)).

Local Notation ">=<%O" := rcomparable.
Local Notation ">=< y" := (>=<_ord y).
Local Notation "x >=< y" := (x >=<_ord y).
Local Notation "x >< y" := (x ><_ord y).

Local Notation "x <= y ?= 'iff' C" := (rleif x y C).
Local Notation "x < y ?<= 'if' C" := (rlteif x y C).

Lemma rgeE x y : rge x y = (y <= x). Proof. by []. Qed.
Lemma rgtE x y : rgt x y = (y < x). Proof. by []. Qed.

Lemma rlexx : reflexive le.
Proof. by case: ord => ? ? []. Qed.
Hint Resolve rlexx : core.
Hint Extern 0 (is_true (_ <=__ _)) => exact: rlexx : core.

Definition rle_refl : reflexive le := rlexx.
Definition rge_refl : reflexive rge := rlexx.

Lemma rle_anti : antisymmetric le.
Proof. by case: ord => le lt [] ? ? ? ha ? x y /andP []; exact: ha. Qed.

Lemma rge_anti : antisymmetric rge.
Proof. by move=> x y /rle_anti. Qed.

Lemma rle_trans : transitive le.
Proof. by case: ord => ? ? []. Qed.

Lemma rge_trans : transitive rge.
Proof. by move=> ? ? ? ? /rle_trans; apply. Qed.

Lemma rlt_def x y : (x < y) = (y != x) && (x <= y).
Proof. by case: ord => ? ? []. Qed.

Lemma rlt_neqAle x y : (x < y) = (x != y) && (x <= y).
Proof. by rewrite rlt_def eq_sym. Qed.

Lemma rltxx x : x < x = false.
Proof. by rewrite rlt_def eqxx. Qed.

Definition rlt_irreflexive : irreflexive lt := rltxx.
Hint Resolve rlt_irreflexive : core.

Definition rltexx := (rlexx, rltxx).

Lemma rle_eqVlt x y : (x <= y) = (x == y) || (x < y).
Proof. by rewrite rlt_neqAle; case: eqP => //= ->; rewrite rlexx. Qed.

Lemma rlt_eqF x y : x < y -> x == y = false.
Proof. by rewrite rlt_neqAle => /andP [/negbTE->]. Qed.

Lemma rgt_eqF x y : y < x -> x == y = false.
Proof. by apply: contraTF => /eqP ->; rewrite rltxx. Qed.

Lemma req_le x y : (x == y) = (x <= y <= x).
Proof. by apply/eqP/idP => [->|/rle_anti]; rewrite ?rlexx. Qed.

Lemma rltW x y : x < y -> x <= y.
Proof. by rewrite rle_eqVlt orbC => ->. Qed.

Lemma rlt_le_trans y x z : x < y -> y <= z -> x < z.
Proof.
rewrite !rlt_neqAle => /andP [nexy lexy leyz]; rewrite (rle_trans lexy) // andbT.
by apply: contraNneq nexy => eqxz; rewrite eqxz req_le leyz andbT in lexy *.
Qed.

Lemma rlt_trans : transitive lt.
Proof. by move=> y x z le1 /rltW le2; apply/(@rlt_le_trans y). Qed.

Lemma rle_lt_trans y x z : x <= y -> y < z -> x < z.
Proof. by rewrite rle_eqVlt => /orP [/eqP ->|/rlt_trans t /t]. Qed.

Lemma rlt_nsym x y : x < y -> y < x -> False.
Proof. by move=> xy /(rlt_trans xy); rewrite rltxx. Qed.

Lemma rlt_asym x y : x < y < x = false.
Proof. by apply/negP => /andP []; apply: rlt_nsym. Qed.

Lemma rle_gtF x y : x <= y -> y < x = false.
Proof.
by move=> le_xy; apply/negP => /rlt_le_trans /(_ le_xy); rewrite rltxx.
Qed.

Lemma rlt_geF x y : (x < y) -> y <= x = false.
Proof.
by move=> le_xy; apply/negP => /rle_lt_trans /(_ le_xy); rewrite rltxx.
Qed.

Definition rlt_gtF x y hxy := rle_gtF (@rltW x y hxy).

Lemma rlt_leAnge x y : (x < y) = (x <= y) && ~~ (y <= x).
Proof.
apply/idP/idP => [ltxy|/andP[lexy Nleyx]]; first by rewrite rltW // rlt_geF.
by rewrite rlt_neqAle lexy andbT; apply: contraNneq Nleyx => ->.
Qed.

Lemma rlt_le_asym x y : x < y <= x = false.
Proof. by rewrite rlt_neqAle -andbA -req_le eq_sym andNb. Qed.

Lemma rle_lt_asym x y : x <= y < x = false.
Proof. by rewrite andbC rlt_le_asym. Qed.

Definition rlte_anti := (=^~ req_le, rlt_asym, rlt_le_asym, rle_lt_asym).

Lemma rlt_sorted_uniq_le s : sorted lt s = uniq s && sorted le s.
Proof.
rewrite (sorted_pairwise rle_trans) (sorted_pairwise rlt_trans) uniq_pairwise.
by rewrite -pairwise_relI; apply/eq_pairwise => ? ?; rewrite rlt_neqAle.
Qed.

Lemma rlt_sorted_eq s1 s2 : sorted lt s1 -> sorted lt s2 -> s1 =i s2 -> s1 = s2.
Proof. by apply: irr_sorted_eq => //; apply: rlt_trans. Qed.

Lemma rle_sorted_eq s1 s2 :
  sorted le s1 -> sorted le s2 -> perm_eq s1 s2 -> s1 = s2.
Proof. exact/sorted_eq/rle_anti/rle_trans. Qed.

Lemma rsort_le_id s : sorted le s -> sort le s = s.
Proof. exact/sorted_sort/rle_trans. Qed.

Lemma rle_sorted_ltn_nth (x0 : T) (s : seq T) : sorted <=:ord s ->
 {in [pred n | (n < size s)%N] &,
    {homo nth x0 s : i j / (i < j)%N >-> i <= j}}.
Proof. exact/sorted_ltn_nth/rle_trans. Qed.

Lemma rle_sorted_leq_nth (x0 : T) (s : seq T) : sorted <=:ord s ->
  {in [pred n | (n < size s)%N] &,
    {homo nth x0 s : i j / (i <= j)%N >-> i <= j}}.
Proof. exact: (sorted_leq_nth rle_trans rle_refl). Qed.

Lemma rlt_sorted_leq_nth (x0 : T) (s : seq T) : sorted <:ord s ->
  {in [pred n | (n < size s)%N] &,
    {mono nth x0 s : i j / (i <= j)%N >-> i <= j}}.
Proof.
rewrite rlt_sorted_uniq_le => /andP[s_uniq le_s].
apply: (total_homo_mono_in _ _ ltn_neqAle rlt_neqAle rle_anti leq_total) => //.
move=> i j ilt jlt ltij; rewrite rlt_neqAle rle_sorted_leq_nth// 1?ltnW//.
by rewrite nth_uniq// ltn_eqF.
Qed.

Lemma rlt_sorted_ltn_nth (x0 : T) (s : seq T) : sorted <:ord s ->
  {in [pred n | (n < size s)%N] &,
    {mono nth x0 s : i j / (i < j)%N >-> i < j}}.
Proof.
move=> ss; have := rlt_sorted_leq_nth x0 ss.
exact: (anti_mono_in _ ltn_neqAle rlt_neqAle anti_leq).
Qed.

Lemma rfilter_lt_nth x0 s i : sorted <:ord s -> (i < size s)%N ->
  [seq x <- s | x < nth x0 s i] = take i s.
Proof.
move=> ss i_lt/=; rewrite -[X in filter _ X](mkseq_nth x0) filter_map.
under eq_in_filter => j do
  [rewrite ?mem_iota => j_s /=; rewrite rlt_sorted_ltn_nth//].
by rewrite (filter_iota_ltn 0) ?map_nth_iota0 // ltnW.
Qed.

Lemma rcount_lt_nth x0 s i : sorted <:ord s -> (i < size s)%N ->
  count (fun y => y < nth x0 s i) s = i.
Proof.
by move=> ss i_lt; rewrite -size_filter/= rfilter_lt_nth// size_take i_lt.
Qed.

Lemma rfilter_le_nth x0 s i : sorted <:ord s -> (i < size s)%N ->
  [seq x <- s | x <= nth x0 s i] = take i.+1 s.
Proof.
move=> ss i_lt/=; rewrite -[X in filter _ X](mkseq_nth x0) filter_map.
under eq_in_filter => j do
  [rewrite ?mem_iota => j_s /=; rewrite rlt_sorted_leq_nth//].
by rewrite (filter_iota_leq 0)// map_nth_iota0.
Qed.

Lemma rcount_le_nth x0 s i : sorted <:ord s -> (i < size s)%N ->
  count (le^~ (nth x0 s i)) s = i.+1.
Proof.
by move=> ss i_lt; rewrite -size_filter/= rfilter_le_nth// size_takel.
Qed.

Lemma rcount_lt_le_mem x s : (count (lt^~ x) s < count (le^~ x) s)%N = (x \in s).
Proof.
have := count_predUI (pred1 x) (lt^~ x) s.
have -> : count (predI (pred1 x) (lt^~ x)) s = 0%N.
  rewrite (@eq_count _ _ pred0) ?count_pred0 // => y /=.
  by rewrite rlt_def; case: eqP => //= ->; rewrite eqxx.
have /eq_count->: predU (pred1 x) (lt^~ x) =1 le^~ x.
  by move=> y /=; rewrite rle_eqVlt.
by rewrite addn0 => ->; rewrite -add1n leq_add2r -has_count has_pred1.
Qed.

Lemma rsorted_filter_lt x s :
  sorted <=:ord s -> [seq y <- s | y < x] = take (count (lt^~ x) s) s.
Proof.
elim: s => [//|y s IHs]/=; rewrite (path_sortedE rle_trans) => /andP[le_y_s ss].
case: ifP => [|ltyxF]; rewrite IHs//.
rewrite (@eq_in_count _ _ pred0) ?count_pred0/= ?take0// => z.
by move=> /(allP le_y_s) yz; apply: contraFF ltyxF; apply: rle_lt_trans.
Qed.

Lemma rsorted_filter_le x s :
  sorted <=:ord s -> [seq y <- s | y <= x] = take (count (le^~ x) s) s.
Proof.
elim: s => [//|y s IHs]/=; rewrite (path_sortedE rle_trans) => /andP[le_y_s ss].
case: ifP => [|leyxF]; rewrite IHs//.
rewrite (@eq_in_count _ _ pred0) ?count_pred0/= ?take0// => z.
by move=> /(allP le_y_s) yz; apply: contraFF leyxF; apply: rle_trans.
Qed.

Lemma rnth_count_le x x0 s i : sorted <=:ord s ->
  (i < count (le^~ x) s)%N -> nth x0 s i <= x.
Proof.
move=> ss iltc; rewrite -(nth_take _ iltc) -rsorted_filter_le //.
by apply/(all_nthP _ (filter_all (le^~ x) _)); rewrite size_filter.
Qed.

Lemma rnth_count_lt x x0 s i : sorted <=:ord s ->
  (i < count (lt^~ x) s)%N -> nth x0 s i < x.
Proof.
move=> ss iltc; rewrite -(nth_take _ iltc) -rsorted_filter_lt //.
by apply/(all_nthP _ (filter_all (lt^~ x) _)); rewrite size_filter.
Qed.

Lemma rcomparable_leNgt x y : x >=< y -> (x <= y) = ~~ (y < x).
Proof.
move=> c_xy; apply/idP/idP => [/rle_gtF/negP/negP//|]; rewrite rlt_neqAle.
by move: c_xy => /orP [] -> //; rewrite andbT negbK => /eqP ->.
Qed.

Lemma rcomparable_ltNge x y : x >=< y -> (x < y) = ~~ (y <= x).
Proof.
move=> c_xy; apply/idP/idP => [/rlt_geF/negP/negP//|].
by rewrite rlt_neqAle req_le; move: c_xy => /orP [] -> //; rewrite andbT.
Qed.

Lemma rcomparable_ltgtP x y : x >=< y ->
  compare x y (rmin y x) (rmin x y) (rmax y x) (rmax x y)
  (y == x) (x == y) (x >= y) (x <= y) (x > y) (x < y).
Proof.
rewrite /rmin /rmax /rcomparable !rle_eqVlt [y == x]eq_sym.
have := (eqVneq x y, (boolP (x < y), boolP (y < x))).
move=> [[->//|neq_xy /=] [[] xy [] //=]] ; do ?by rewrite ?rltxx; constructor.
  by rewrite rltxx in xy.
by rewrite rle_gtF // rltW.
Qed.

Lemma rcomparable_leP x y : x >=< y ->
  le_xor_gt x y (rmin y x) (rmin x y) (rmax y x) (rmax x y) (x <= y) (y < x).
Proof. by case/rcomparable_ltgtP=> [?|?|->]; constructor; rewrite // rltW. Qed.

Lemma rcomparable_ltP x y : x >=< y ->
  lt_xor_ge x y (rmin y x) (rmin x y) (rmax y x) (rmax x y) (y <= x) (x < y).
Proof. by case/rcomparable_ltgtP=> [?|?|->]; constructor; rewrite // rltW. Qed.

Lemma rcomparable_sym x y : (y >=< x) = (x >=< y).
Proof. by rewrite /rcomparable orbC. Qed.

Lemma rcomparablexx x : x >=< x.
Proof. by rewrite /rcomparable rlexx. Qed.

Lemma rincomparable_eqF x y : (x >< y) -> (x == y) = false.
Proof. by apply: contraNF => /eqP ->; rewrite rcomparablexx. Qed.

Lemma rincomparable_leF x y : (x >< y) -> (x <= y) = false.
Proof. by apply: contraNF; rewrite /rcomparable => ->. Qed.

Lemma rincomparable_ltF x y : (x >< y) -> (x < y) = false.
Proof. by rewrite rlt_neqAle => /rincomparable_leF ->; rewrite andbF. Qed.

Lemma rcomparableP x y : incompare x y
  (rmin y x) (rmin x y) (rmax y x) (rmax x y)
  (y == x) (x == y) (x >= y) (x <= y) (x > y) (x < y) (y >=< x) (x >=< y).
Proof.
rewrite ![y >=< _]rcomparable_sym; have [c_xy|i_xy] := boolP (x >=< y).
  by case: (rcomparable_ltgtP c_xy) => ?; constructor.
by rewrite /rmin /rmax ?rincomparable_eqF ?rincomparable_leF;
   rewrite ?rincomparable_ltF// 1?rcomparable_sym //; constructor.
Qed.

Lemma rle_comparable (x y : T) : x <= y -> x >=< y.
Proof. by case: rcomparableP. Qed.

Lemma rlt_comparable (x y : T) : x < y -> x >=< y.
Proof. by case: rcomparableP. Qed.

Lemma rge_comparable (x y : T) : y <= x -> x >=< y.
Proof. by case: rcomparableP. Qed.

Lemma rgt_comparable (x y : T) : y < x -> x >=< y.
Proof. by case: rcomparableP. Qed.

(* rleif *)

Lemma rleifP x y C : reflect (x <= y ?= iff C) (if C then x == y else x < y).
Proof.
rewrite /rleif rle_eqVlt; apply: (iffP idP)=> [|[]].
  by case: C => [/eqP->|lxy]; rewrite ?eqxx // lxy rlt_eqF.
by case/orP=> [/eqP->|lxy] <-; rewrite ?eqxx // rlt_eqF.
Qed.

Lemma rleif_refl x C : reflect (x <= x ?= iff C) C.
Proof. by apply: (iffP idP) => [-> | <-] //; split; rewrite ?eqxx. Qed.

Lemma rleif_trans x1 x2 x3 C12 C23 :
  x1 <= x2 ?= iff C12 -> x2 <= x3 ?= iff C23 -> x1 <= x3 ?= iff C12 && C23.
Proof.
move=> ltx12 ltx23; apply/rleifP; rewrite -ltx12.
case eqx12: (x1 == x2).
  by rewrite (eqP eqx12) rlt_neqAle !ltx23 andbT; case C23.
by rewrite (@rlt_le_trans x2) ?ltx23 // rlt_neqAle eqx12 ltx12.
Qed.

Lemma rleif_le x y : x <= y -> x <= y ?= iff (x >= y).
Proof. by move=> lexy; split=> //; rewrite req_le lexy. Qed.

Lemma rleif_eq x y : x <= y -> x <= y ?= iff (x == y).
Proof. by []. Qed.

Lemma rge_leif x y C : x <= y ?= iff C -> (y <= x) = C.
Proof. by case=> le_xy; rewrite req_le le_xy. Qed.

Lemma rlt_leif x y C : x <= y ?= iff C -> (x < y) = ~~ C.
Proof. by move=> le_xy; rewrite rlt_neqAle !le_xy andbT. Qed.

Lemma rltNleif x y C : x <= y ?= iff ~~ C -> (x < y) = C.
Proof. by move/rlt_leif; rewrite negbK. Qed.

Lemma req_leif x y C : x <= y ?= iff C -> (x == y) = C.
Proof. by move/rleifP; case: C rcomparableP => [] []. Qed.

Lemma reqTleif x y C : x <= y ?= iff C -> C -> x = y.
Proof. by move=> /req_leif<-/eqP. Qed.

(* rlteif *)

Lemma rlteif_trans x y z C1 C2 :
  x < y ?<= if C1 -> y < z ?<= if C2 -> x < z ?<= if C1 && C2.
Proof.
case: C1 C2 => [][];
  [exact: rle_trans | exact: rle_lt_trans | exact: rlt_le_trans | exact: rlt_trans].
Qed.

Lemma rlteif_anti C1 C2 x y :
  (x < y ?<= if C1) && (y < x ?<= if C2) = C1 && C2 && (x == y).
Proof. by case: C1 C2 => [][]; rewrite rlte_anti. Qed.

Lemma rlteifxx x C : (x < x ?<= if C) = C.
Proof. by case: C; rewrite /= rltexx. Qed.

Lemma rlteifNF x y C : y < x ?<= if ~~ C -> x < y ?<= if C = false.
Proof. by case: C => [/rlt_geF|/rle_gtF]. Qed.

Lemma rlteifS x y C : x < y -> x < y ?<= if C.
Proof. by case: C => //= /rltW. Qed.

Lemma rlteifT x y : x < y ?<= if true = (x <= y). Proof. by []. Qed.

Lemma rlteifF x y : x < y ?<= if false = (x < y). Proof. by []. Qed.

Lemma rlteif_orb x y : {morph rlteif x y : p q / p || q}.
Proof. by case=> [][] /=; case: rcomparableP. Qed.

Lemma rlteif_andb x y : {morph rlteif x y : p q / p && q}.
Proof. by case=> [][] /=; case: rcomparableP. Qed.

Lemma rlteif_imply C1 C2 x y : C1 ==> C2 -> x < y ?<= if C1 -> x < y ?<= if C2.
Proof. by case: C1 C2 => [][] //= _ /rltW. Qed.

Lemma rlteifW C x y : x < y ?<= if C -> x <= y.
Proof. by case: C => // /rltW. Qed.

Lemma rltrW_lteif C x y : x < y -> x < y ?<= if C.
Proof. by case: C => // /rltW. Qed.

Lemma rlteifN C x y : x < y ?<= if ~~ C -> ~~ (y < x ?<= if C).
Proof. by case: C => /=; case: rcomparableP. Qed.

(* rmin and rmax *)

Lemma rminElt x y : rmin x y = if x < y then x else y. Proof. by []. Qed.
Lemma rmaxElt x y : rmax x y = if x < y then y else x. Proof. by []. Qed.

Lemma rminEle x y : rmin x y = if x <= y then x else y.
Proof. by case: rcomparableP. Qed.

Lemma rmaxEle x y : rmax x y = if x <= y then y else x.
Proof. by case: rcomparableP. Qed.

Lemma rcomparable_minEgt x y : x >=< y -> rmin x y = if x > y then y else x.
Proof. by case: rcomparableP. Qed.
Lemma rcomparable_maxEgt x y : x >=< y -> rmax x y = if x > y then x else y.
Proof. by case: rcomparableP. Qed.
Lemma rcomparable_minEge x y : x >=< y -> rmin x y = if x >= y then y else x.
Proof. by case: rcomparableP. Qed.
Lemma rcomparable_maxEge x y : x >=< y -> rmax x y = if x >= y then x else y.
Proof. by case: rcomparableP. Qed.

Lemma rmin_l x y : x <= y -> rmin x y = x. Proof. by case: rcomparableP. Qed.
Lemma rmin_r x y : y <= x -> rmin x y = y. Proof. by case: rcomparableP. Qed.
Lemma rmax_l x y : y <= x -> rmax x y = x. Proof. by case: rcomparableP. Qed.
Lemma rmax_r x y : x <= y -> rmax x y = y. Proof. by case: rcomparableP. Qed.

Lemma rminxx : idempotent (rmin : T -> T -> T).
Proof. by rewrite /rmin => x; rewrite rltxx. Qed.

Lemma rmaxxx : idempotent (rmax : T -> T -> T).
Proof. by rewrite /rmax => x; rewrite rltxx. Qed.

Lemma req_minl x y : (rmin x y == x) = (x <= y).
Proof. by rewrite !(fun_if, if_arg) eqxx; case: rcomparableP. Qed.

Lemma req_maxr x y : (rmax x y == y) = (x <= y).
Proof. by rewrite !(fun_if, if_arg) eqxx; case: rcomparableP. Qed.

Lemma rmin_idPl x y : reflect (rmin x y = x) (x <= y).
Proof. by apply: (iffP idP); rewrite (rwP eqP) req_minl. Qed.

Lemma rmax_idPr x y : reflect (rmax x y = y) (x <= y).
Proof. by apply: (iffP idP); rewrite (rwP eqP) req_maxr. Qed.

Lemma rmin_minKx x y : rmin (rmin x y) y = rmin x y.
Proof. by rewrite !(fun_if, if_arg) rltxx/=; case: rcomparableP. Qed.

Lemma rmin_minxK x y : rmin x (rmin x y) = rmin x y.
Proof. by rewrite !(fun_if, if_arg) rltxx/=; case: rcomparableP. Qed.

Lemma rmax_maxKx x y : rmax (rmax x y) y = rmax x y.
Proof. by rewrite !(fun_if, if_arg) rltxx/=; case: rcomparableP. Qed.

Lemma rmax_maxxK x y : rmax x (rmax x y) = rmax x y.
Proof. by rewrite !(fun_if, if_arg) rltxx/=; case: rcomparableP. Qed.

Lemma rcomparable_minl z : {in >=< z &, forall x y, rmin x y >=< z}.
Proof. by move=> x y cmp_xz cmp_yz; rewrite /rmin; case: ifP. Qed.

Lemma rcomparable_minr z : {in >=<%O z &, forall x y, z >=< rmin x y}.
Proof. by move=> x y cmp_xz cmp_yz; rewrite /rmin; case: ifP. Qed.

Lemma rcomparable_maxl z : {in >=< z &, forall x y, rmax x y >=< z}.
Proof. by move=> x y cmp_xz cmp_yz; rewrite /rmax; case: ifP. Qed.

Lemma rcomparable_maxr z : {in >=<%O z &, forall x y, z >=< rmax x y}.
Proof. by move=> x y cmp_xz cmp_yz; rewrite /rmax; case: ifP. Qed.

Section Comparable2.
Variables (z x y : T) (cmp_xy : x >=< y).

Lemma rcomparable_minC : rmin x y = rmin y x.
Proof. by case: rcomparableP cmp_xy. Qed.

Lemma rcomparable_maxC : rmax x y = rmax y x.
Proof. by case: rcomparableP cmp_xy. Qed.

Lemma rcomparable_eq_minr : (rmin x y == y) = (y <= x).
Proof. by rewrite !(fun_if, if_arg) eqxx; case: rcomparableP cmp_xy. Qed.

Lemma rcomparable_eq_maxl : (rmax x y == x) = (y <= x).
Proof. by rewrite !(fun_if, if_arg) eqxx; case: rcomparableP cmp_xy. Qed.

Lemma rcomparable_min_idPr : reflect (rmin x y = y) (y <= x).
Proof. by apply: (iffP idP); rewrite (rwP eqP) rcomparable_eq_minr. Qed.

Lemma rcomparable_max_idPl : reflect (rmax x y = x) (y <= x).
Proof. by apply: (iffP idP); rewrite (rwP eqP) rcomparable_eq_maxl. Qed.

Lemma rcomparable_le_minr : (z <= rmin x y) = (z <= x) && (z <= y).
Proof.
case: rcomparableP cmp_xy => // [||<-//]; rewrite ?andbb//; last rewrite andbC;
  by case: (rcomparableP z) => // [/rlt_trans xlt/xlt|->] /rltW.
Qed.

Lemma rcomparable_le_minl : (rmin x y <= z) = (x <= z) || (y <= z).
Proof.
case: rcomparableP cmp_xy => // [||<-//]; rewrite ?orbb//; last rewrite orbC;
  by move=> xy _; apply/idP/idP => [->|/orP[]]//; apply/rle_trans/rltW.
Qed.

Lemma rcomparable_lt_minr : (z < rmin x y) = (z < x) && (z < y).
Proof.
case: rcomparableP cmp_xy => // [||<-//]; rewrite ?andbb//; last rewrite andbC;
  by case: (rcomparableP z) => // /rlt_trans xlt/xlt.
Qed.

Lemma rcomparable_lt_minl : (rmin x y < z) = (x < z) || (y < z).
Proof.
case: rcomparableP cmp_xy => // [||<-//]; rewrite ?orbb//; last rewrite orbC;
  by move=> xy _; apply/idP/idP => [->|/orP[]]//; apply/rlt_trans.
Qed.

Lemma rcomparable_le_maxr : (z <= rmax x y) = (z <= x) || (z <= y).
Proof.
case: rcomparableP cmp_xy => // [||<-//]; rewrite ?orbb//; first rewrite orbC;
  by move=> xy _; apply/idP/idP => [->|/orP[]]// /rle_trans->//; apply/rltW.
Qed.

Lemma rcomparable_le_maxl : (rmax x y <= z) = (x <= z) && (y <= z).
Proof.
case: rcomparableP cmp_xy => // [||<-//]; rewrite ?andbb//; first rewrite andbC;
  by case: (rcomparableP z) => // [ylt /rlt_trans /(_ _)/rltW|->/rltW]->.
Qed.

Lemma rcomparable_lt_maxr : (z < rmax x y) = (z < x) || (z < y).
Proof.
case: rcomparableP cmp_xy => // [||<-//]; rewrite ?orbb//; first rewrite orbC;
  by move=> xy _; apply/idP/idP => [->|/orP[]]// /rlt_trans->.
Qed.

Lemma rcomparable_lt_maxl : (rmax x y < z) = (x < z) && (y < z).
Proof.
case: rcomparableP cmp_xy => // [||<-//]; rewrite ?andbb//; first rewrite andbC;
by case: (rcomparableP z) => // ylt /rlt_trans->.
Qed.

Lemma rcomparable_minxK : rmax (rmin x y) y = y.
Proof. by rewrite !(fun_if, if_arg) rltxx/=; case: rcomparableP cmp_xy. Qed.

Lemma rcomparable_minKx : rmax x (rmin x y) = x.
Proof. by rewrite !(fun_if, if_arg) rltxx/=; case: rcomparableP cmp_xy. Qed.

Lemma rcomparable_maxxK : rmin (rmax x y) y = y.
Proof. by rewrite !(fun_if, if_arg) rltxx/=; case: rcomparableP cmp_xy. Qed.

Lemma rcomparable_maxKx : rmin x (rmax x y) = x.
Proof. by rewrite !(fun_if, if_arg) rltxx/=; case: rcomparableP cmp_xy. Qed.

Lemma rcomparable_lteifNE C : x >=< y -> x < y ?<= if ~~ C = ~~ (y < x ?<= if C).
Proof. by case: C => /=; case: rcomparableP. Qed.

Lemma rcomparable_lteif_minr C :
  (z < rmin x y ?<= if C) = (z < x ?<= if C) && (z < y ?<= if C).
Proof. by case: C; rewrite /= (rcomparable_le_minr, rcomparable_lt_minr). Qed.

Lemma rcomparable_lteif_minl C :
  (rmin x y < z ?<= if C) = (x < z ?<= if C) || (y < z ?<= if C).
Proof. by case: C; rewrite /= (rcomparable_le_minl, rcomparable_lt_minl). Qed.

Lemma rcomparable_lteif_maxr C :
  (z < rmax x y ?<= if C) = (z < x ?<= if C) || (z < y ?<= if C).
Proof. by case: C; rewrite /= (rcomparable_le_maxr, rcomparable_lt_maxr). Qed.

Lemma rcomparable_lteif_maxl C :
  (rmax x y < z ?<= if C) = (x < z ?<= if C) && (y < z ?<= if C).
Proof. by case: C; rewrite /= (rcomparable_le_maxl, rcomparable_lt_maxl). Qed.

End Comparable2.

Section Comparable3.
Variables (x y z : T) (cmp_xy : x >=< y) (cmp_xz : x >=< z) (cmp_yz : y >=< z).
Let P := rcomparableP.

Lemma rcomparable_minA : rmin x (rmin y z) = rmin (rmin x y) z.
Proof.
move: cmp_xy cmp_xz cmp_yz; rewrite !(fun_if, if_arg)/=.
move: (P x y) (P x z) (P y z) => [xy|xy|xy|<-] [xz|xz|xz|<-]// []//= yz.
- by have := rlt_trans xy (rlt_trans yz xz); rewrite rltxx.
- by have := rlt_trans xy (rlt_trans xz yz); rewrite rltxx.
- by have := rlt_trans xy xz; rewrite yz rltxx.
Qed.

Lemma rcomparable_maxA : rmax x (rmax y z) = rmax (rmax x y) z.
Proof.
move: cmp_xy cmp_xz cmp_yz; rewrite !(fun_if, if_arg)/=.
move: (P x y) (P x z) (P y z) => [xy|xy|xy|<-] [xz|xz|xz|<-]// []//= yz.
- by have := rlt_trans xy (rlt_trans yz xz); rewrite rltxx.
- by have := rlt_trans xy (rlt_trans xz yz); rewrite rltxx.
- by have := rlt_trans xy xz; rewrite yz rltxx.
Qed.

Lemma rcomparable_max_minl : rmax (rmin x y) z = rmin (rmax x z) (rmax y z).
Proof.
move: cmp_xy cmp_xz cmp_yz; rewrite !(fun_if, if_arg)/=.
move: (P x y) (P x z) (P y z).
move=> [xy|xy|xy|<-] [xz|xz|xz|<-] [yz|yz|yz|//->]//= _; rewrite ?rltxx//.
- by have := rlt_trans xy (rlt_trans yz xz); rewrite rltxx.
- by have := rlt_trans xy (rlt_trans xz yz); rewrite rltxx.
Qed.

Lemma rcomparable_min_maxl : rmin (rmax x y) z = rmax (rmin x z) (rmin y z).
Proof.
move: cmp_xy cmp_xz cmp_yz; rewrite !(fun_if, if_arg)/=.
move: (P x y) (P x z) (P y z).
move=> [xy|xy|xy|<-] [xz|xz|xz|<-] []yz//= _; rewrite ?rltxx//.
- by have := rlt_trans xy (rlt_trans yz xz); rewrite rltxx.
- by have := rlt_trans xy yz; rewrite rltxx.
- by have := rlt_trans xy (rlt_trans xz yz); rewrite rltxx.
- by have := rlt_trans xy xz; rewrite yz rltxx.
Qed.

End Comparable3.

Lemma rcomparable_minAC x y z : x >=< y -> x >=< z -> y >=< z ->
  rmin (rmin x y) z = rmin (rmin x z) y.
Proof.
move=> xy xz yz; rewrite -rcomparable_minA// [rmin y z]rcomparable_minC//.
by rewrite rcomparable_minA// 1?rcomparable_sym.
Qed.

Lemma rcomparable_maxAC x y z : x >=< y -> x >=< z -> y >=< z ->
  rmax (rmax x y) z = rmax (rmax x z) y.
Proof.
move=> xy xz yz; rewrite -rcomparable_maxA// [rmax y z]rcomparable_maxC//.
by rewrite rcomparable_maxA// 1?rcomparable_sym.
Qed.

Lemma rcomparable_minCA x y z : x >=< y -> x >=< z -> y >=< z ->
  rmin x (rmin y z) = rmin y (rmin x z).
Proof.
move=> xy xz yz; rewrite rcomparable_minA// [rmin x y]rcomparable_minC//.
by rewrite -rcomparable_minA// 1?rcomparable_sym.
Qed.

Lemma rcomparable_maxCA x y z : x >=< y -> x >=< z -> y >=< z ->
  rmax x (rmax y z) = rmax y (rmax x z).
Proof.
move=> xy xz yz; rewrite rcomparable_maxA// [rmax x y]rcomparable_maxC//.
by rewrite -rcomparable_maxA// 1?rcomparable_sym.
Qed.

Lemma rcomparable_minACA x y z t :
    x >=< y -> x >=< z -> x >=< t -> y >=< z -> y >=< t -> z >=< t ->
  rmin (rmin x y) (rmin z t) = rmin (rmin x z) (rmin y t).
Proof.
move=> xy xz xt yz yt zt; rewrite rcomparable_minA// ?rcomparable_minl//.
rewrite [rmin _ z]rcomparable_minAC// -rcomparable_minA// ?rcomparable_minl//.
by rewrite inE rcomparable_sym.
Qed.

Lemma rcomparable_maxACA x y z t :
    x >=< y -> x >=< z -> x >=< t -> y >=< z -> y >=< t -> z >=< t ->
  rmax (rmax x y) (rmax z t) = rmax (rmax x z) (rmax y t).
Proof.
move=> xy xz xt yz yt zt; rewrite rcomparable_maxA// ?rcomparable_maxl//.
rewrite [rmax _ z]rcomparable_maxAC// -rcomparable_maxA// ?rcomparable_maxl//.
by rewrite inE rcomparable_sym.
Qed.

Lemma rcomparable_max_minr x y z : x >=< y -> x >=< z -> y >=< z ->
  rmax x (rmin y z) = rmin (rmax x y) (rmax x z).
Proof.
move=> xy xz yz; rewrite ![rmax x _]rcomparable_maxC// ?rcomparable_minr//.
by rewrite rcomparable_max_minl// 1?rcomparable_sym.
Qed.

Lemma rcomparable_min_maxr x y z : x >=< y -> x >=< z -> y >=< z ->
  rmin x (rmax y z) = rmax (rmin x y) (rmin x z).
Proof.
move=> xy xz yz; rewrite ![rmin x _]rcomparable_minC// ?rcomparable_maxr//.
by rewrite rcomparable_min_maxl// 1?rcomparable_sym.
Qed.

Section ArgExtremum.

Context (I : finType) (i0 : I) (P : {pred I}) (F : I -> T) (Pi0 : P i0).
Hypothesis F_comparable : {in P &, forall i j, F i >=< F j}.

Lemma rcomparable_arg_minP : extremum_spec le P F (rarg_min i0 P F).
Proof.
by apply: extremum_inP => // [x _|y x z _ _ _]; [apply: rlexx|apply: rle_trans].
Qed.

Lemma rcomparable_arg_maxP : extremum_spec rge P F (rarg_max i0 P F).
Proof.
apply: extremum_inP => // [x _|y x z _ _ _|]; [exact: rlexx|exact: rge_trans|].
by move=> x y xP yP; rewrite orbC [_ || _]F_comparable.
Qed.

End ArgExtremum.

(* monotonicity *)

Lemma rmono_in_leif (A : {pred T}) (f : T -> T) C :
   {in A &, {mono f : x y / x <= y}} ->
  {in A &, forall x y, (f x <= f y ?= iff C) = (x <= y ?= iff C)}.
Proof. by move=> mf x y Ax Ay; rewrite /rleif !req_le !mf. Qed.

Lemma rmono_leif (f : T -> T) C :
    {mono f : x y / x <= y} ->
  forall x y, (f x <= f y ?= iff C) = (x <= y ?= iff C).
Proof. by move=> mf x y; rewrite /rleif !req_le !mf. Qed.

Lemma rnmono_in_leif (A : {pred T}) (f : T -> T) C :
    {in A &, {mono f : x y /~ x <= y}} ->
  {in A &, forall x y, (f x <= f y ?= iff C) = (y <= x ?= iff C)}.
Proof. by move=> mf x y Ax Ay; rewrite /rleif !req_le !mf. Qed.

Lemma rnmono_leif (f : T -> T) C : {mono f : x y /~ x <= y} ->
  forall x y, (f x <= f y ?= iff C) = (y <= x ?= iff C).
Proof. by move=> mf x y; rewrite /rleif !req_le !mf. Qed.

Lemma rcomparable_bigl x x0 op I (P : pred I) F (s : seq I) :
  {in >=< x &, forall y z, op y z >=< x} -> x0 >=< x ->
  {in P, forall i, F i >=< x} -> \big[op/x0]_(i <- s | P i) F i >=< x.
Proof. by move=> *; elim/big_ind : _. Qed.

Lemma rcomparable_bigr x x0 op I (P : pred I) F (s : seq I) :
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

Lemma rcomparable_contraTle b x y : x >=< y -> (y < x -> ~~ b) -> (b -> x <= y).
Proof. by case: rcomparableP; case: b. Qed.

Lemma rcomparable_contraTlt b x y : x >=< y -> (y <= x -> ~~ b) -> (b -> x < y).
Proof. by case: rcomparableP; case: b. Qed.

Lemma rcomparable_contraPle P x y : x >=< y -> (y < x -> ~ P) -> (P -> x <= y).
Proof. by case: rcomparableP => // _ _ /(_ isT). Qed.

Lemma rcomparable_contraPlt P x y : x >=< y -> (y <= x -> ~ P) -> (P -> x < y).
Proof. by case: rcomparableP => // _ _ /(_ isT). Qed.

Lemma rcomparable_contraNle b x y : x >=< y -> (y < x -> b) -> (~~ b -> x <= y).
Proof. by case: rcomparableP; case: b. Qed.

Lemma rcomparable_contraNlt b x y : x >=< y -> (y <= x -> b) -> (~~ b -> x < y).
Proof. by case: rcomparableP; case: b. Qed.

Lemma rcomparable_contra_not_le P x y : x >=< y -> (y < x -> P) -> (~ P -> x <= y).
Proof. by case: rcomparableP => // _ _ /(_ isT). Qed.

Lemma rcomparable_contra_not_lt P x y : x >=< y -> (y <= x -> P) -> (~ P -> x < y).
Proof. by case: rcomparableP => // _ _ /(_ isT). Qed.

Lemma rcomparable_contraFle b x y : x >=< y -> (y < x -> b) -> (b = false -> x <= y).
Proof. by case: rcomparableP; case: b => // _ _ /implyP. Qed.

Lemma rcomparable_contraFlt b x y : x >=< y -> (y <= x -> b) -> (b = false -> x < y).
Proof. by case: rcomparableP; case: b => // _ _ /implyP. Qed.

Lemma rcontra_leT b x y : (~~ b -> x < y) -> (y <= x -> b).
Proof. by case: rcomparableP; case: b. Qed.

Lemma rcontra_ltT b x y : (~~ b -> x <= y) -> (y < x -> b).
Proof. by case: rcomparableP; case: b. Qed.

Lemma rcontra_leN b x y : (b -> x < y) -> (y <= x -> ~~ b).
Proof. by case: rcomparableP; case: b. Qed.

Lemma rcontra_ltN b x y : (b -> x <= y) -> (y < x -> ~~ b).
Proof. by case: rcomparableP; case: b. Qed.

Lemma rcontra_le_not P x y : (P -> x < y) -> (y <= x -> ~ P).
Proof. by case: rcomparableP => // _ PF _ /PF. Qed.

Lemma rcontra_lt_not P x y : (P -> x <= y) -> (y < x -> ~ P).
Proof. by case: rcomparableP => // _ PF _ /PF. Qed.

Lemma rcontra_leF b x y : (b -> x < y) -> (y <= x -> b = false).
Proof. by case: rcomparableP; case: b => // _ /implyP. Qed.

Lemma rcontra_ltF b x y : (b -> x <= y) -> (y < x -> b = false).
Proof. by case: rcomparableP; case: b => // _ /implyP. Qed.

Lemma rcomparable_contra_leq_le m n x y : x >=< y ->
  (y < x -> (n < m)%N) -> ((m <= n)%N -> x <= y).
Proof. by case: rcomparableP; case: ltngtP. Qed.

Lemma rcomparable_contra_leq_lt m n x y : x >=< y ->
  (y <= x -> (n < m)%N) -> ((m <= n)%N -> x < y).
Proof. by case: rcomparableP; case: ltngtP. Qed.

Lemma rcomparable_contra_ltn_le m n x y : x >=< y ->
  (y < x -> (n <= m)%N) -> ((m < n)%N -> x <= y).
Proof. by case: rcomparableP; case: ltngtP. Qed.

Lemma rcomparable_contra_ltn_lt m n x y : x >=< y ->
  (y <= x -> (n <= m)%N) -> ((m < n)%N -> x < y).
Proof. by case: rcomparableP; case: ltngtP. Qed.

Lemma rcontra_le_leq x y m n : ((n < m)%N -> y < x) -> (x <= y -> (m <= n)%N).
Proof. by case: rcomparableP; case: ltngtP. Qed.

Lemma rcontra_le_ltn x y m n : ((n <= m)%N -> y < x) -> (x <= y -> (m < n)%N).
Proof. by case: rcomparableP; case: ltngtP. Qed.

Lemma rcontra_lt_leq x y m n : ((n < m)%N -> y <= x) -> (x < y -> (m <= n)%N).
Proof. by case: rcomparableP; case: ltngtP. Qed.

Lemma rcontra_lt_ltn x y m n : ((n <= m)%N -> y <= x) -> (x < y -> (m < n)%N).
Proof. by case: rcomparableP; case: ltngtP. Qed.

Lemma rcomparable_contra_le x y z t : z >=<_ord2 t ->
  (t <_ord2 z -> y < x) -> (x <= y -> z <=_ord2 t).
Proof. by do 2![case: rcomparableP => //= ?]. Qed.

Lemma rcomparable_contra_le_lt x y z t : z >=<_ord2 t ->
  (t <=_ord2 z -> y < x) -> (x <= y -> z <_ord2 t).
Proof. by do 2![case: rcomparableP => //= ?]. Qed.

Lemma rcomparable_contra_lt_le x y z t : z >=<_ord2 t ->
  (t <_ord2 z -> y <= x) -> (x < y -> z <=_ord2 t).
Proof. by do 2![case: rcomparableP => //= ?]. Qed.

Lemma rcomparable_contra_lt x y z t : z >=<_ord2 t ->
 (t <=_ord2 z -> y <= x) -> (x < y -> z <_ord2 t).
Proof. by do 2![case: rcomparableP => //= ?]. Qed.

End ContraTheory.

Section POrderMonotonyTheory.

Context {T T' : eqType} {ord : {pOrder T}} {ord' : {pOrder T'}}.
Implicit Types (m n p : nat) (x y z : T) (u v w : T').
Variables (D D' : {pred T}) (f : T -> T').

Let leT_refl := @rlexx _ ord.
Let leT'_refl := @rlexx _ ord'.
Let ltT_neqAle := @rlt_neqAle _ ord.
Let ltT'_neqAle := @rlt_neqAle _ ord'.
Let ltT_def := @rlt_def _ ord.
Let leT_anti := @rle_anti _ ord.

Let ge_antiT : antisymmetric (rge ord).
Proof. by move=> ? ? /rle_anti. Qed.

Lemma rltW_homo : {homo f : x y / x <_ord y >-> x <_ord' y} ->
                 {homo f : x y / x <=_ord y >-> x <=_ord' y}.
Proof. exact: homoW. Qed.

Lemma rltW_nhomo : {homo f : x y / y <_ord x >-> x <_ord' y} ->
                  {homo f : x y / y <=_ord x >-> x <=_ord' y}.
Proof. exact: homoW. Qed.

Lemma rinj_homo_lt :
  injective f -> {homo f : x y / x <=_ord y >-> x <=_ord' y} ->
  {homo f : x y / x <_ord y >-> x <_ord' y}.
Proof. exact: inj_homo. Qed.

Lemma rinj_nhomo_lt :
  injective f -> {homo f : x y / y <=_ord x >-> x <=_ord' y} ->
  {homo f : x y / y <_ord x >-> x <_ord' y}.
Proof. exact: inj_homo. Qed.

Lemma rinc_inj : {mono f : x y / x <=_ord y >-> x <=_ord' y} -> injective f.
Proof. exact: mono_inj. Qed.

Lemma rdec_inj : {mono f : x y / y <=_ord x >-> x <=_ord' y} -> injective f.
Proof. exact: mono_inj. Qed.

Lemma rleW_mono : {mono f : x y / x <=_ord y >-> x <=_ord' y} ->
                 {mono f : x y / x <_ord y >-> x <_ord' y}.
Proof. exact: anti_mono. Qed.

Lemma rleW_nmono : {mono f : x y / y <=_ord x >-> x <=_ord' y} ->
                  {mono f : x y / y <_ord x >-> x <_ord' y}.
Proof. exact: anti_mono. Qed.

(* Monotony in D D' *)
Lemma rltW_homo_in : {in D & D', {homo f : x y / x <_ord y >-> x <_ord' y}} ->
                    {in D & D', {homo f : x y / x <=_ord y >-> x <=_ord' y}}.
Proof. exact: homoW_in. Qed.

Lemma rltW_nhomo_in : {in D & D', {homo f : x y / y <_ord x >-> x <_ord' y}} ->
                     {in D & D', {homo f : x y / y <=_ord x >-> x <=_ord' y}}.
Proof. exact: homoW_in. Qed.

Lemma rinj_homo_lt_in :
  {in D & D', injective f} ->
  {in D & D', {homo f : x y / x <=_ord y >-> x <=_ord' y}} ->
  {in D & D', {homo f : x y / x <_ord y >-> x <_ord' y}}.
Proof. exact: inj_homo_in. Qed.

Lemma rinj_nhomo_lt_in :
  {in D & D', injective f} ->
  {in D & D', {homo f : x y / y <=_ord x >-> x <=_ord' y}} ->
  {in D & D', {homo f : x y / y <_ord x >-> x <_ord' y}}.
Proof. exact: inj_homo_in. Qed.

Lemma rinc_inj_in : {in D &, {mono f : x y / x <=_ord y >-> x <=_ord' y}} ->
                   {in D &, injective f}.
Proof. exact: mono_inj_in. Qed.

Lemma rdec_inj_in : {in D &, {mono f : x y / y <=_ord x >-> x <=_ord' y}} ->
                   {in D &, injective f}.
Proof. exact: mono_inj_in. Qed.

Lemma rleW_mono_in : {in D &, {mono f : x y / x <=_ord y >-> x <=_ord' y}} ->
                    {in D &, {mono f : x y / x <_ord y >-> x <_ord' y}}.
Proof. exact: anti_mono_in. Qed.

Lemma rleW_nmono_in : {in D &, {mono f : x y / y <=_ord x >-> x <=_ord' y}} ->
                     {in D &, {mono f : x y / y <_ord x >-> x <_ord' y}}.
Proof. exact: anti_mono_in. Qed.

End POrderMonotonyTheory.

End POrderTheory.

#[global] Hint Extern 0 (is_true (le _ _ _)) => apply: rlexx : core.
#[global] Hint Resolve rlexx rltxx rlt_irreflexive rltW rlt_eqF : core.

Arguments rleifP {T ord x y C}.
Arguments rleif_refl {T ord x C}.
Arguments rmono_in_leif [T ord A f C].
Arguments rnmono_in_leif [T ord A f C].
Arguments rmono_leif [T ord f C].
Arguments rnmono_leif [T ord f C].
Arguments rmin_idPl {T ord x y}.
Arguments rmax_idPr {T ord x y}.
Arguments rcomparable_min_idPr {T ord x y _}.
Arguments rcomparable_max_idPl {T ord x y _}.

Module Import BPOrderTheory.
Section BPOrderTheory.
Context {T : eqType} {ord : {bPOrder T}}.
Implicit Types (x y : T).

Local Notation "x <= y" := (x <=_ord y).
Local Notation "x < y" := (x <_ord y).
Local Notation "0" := (bottom ord).

Lemma rle0x x : 0 <= x. Proof. by case: ord => ? ? ? []. Qed.

Lemma rlex0 x : (x <= 0) = (x == 0).
Proof. by rewrite rle_eqVlt (rle_gtF (rle0x _)) orbF. Qed.

Lemma rltx0 x : (x < 0) = false.
Proof. by rewrite rlt_neqAle rlex0 andNb. Qed.

Lemma rlt0x x : (0 < x) = (x != 0).
Proof. by rewrite rlt_neqAle rle0x andbT eq_sym. Qed.

Variant eq0_xor_gt0 x : bool -> bool -> Set :=
    Eq0NotPOs : x = 0 -> eq0_xor_gt0 x true false
  | POsNotEq0 : 0 < x -> eq0_xor_gt0 x false true.

Lemma rposxP x : eq0_xor_gt0 x (x == 0) (0 < x).
Proof. by rewrite rlt0x; have [] := eqVneq; constructor; rewrite ?rlt0x. Qed.

End BPOrderTheory.
End BPOrderTheory.

Module Import TPOrderTheory.
Section TPOrderTheory.
Context {T : eqType} {ord : {tPOrder T}}.
Let ord_dual := [bPOrder of rdual_rel <=:ord].
Implicit Types (x y : T).

Local Notation "x <= y" := (x <=_ord y).
Local Notation "x < y" := (x <_ord y).
Local Notation "1" := (top ord).

Lemma rlex1 (x : T) : x <= 1. Proof. exact: (@rle0x _ ord_dual). Qed.
Lemma rle1x x : (1 <= x) = (x == 1). Proof. exact: (@rlex0 _ ord_dual). Qed.
Lemma rlt1x x : (1 < x) = false. Proof. exact: (@rltx0 _ ord_dual). Qed.
Lemma rltx1 x : (x < 1) = (x != 1). Proof. exact: (@rlt0x _ ord_dual). Qed.

End TPOrderTheory.
End TPOrderTheory.

#[global] Hint Extern 0 (is_true (le _ (bottom _) _)) => apply: rle0x : core.
#[global] Hint Extern 0 (is_true (le _ _ (top _))) => apply: rlex1 : core.

Module Import MeetTheory.
Section MeetTheory.
Context {L : eqType} {ord : {meetOrder L}}.
Implicit Types (x y : L).

Local Notation meet := (meet ord).

Local Notation "x <= y" := (x <=_ord y).
Local Notation "x `&` y" := (meet x y).

Lemma rmeetC : commutative meet. Proof. by case: ord => ? ? ? [? []]. Qed.
Lemma rmeetA : associative meet. Proof. by case: ord => ? ? ? [? []]. Qed.
Lemma rleEmeet x y : (x <= y) = (x `&` y == x).
Proof. by case: ord => ? ? ? [? []]. Qed.

Lemma rmeetxx : idempotent meet.
Proof. by move=> x; apply/eqP; rewrite -rleEmeet. Qed.
Lemma rmeetAC : right_commutative meet.
Proof. by move=> x y z; rewrite -!rmeetA [X in _ `&` X]rmeetC. Qed.
Lemma rmeetCA : left_commutative meet.
Proof. by move=> x y z; rewrite !rmeetA [X in X `&` _]rmeetC. Qed.
Lemma rmeetACA : interchange meet meet.
Proof. by move=> x y z t; rewrite !rmeetA [X in X `&` _]rmeetAC. Qed.

Lemma rmeetKI y x : x `&` (x `&` y) = x `&` y.
Proof. by rewrite rmeetA rmeetxx. Qed.
Lemma rmeetIK y x : (x `&` y) `&` y = x `&` y.
Proof. by rewrite -rmeetA rmeetxx. Qed.
Lemma rmeetKIC y x : x `&` (y `&` x) = x `&` y.
Proof. by rewrite rmeetC rmeetIK rmeetC. Qed.
Lemma rmeetIKC y x : y `&` x `&` y = x `&` y.
Proof. by rewrite rmeetAC rmeetC rmeetxx. Qed.

(* interaction with order *)

Lemma rlexI x y z : (x <= y `&` z) = (x <= y) && (x <= z).
Proof.
rewrite !rleEmeet; apply/eqP/andP => [<-|[/eqP<- /eqP<-]].
  by rewrite rmeetA rmeetIK eqxx -rmeetA rmeetACA rmeetxx rmeetAC eqxx.
by rewrite -[X in X `&` _]rmeetA rmeetIK rmeetA.
Qed.

Lemma rleIxl x y z : y <= x -> y `&` z <= x.
Proof. by rewrite !rleEmeet rmeetAC => /eqP ->. Qed.

Lemma rleIxr x y z : z <= x -> y `&` z <= x.
Proof. by rewrite !rleEmeet -rmeetA => /eqP ->. Qed.

Lemma rleIx2 x y z : (y <= x) || (z <= x) -> y `&` z <= x.
Proof. by case/orP => [/rleIxl|/rleIxr]. Qed.

Lemma rleIr x y : y `&` x <= x.
Proof. by rewrite rleIx2 ?rlexx ?orbT. Qed.

Lemma rleIl x y : x `&` y <= x.
Proof. by rewrite rleIx2 ?rlexx ?orbT. Qed.

Lemma rmeet_idPl {x y} : reflect (x `&` y = x) (x <= y).
Proof. by rewrite rleEmeet; apply/eqP. Qed.
Lemma rmeet_idPr {x y} : reflect (y `&` x = x) (x <= y).
Proof. by rewrite rmeetC; apply/rmeet_idPl. Qed.

Lemma rmeet_l x y : x <= y -> x `&` y = x. Proof. exact/rmeet_idPl. Qed.
Lemma rmeet_r x y : y <= x -> x `&` y = y. Proof. exact/rmeet_idPr. Qed.

Lemma rleIidl x y : (x <= x `&` y) = (x <= y).
Proof. by rewrite !rleEmeet rmeetKI. Qed.
Lemma rleIidr x y : (x <= y `&` x) = (x <= y).
Proof. by rewrite !rleEmeet rmeetKIC. Qed.

Lemma req_meetl x y : (x `&` y == x) = (x <= y).
Proof. by apply/esym/rleEmeet. Qed.

Lemma req_meetr x y : (x `&` y == y) = (y <= x).
Proof. by rewrite rmeetC req_meetl. Qed.

Lemma rleI2 x y z t : x <= z -> y <= t -> x `&` y <= z `&` t.
Proof. by move=> xz yt; rewrite rlexI !rleIx2 ?xz ?yt ?orbT //. Qed.

End MeetTheory.
End MeetTheory.

Arguments rmeet_idPl {L ord x y}.
Arguments rmeet_idPr {L ord x y}.

Module Import BMeetTheory.
Section BMeetTheory.
Context {L : eqType} {ord : {bMeetOrder L}}.

Local Notation meet := (meet ord).
Local Notation "0" := (bottom ord).

Lemma rmeet0x : left_zero 0 meet. Proof. by move=> x; apply/rmeet_idPl. Qed.
Lemma rmeetx0 : right_zero 0 meet. Proof. by move=> x; apply/rmeet_idPr. Qed.

Canonical meet_muloid := Monoid.MulLaw rmeet0x rmeetx0.

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

Lemma rmeetx1 : right_id 1 meet. Proof. by move=> x; apply/rmeet_idPl. Qed.
Lemma rmeet1x : left_id 1 meet. Proof. by move=> x; apply/rmeet_idPr. Qed.

Lemma rmeet_eq1 x y : (x `&` y == 1) = (x == 1) && (y == 1).
Proof. by rewrite !(@req_le _ ord) !rlex1 rlexI. Qed.

Canonical meet_monoid := Monoid.Law rmeetA rmeet1x rmeetx1.
Canonical meet_comoid := Monoid.ComLaw rmeetC.

Lemma rmeets_inf_seq T (r : seq T) (P : {pred T}) (F : T -> L) (x : T) :
  x \in r -> P x -> \big[meet/1]_(i <- r | P i) F i <= F x.
Proof. by move=> xr Px; rewrite (big_rem x) ?Px //= rleIl. Qed.

Lemma rmeets_max_seq T (r : seq T) (P : {pred T}) (F : T -> L) (x : T) (u : L) :
  x \in r -> P x -> F x <= u -> \big[meet/1]_(x <- r | P x) F x <= u.
Proof. by move=> ? ?; apply/rle_trans/rmeets_inf_seq. Qed.

Lemma rmeets_inf I (j : I) (P : {pred I}) (F : I -> L) :
   P j -> \big[meet/1]_(i | P i) F i <= F j.
Proof. exact: rmeets_inf_seq. Qed.

Lemma rmeets_max I (j : I) (u : L) (P : {pred I}) (F : I -> L) :
   P j -> F j <= u -> \big[meet/1]_(i | P i) F i <= u.
Proof. exact: rmeets_max_seq. Qed.

Lemma rmeets_ge J (r : seq J) (P : {pred J}) (F : J -> L) (u : L) :
  (forall x : J, P x -> u <= F x) -> u <= \big[meet/1]_(x <- r | P x) F x.
Proof. by move=> leFm; elim/big_rec: _ => // i x Px xu; rewrite rlexI leFm. Qed.

Lemma rmeetsP_seq T (r : seq T) (P : {pred T}) (F : T -> L) (l : L) :
  reflect (forall x : T, x \in r -> P x -> l <= F x)
          (l <= \big[meet/1]_(x <- r | P x) F x).
Proof.
apply: (iffP idP) => leFm => [x xr Px|].
  exact/(rle_trans leFm)/rmeets_inf_seq.
by rewrite big_seq_cond rmeets_ge // => x /andP[/leFm].
Qed.

Lemma rmeetsP I (l : L) (P : {pred I}) (F : I -> L) :
   reflect (forall i : I, P i -> l <= F i) (l <= \big[meet/1]_(i | P i) F i).
Proof. by apply: (iffP (rmeetsP_seq _ _ _ _)) => H ? ?; apply: H. Qed.

Lemma rle_meets I (A B : {set I}) (F : I -> L) :
   A \subset B -> \big[meet/1]_(i in B) F i <= \big[meet/1]_(i in A) F i.
Proof. by move=> /subsetP AB; apply/rmeetsP => i iA; apply/rmeets_inf/AB. Qed.

Lemma rmeets_setU I (A B : {set I}) (F : I -> L) :
  \big[meet/1]_(i in (A :|: B)) F i =
  \big[meet/1]_(i in A) F i `&` \big[meet/1]_(i in B) F i.
Proof.
rewrite -!big_enum; have /= <- := @big_cat _ _ meet_comoid.
apply/eq_big_idem; first exact: rmeetxx.
by move=> ?; rewrite mem_cat !mem_enum inE.
Qed.

Lemma rmeets_seq I (r : seq I) (F : I -> L) :
  \big[meet/1]_(i <- r) F i = \big[meet/1]_(i in r) F i.
Proof.
by rewrite -big_enum; apply/eq_big_idem => ?; rewrite /= ?rmeetxx ?mem_enum.
Qed.

End TMeetTheory.
End TMeetTheory.

Module Import JoinTheory.
Section JoinTheory.
Context {L : eqType} {ord : {joinOrder L}}.
Let ord_dual := [meetOrder of rdual_rel <=:ord].
Implicit Types (x y : L).

Local Notation join := (join ord).

Local Notation "x <= y" := (x <=_ord y).
Local Notation "x `|` y" := (join x y).

Lemma rjoinC : commutative join. Proof. exact: (@rmeetC _ ord_dual). Qed.
Lemma rjoinA : associative join. Proof. exact: (@rmeetA _ ord_dual). Qed.
Lemma rleEjoin x y : (x <= y) = (x `|` y == y).
Proof. by rewrite rjoinC; apply: (@rleEmeet _ ord_dual). Qed.

Lemma rjoinxx : idempotent join. Proof. exact: (@rmeetxx _ ord_dual). Qed.
Lemma rjoinAC : right_commutative join. Proof. exact: (@rmeetAC _ ord_dual). Qed.
Lemma rjoinCA : left_commutative join. Proof. exact: (@rmeetCA _ ord_dual). Qed.
Lemma rjoinACA : interchange join join.
Proof. exact: (@rmeetACA _ ord_dual). Qed.

Lemma rjoinKU y x : x `|` (x `|` y) = x `|` y.
Proof. exact: (@rmeetKI _ ord_dual). Qed.
Lemma rjoinUK y x : (x `|` y) `|` y = x `|` y.
Proof. exact: (@rmeetIK _ ord_dual). Qed.
Lemma rjoinKUC y x : x `|` (y `|` x) = x `|` y.
Proof. exact: (@rmeetKIC _ ord_dual). Qed.
Lemma rjoinUKC y x : y `|` x `|` y = x `|` y.
Proof. exact: (@rmeetIKC _ ord_dual). Qed.

(* interaction with order *)
Lemma rleUx x y z : (x `|` y <= z) = (x <= z) && (y <= z).
Proof. exact: (@rlexI _ ord_dual). Qed.
Lemma rlexUl x y z : x <= y -> x <= y `|` z.
Proof. exact: (@rleIxl _ ord_dual). Qed.
Lemma rlexUr x y z : x <= z -> x <= y `|` z.
Proof. exact: (@rleIxr _ ord_dual). Qed.
Lemma rlexU2 x y z : (x <= y) || (x <= z) -> x <= y `|` z.
Proof. exact: (@rleIx2 _ ord_dual). Qed.

Lemma rleUr x y : x <= y `|` x. Proof. exact: (@rleIr _ ord_dual). Qed.
Lemma rleUl x y : x <= x `|` y. Proof. exact: (@rleIl _ ord_dual). Qed.

Lemma rjoin_idPl {x y} : reflect (y `|` x = y) (x <= y).
Proof. exact: (@rmeet_idPl _ ord_dual). Qed.
Lemma rjoin_idPr {x y} : reflect (x `|` y = y) (x <= y).
Proof. exact: (@rmeet_idPr _ ord_dual). Qed.

Lemma rjoin_l x y : y <= x -> x `|` y = x. Proof. exact/rjoin_idPl. Qed.
Lemma rjoin_r x y : x <= y -> x `|` y = y. Proof. exact/rjoin_idPr. Qed.

Lemma rleUidl x y : (x `|` y <= y) = (x <= y).
Proof. exact: (@rleIidr _ ord_dual). Qed.
Lemma rleUidr x y : (y `|` x <= y) = (x <= y).
Proof. exact: (@rleIidl _ ord_dual). Qed.

Lemma req_joinl x y : (x `|` y == x) = (y <= x).
Proof. exact: (@req_meetl _ ord_dual). Qed.
Lemma req_joinr x y : (x `|` y == y) = (x <= y).
Proof. exact: (@req_meetr _ ord_dual). Qed.

Lemma rleU2 x y z t : x <= z -> y <= t -> x `|` y <= z `|` t.
Proof. exact: (@rleI2 _ ord_dual). Qed.

End JoinTheory.
End JoinTheory.

Arguments rjoin_idPl {L ord x y}.
Arguments rjoin_idPr {L ord x y}.

Module Import BJoinTheory.
Section BJoinTheory.
Context {L : eqType} {ord : {bJoinOrder L}}.
Let ord_dual := [tMeetOrder of rdual_rel <=:ord].
Implicit Types (I : finType) (T : eqType) (x y : L).

Local Notation join := (join ord).

Local Notation "x <= y" := (x <=_ord y).
Local Notation "x `|` y" := (join x y).
Local Notation "0" := (bottom ord).

Lemma rjoinx0 : right_id 0 join. Proof. exact: (@rmeetx1 _ ord_dual). Qed.
Lemma rjoin0x : left_id 0 join. Proof. exact: (@rmeet1x _ ord_dual). Qed.

Lemma rjoin_eq0 x y : (x `|` y == 0) = (x == 0) && (y == 0).
Proof. exact: (@rmeet_eq1 _ ord_dual). Qed.

Canonical join_monoid := Monoid.Law rjoinA rjoin0x rjoinx0.
Canonical join_comoid := Monoid.ComLaw rjoinC.

Lemma rjoins_sup_seq T (r : seq T) (P : {pred T}) (F : T -> L) (x : T) :
  x \in r -> P x -> F x <= \big[join/0]_(i <- r | P i) F i.
Proof. exact: (@rmeets_inf_seq _ ord_dual). Qed.

Lemma rjoins_min_seq T (r : seq T) (P : {pred T}) (F : T -> L) (x : T) (l : L) :
  x \in r -> P x -> l <= F x -> l <= \big[join/0]_(x <- r | P x) F x.
Proof. exact: (@rmeets_max_seq _ ord_dual). Qed.

Lemma rjoins_sup I (j : I) (P : {pred I}) (F : I -> L) :
  P j -> F j <= \big[join/0]_(i | P i) F i.
Proof. exact: (@rmeets_inf _ ord_dual). Qed.

Lemma rjoins_min I (j : I) (l : L) (P : {pred I}) (F : I -> L) :
  P j -> l <= F j -> l <= \big[join/0]_(i | P i) F i.
Proof. exact: (@rmeets_max _ ord_dual). Qed.

Lemma rjoins_le J (r : seq J) (P : {pred J}) (F : J -> L) (u : L) :
  (forall x : J, P x -> F x <= u) -> \big[join/0]_(x <- r | P x) F x <= u.
Proof. exact: (@rmeets_ge _ ord_dual). Qed.

Lemma rjoinsP_seq T (r : seq T) (P : {pred T}) (F : T -> L) (u : L) :
  reflect (forall x : T, x \in r -> P x -> F x <= u)
          (\big[join/0]_(x <- r | P x) F x <= u).
Proof. exact: (@rmeetsP_seq _ ord_dual). Qed.

Lemma rjoinsP I (u : L) (P : {pred I}) (F : I -> L) :
  reflect (forall i : I, P i -> F i <= u) (\big[join/0]_(i | P i) F i <= u).
Proof. exact: (@rmeetsP _ ord_dual). Qed.

Lemma rle_joins I (A B : {set I}) (F : I -> L) :
  A \subset B -> \big[join/0]_(i in A) F i <= \big[join/0]_(i in B) F i.
Proof. exact: (@rle_meets _ ord_dual). Qed.

Lemma rjoins_setU I (A B : {set I}) (F : I -> L) :
  \big[join/0]_(i in (A :|: B)) F i =
  \big[join/0]_(i in A) F i `|` \big[join/0]_(i in B) F i.
Proof. exact: (@rmeets_setU _ ord_dual). Qed.

Lemma rjoins_seq I (r : seq I) (F : I -> L) :
  \big[join/0]_(i <- r) F i = \big[join/0]_(i in r) F i.
Proof. exact: (@rmeets_seq _ ord_dual). Qed.

End BJoinTheory.
End BJoinTheory.

Module Import TJoinTheory.
Section TJoinTheory.
Context {L : eqType} {ord : {tJoinOrder L}}.
Let ord_dual := [bMeetOrder of rdual_rel <=:ord].

Local Notation join := (join ord).
Local Notation "1" := (top ord).

Lemma rjoinx1 : right_zero 1 join. Proof. exact: (@rmeetx0 _ ord_dual). Qed.
Lemma rjoin1x : left_zero 1 join. Proof. exact: (@rmeet0x _ ord_dual). Qed.

Canonical join_muloid := Monoid.MulLaw rjoin1x rjoinx1.

End TJoinTheory.
End TJoinTheory.

Module Import LatticeTheory.
Section LatticeTheory.
Context {L : eqType} {ord : {lattice L}}.
Implicit Types (x y : L).

Local Notation le := (le ord).
Local Notation lt := (lt ord).
Local Notation rcomparable := (rcomparable ord).
Local Notation rmin := (rmin ord).
Local Notation rmax := (rmax ord).
Local Notation meet := (meet ord).
Local Notation join := (join ord).
Local Notation lel_xor_gt := (lel_xor_gt le lt).
Local Notation ltl_xor_ge := (ltl_xor_ge le lt).
Local Notation comparel := (comparel lt).
Local Notation incomparel := (incomparel lt rcomparable meet join).

Local Notation "x <= y" := (x <=_ord y).
Local Notation "x < y" := (x <_ord y).
Local Notation "x >= y" := (x >=_ord y) (only parsing).
Local Notation "x > y" := (x >_ord y) (only parsing).
Local Notation "x >=< y" := (rcomparable x y).
Local Notation "x `&` y" := (meet x y).
Local Notation "x `|` y" := (join x y).

Lemma rmeetUK x y : (x `&` y) `|` y = y.
Proof. by apply/eqP; rewrite req_joinr -req_meetl rmeetIK. Qed.

Lemma rmeetUKC x y : (y `&` x) `|` y = y. Proof. by rewrite rmeetC rmeetUK. Qed.
Lemma rmeetKUC y x : x `|` (y `&` x) = x. Proof. by rewrite rjoinC rmeetUK. Qed.
Lemma rmeetKU y x : x `|` (x `&` y) = x. Proof. by rewrite rmeetC rmeetKUC. Qed.

Lemma rjoinIK x y : (x `|` y) `&` y = y.
Proof. by apply/eqP; rewrite req_meetr -req_joinl rjoinUK. Qed.

Lemma rjoinIKC x y : (y `|` x) `&` y = y. Proof. by rewrite rjoinC rjoinIK. Qed.
Lemma rjoinKIC y x : x `&` (y `|` x) = x. Proof. by rewrite rmeetC rjoinIK. Qed.
Lemma rjoinKI y x : x `&` (x `|` y) = x. Proof. by rewrite rjoinC rjoinKIC. Qed.

(* comparison predicates *)

Lemma rlcomparableP x y : incomparel x y
  (rmin y x) (rmin x y) (rmax y x) (rmax x y)
  (y `&` x) (x `&` y) (y `|` x) (x `|` y)
  (y == x) (x == y) (x >= y) (x <= y) (x > y) (x < y) (y >=< x) (x >=< y).
Proof.
by case: (rcomparableP x) => [hxy|hxy|hxy|->]; do 1?have hxy' := rltW hxy;
   rewrite ?(rmeetxx, rjoinxx);
   rewrite ?(rmeet_l hxy', rmeet_r hxy', rjoin_l hxy', rjoin_r hxy');
   constructor.
Qed.

Lemma rlcomparable_ltgtP x y : x >=< y ->
  comparel x y (rmin y x) (rmin x y) (rmax y x) (rmax x y)
               (y `&` x) (x `&` y) (y `|` x) (x `|` y)
               (y == x) (x == y) (x >= y) (x <= y) (x > y) (x < y).
Proof. by case: (rlcomparableP x) => // *; constructor. Qed.

Lemma rlcomparable_leP x y : x >=< y ->
  lel_xor_gt x y (rmin y x) (rmin x y) (rmax y x) (rmax x y)
                 (y `&` x) (x `&` y) (y `|` x) (x `|` y) (x <= y) (y < x).
Proof. by case/rlcomparable_ltgtP => [/rltW xy|xy|->]; constructor. Qed.

Lemma rlcomparable_ltP x y : x >=< y ->
  ltl_xor_ge x y (rmin y x) (rmin x y) (rmax y x) (rmax x y)
                 (y `&` x) (x `&` y) (y `|` x) (x `|` y) (y <= x) (x < y).
Proof. by case/rlcomparable_ltgtP => [xy|/rltW xy|->]; constructor. Qed.

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

Lemma rmeetUl : left_distributive meet join.
Proof. by case: ord => ? ? ? ? [? []]. Qed.

Lemma rjoinIl : left_distributive join meet.
Proof. by case: ord => ? ? ? ? [? []]. Qed.

Lemma rmeetUr : right_distributive meet join.
Proof. by move=> x y z; rewrite ![x `&` _]rmeetC rmeetUl. Qed.

Lemma rjoinIr : right_distributive join meet.
Proof. by move=> x y z; rewrite ![x `|` _]rjoinC rjoinIl. Qed.

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

Canonical join_addoid := Monoid.AddLaw (@rmeetUl _ ord) (@rmeetUr _ _).

Lemma rleU2l_le y t x z : x `&` t = 0 -> x `|` y <= z `|` t -> x <= z.
Proof.
by move=> xIt0 /(rleI2 (rlexx x)); rewrite rjoinKI rmeetUr xIt0 rjoinx0 rleIidl.
Qed.

Lemma rleU2r_le y t x z : x `&` t = 0 -> y `|` x <= t `|` z -> x <= z.
Proof. by rewrite rjoinC [_ `|` z]rjoinC => /rleU2l_le H /H. Qed.

Lemma rdisjoint_lexUl z x y : x `&` z = 0 -> (x <= y `|` z) = (x <= y).
Proof.
move=> xz0; apply/idP/idP=> xy; last by rewrite rlexU2 ?xy.
by apply: (@rleU2l_le x z); rewrite ?rjoinxx.
Qed.

Lemma rdisjoint_lexUr z x y : x `&` z = 0 -> (x <= z `|` y) = (x <= y).
Proof. by move=> xz0; rewrite rjoinC; rewrite rdisjoint_lexUl. Qed.

Lemma rleU2E x y z t : x `&` t = 0 -> y `&` z = 0 ->
  (x `|` y <= z `|` t) = (x <= z) && (y <= t).
Proof.
move=> dxt dyz; apply/idP/andP; last by case=> ? ?; exact: rleU2.
by move=> lexyzt; rewrite (rleU2l_le _ lexyzt) // (rleU2r_le _ lexyzt).
Qed.

Lemma rjoins_disjoint I (d : L) (P : {pred I}) (F : I -> L) :
   (forall i : I, P i -> d `&` F i = 0) -> d `&` \big[join/0]_(i | P i) F i = 0.
Proof.
move=> d_Fi_disj; have : \big[andb/true]_(i | P i) (d `&` F i == 0).
  rewrite big_all_cond; apply/allP => i _ /=.
  by apply/implyP => /d_Fi_disj ->.
elim/big_rec2: _ => [|i y]; first by rewrite rmeetx0.
case; rewrite (andbF, andbT) // => Pi /(_ isT) dy /eqP dFi.
by rewrite rmeetUr dy dFi rjoinxx.
Qed.

End BDistrLatticeTheory.
End BDistrLatticeTheory.

Module Import TDistrLatticeTheory.
Section TDistrLatticeTheory.
Context {L : eqType} {ord : {tDistrLattice L}}.
Let ord_dual := [bDistrLattice of rdual_rel <=:ord].
Implicit Types (I : finType) (T : eqType) (x y z : L).

Local Notation meet := (meet ord).
Local Notation join := (join ord).

Local Notation "x <= y" := (x <=_ord y).
Local Notation "x `&` y" := (meet x y).
Local Notation "x `|` y" := (join x y).
Local Notation "1" := (top ord).
(* Distributive lattice theory with 1 *)

Canonical meet_addoid := Monoid.AddLaw (@rjoinIl _ ord) (@rjoinIr _ _).

Lemma rleI2l_le y t x z : y `|` z = 1 -> x `&` y <= z `&` t -> x <= z.
Proof. rewrite rjoinC; exact: (@rleU2l_le _ ord_dual). Qed.

Lemma rleI2r_le y t x z : y `|` z = 1 -> y `&` x <= t `&` z -> x <= z.
Proof. rewrite rjoinC; exact: (@rleU2r_le _ ord_dual). Qed.

Lemma rcover_leIxl z x y : z `|` y = 1 -> (x `&` z <= y) = (x <= y).
Proof. rewrite rjoinC; exact: (@rdisjoint_lexUl _ ord_dual). Qed.

Lemma rcover_leIxr z x y : z `|` y = 1 -> (z `&` x <= y) = (x <= y).
Proof. rewrite rjoinC; exact: (@rdisjoint_lexUr _ ord_dual). Qed.

Lemma rleI2E x y z t : x `|` t = 1 -> y `|` z = 1 ->
  (x `&` y <= z `&` t) = (x <= z) && (y <= t).
Proof. by move=> ? ?; apply: (@rleU2E _ ord_dual); rewrite rmeetC. Qed.

Lemma rmeets_total I (d : L) (P : {pred I}) (F : I -> L) :
   (forall i : I, P i -> d `|` F i = 1) -> d `|` \big[meet/1]_(i | P i) F i = 1.
Proof. exact: (@rjoins_disjoint _ ord_dual). Qed.

End TDistrLatticeTheory.
End TDistrLatticeTheory.

Module Import TotalTheory.
Section TotalTheory.
Context {T : eqType} {ord : {totalOrder T}}.
Implicit Types (x y z t : T) (s : seq T).

Local Notation le := (le ord).
Local Notation lt := (lt ord).
Local Notation rge := (rge ord).
Local Notation rmin := (rmin ord).
Local Notation rmax := (rmax ord).
Local Notation rarg_min := (rarg_min ord).
Local Notation rarg_max := (rarg_max ord).

Local Notation "x <= y" := (x <=_ord y).
Local Notation "x < y" := (x <_ord y).
Local Notation "x >= y" := (x >=_ord y) (only parsing).
Local Notation "x > y" := (x >_ord y) (only parsing).
Local Notation "x >=< y" := (rcomparable ord x y).
Local Notation "x < y ?<= 'if' C" := (rlteif ord x y C).
Local Notation "x `&` y" := (meet ord x y).
Local Notation "x `|` y" := (join ord x y).

Lemma le_total : total le. Proof. by case: ord => ? ? ? ? []. Qed.
Hint Resolve le_total : core.

Lemma rge_total : total rge. Proof. by move=> ? ?; apply: le_total. Qed.
Hint Resolve rge_total : core.

Lemma rcomparableT x y : x >=< y. Proof. exact: le_total. Qed.
Hint Resolve rcomparableT : core.

Lemma rleNgt x y : (x <= y) = ~~ (y < x). Proof. exact: rcomparable_leNgt. Qed.

Lemma rltNge x y : (x < y) = ~~ (y <= x). Proof. exact: rcomparable_ltNge. Qed.

Definition rltgtP x y := LatticeTheory.rlcomparable_ltgtP (rcomparableT x y).
Definition rleP x y := LatticeTheory.rlcomparable_leP (rcomparableT x y).
Definition rltP x y := LatticeTheory.rlcomparable_ltP (rcomparableT x y).

Lemma rwlog_le P :
     (forall x y, P y x -> P x y) -> (forall x y, x <= y -> P x y) ->
   forall x y, P x y.
Proof. by move=> sP hP x y; case: (rleP x y) => [| /rltW] /hP // /sP. Qed.

Lemma rwlog_lt P :
    (forall x, P x x) ->
    (forall x y, (P y x -> P x y)) -> (forall x y, x < y -> P x y) ->
  forall x y, P x y.
Proof. by move=> rP sP hP x y; case: (rltgtP x y) => [||->] // /hP // /sP. Qed.

Lemma rneq_lt x y : (x != y) = (x < y) || (y < x). Proof. by case: rltgtP. Qed.

Lemma rlt_total x y : x != y -> (x < y) || (y < x). Proof. by case: rltgtP. Qed.

Lemma req_leLR x y z t :
  (x <= y -> z <= t) -> (y < x -> t < z) -> (x <= y) = (z <= t).
Proof. by rewrite !rltNge => ? /contraTT ?; apply/idP/idP. Qed.

Lemma req_leRL x y z t :
  (x <= y -> z <= t) -> (y < x -> t < z) -> (z <= t) = (x <= y).
Proof. by move=> *; symmetry; apply: req_leLR. Qed.

Lemma req_ltLR x y z t :
  (x < y -> z < t) -> (y <= x -> t <= z) -> (x < y) = (z < t).
Proof. by rewrite !rleNgt => ? /contraTT ?; apply/idP/idP. Qed.

Lemma req_ltRL x y z t :
  (x < y -> z < t) -> (y <= x -> t <= z) -> (z < t) = (x < y).
Proof. by move=> *; symmetry; apply: req_ltLR. Qed.

Lemma rsort_le_sorted s : sorted le (sort le s).
Proof. exact: sort_sorted. Qed.
Hint Resolve rsort_le_sorted : core.

Lemma rsort_lt_sorted s : sorted lt (sort le s) = uniq s.
Proof. by rewrite rlt_sorted_uniq_le sort_uniq rsort_le_sorted andbT. Qed.

Lemma rcount_le_gt x s :
  count (fun y => y <= x) s = size s - count (fun y => y > x) s.
Proof.
rewrite -(count_predC (fun y => y > x)) addKn.
by apply: eq_count => y; rewrite /= rleNgt.
Qed.

Lemma rcount_lt_ge x s :
  count (fun y => y < x) s = size s - count (fun y => y >= x) s.
Proof.
rewrite -(count_predC (fun y => y >= x)) addKn.
by apply: eq_count => y; rewrite /= rltNge.
Qed.

Lemma rsorted_filter_gt x s :
  sorted <=:ord s -> [seq y <- s | x < y] = drop (count (le^~ x) s) s.
Proof.
move=> s_sorted; rewrite rcount_le_gt -[LHS]revK -filter_rev.
rewrite (@rsorted_filter_lt _ [totalOrder of rdual_rel <=:ord]).
  by rewrite take_rev revK count_rev.
by rewrite rev_sorted.
Qed.

Lemma rsorted_filter_ge x s :
  sorted <=:ord s -> [seq y <- s | x <= y] = drop (count (lt^~ x) s) s.
Proof.
move=> s_sorted; rewrite rcount_lt_ge -[LHS]revK -filter_rev.
rewrite (@rsorted_filter_le _ [totalOrder of rdual_rel <=:ord]).
  by rewrite take_rev revK count_rev.
by rewrite rev_sorted.
Qed.

Lemma rnth_count_ge x x0 s i : sorted <=:ord s ->
  (count (lt^~ x) s <= i < size s)%N -> x <= nth x0 s i.
Proof.
move=> ss /andP[ige ilt]; rewrite -(subnKC ige) -nth_drop -rsorted_filter_ge //.
apply/(all_nthP _ (filter_all _ _)).
by rewrite size_filter ltn_subLR // rcount_lt_ge subnK // count_size.
Qed.

Lemma rnth_count_gt x x0 s i : sorted <=:ord s ->
  (count (le^~ x) s <= i < size s)%N -> x < nth x0 s i.
Proof.
move=> ss /andP[ige ilt]; rewrite -(subnKC ige) -nth_drop -rsorted_filter_gt //.
apply/(all_nthP _ (filter_all _ _)).
by rewrite size_filter ltn_subLR // rcount_le_gt subnK // count_size.
Qed.

Lemma rnth_count_eq x x0 s i : sorted <=:ord s ->
  (count (lt^~ x) s <= i < count (le^~ x) s)%N -> nth x0 s i = x.
Proof.
move=> ss /andP[ige ilt]; apply/(@rle_anti _ ord).
by rewrite rnth_count_le// rnth_count_ge// ige (leq_trans ilt (count_size _ _)).
Qed.

(* rmax and rmin is join and meet *)

Lemma rmeetEtotal x y : x `&` y = rmin x y. Proof. by case: rleP. Qed.
Lemma rjoinEtotal x y : x `|` y = rmax x y. Proof. by case: rleP. Qed.

(* rmax and rmin theory *)

Lemma rminEgt x y : rmin x y = if x > y then y else x. Proof. by case: rltP. Qed.
Lemma rmaxEgt x y : rmax x y = if x > y then x else y. Proof. by case: rltP. Qed.
Lemma rminEge x y : rmin x y = if x >= y then y else x. Proof. by case: rleP. Qed.
Lemma rmaxEge x y : rmax x y = if x >= y then x else y. Proof. by case: rleP. Qed.

Lemma rminC : commutative rmin. Proof. by move=> x y; apply: rcomparable_minC. Qed.

Lemma rmaxC : commutative rmax. Proof. by move=> x y; apply: rcomparable_maxC. Qed.

Lemma rminA : associative rmin.
Proof. by move=> x y z; apply: rcomparable_minA. Qed.

Lemma rmaxA : associative rmax.
Proof. by move=> x y z; apply: rcomparable_maxA. Qed.

Lemma rminAC : right_commutative rmin.
Proof. by move=> x y z; apply: rcomparable_minAC. Qed.

Lemma rmaxAC : right_commutative rmax.
Proof. by move=> x y z; apply: rcomparable_maxAC. Qed.

Lemma rminCA : left_commutative rmin.
Proof. by move=> x y z; apply: rcomparable_minCA. Qed.

Lemma rmaxCA : left_commutative rmax.
Proof. by move=> x y z; apply: rcomparable_maxCA. Qed.

Lemma rminACA : interchange rmin rmin.
Proof. by move=> x y z t; apply: rcomparable_minACA. Qed.

Lemma rmaxACA : interchange rmax rmax.
Proof. by move=> x y z t; apply: rcomparable_maxACA. Qed.

Lemma req_minr x y : (rmin x y == y) = (y <= x).
Proof. exact: rcomparable_eq_minr. Qed.

Lemma req_maxl x y : (rmax x y == x) = (y <= x).
Proof. exact: rcomparable_eq_maxl. Qed.

Lemma rmin_idPr x y : reflect (rmin x y = y) (y <= x).
Proof. exact: rcomparable_min_idPr. Qed.

Lemma rmax_idPl x y : reflect (rmax x y = x) (y <= x).
Proof. exact: rcomparable_max_idPl. Qed.

Lemma rle_minr z x y : (z <= rmin x y) = (z <= x) && (z <= y).
Proof. exact: rcomparable_le_minr. Qed.

Lemma rle_minl z x y : (rmin x y <= z) = (x <= z) || (y <= z).
Proof. exact: rcomparable_le_minl. Qed.

Lemma rlt_minr z x y : (z < rmin x y) = (z < x) && (z < y).
Proof. exact: rcomparable_lt_minr. Qed.

Lemma rlt_minl z x y : (rmin x y < z) = (x < z) || (y < z).
Proof. exact: rcomparable_lt_minl. Qed.

Lemma rle_maxr z x y : (z <= rmax x y) = (z <= x) || (z <= y).
Proof. exact: rcomparable_le_maxr. Qed.

Lemma rle_maxl z x y : (rmax x y <= z) = (x <= z) && (y <= z).
Proof. exact: rcomparable_le_maxl. Qed.

Lemma rlt_maxr z x y : (z < rmax x y) = (z < x) || (z < y).
Proof. exact: rcomparable_lt_maxr. Qed.

Lemma rlt_maxl z x y : (rmax x y < z) = (x < z) && (y < z).
Proof. exact: rcomparable_lt_maxl. Qed.

Lemma rminxK x y : rmax (rmin x y) y = y. Proof. exact: rcomparable_minxK. Qed.
Lemma rminKx x y : rmax x (rmin x y) = x. Proof. exact: rcomparable_minKx. Qed.
Lemma rmaxxK x y : rmin (rmax x y) y = y. Proof. exact: rcomparable_maxxK. Qed.
Lemma rmaxKx x y : rmin x (rmax x y) = x. Proof. exact: rcomparable_maxKx. Qed.

Lemma rmax_minl : left_distributive rmax rmin.
Proof. by move=> x y z; apply: rcomparable_max_minl. Qed.

Lemma rmin_maxl : left_distributive rmin rmax.
Proof. by move=> x y z; apply: rcomparable_min_maxl. Qed.

Lemma rmax_minr : right_distributive rmax rmin.
Proof. by move=> x y z; apply: rcomparable_max_minr. Qed.

Lemma rmin_maxr : right_distributive rmin rmax.
Proof. by move=> x y z; apply: rcomparable_min_maxr. Qed.

Lemma rleIx x y z : (y `&` z <= x) = (y <= x) || (z <= x).
Proof. by rewrite rmeetEtotal rle_minl. Qed.

Lemma rlexU x y z : (x <= y `|` z) = (x <= y) || (x <= z).
Proof. by rewrite rjoinEtotal rle_maxr. Qed.

Lemma rltxI x y z : (x < y `&` z) = (x < y) && (x < z).
Proof. by rewrite !rltNge rleIx negb_or. Qed.

Lemma rltIx x y z : (y `&` z < x) = (y < x) || (z < x).
Proof. by rewrite !rltNge rlexI negb_and. Qed.

Lemma rltxU x y z : (x < y `|` z) = (x < y) || (x < z).
Proof. by rewrite !rltNge rleUx negb_and. Qed.

Lemma rltUx x y z : (y `|` z < x) = (y < x) && (z < x).
Proof. by rewrite !rltNge rlexU negb_or. Qed.

Definition rltexI := (@rlexI _ ord, rltxI).
Definition rlteIx := (rleIx, rltIx).
Definition rltexU := (rlexU, rltxU).
Definition rlteUx := (@rleUx _ ord, rltUx).

(* rlteif *)

Lemma rlteifNE x y C : x < y ?<= if ~~ C = ~~ (y < x ?<= if C).
Proof. by case: C => /=; case: rleP. Qed.

Lemma rlteif_minr z x y C :
  (z < rmin x y ?<= if C) = (z < x ?<= if C) && (z < y ?<= if C).
Proof. by case: C; rewrite /= (rle_minr, rlt_minr). Qed.

Lemma rlteif_minl z x y C :
  (rmin x y < z ?<= if C) = (x < z ?<= if C) || (y < z ?<= if C).
Proof. by case: C; rewrite /= (rle_minl, rlt_minl). Qed.

Lemma rlteif_maxr z x y C :
  (z < rmax x y ?<= if C) = (z < x ?<= if C) || (z < y ?<= if C).
Proof. by case: C; rewrite /= (rle_maxr, rlt_maxr). Qed.

Lemma rlteif_maxl z x y C :
  (rmax x y < z ?<= if C) = (x < z ?<= if C) && (y < z ?<= if C).
Proof. by case: C; rewrite /= (rle_maxl, rlt_maxl). Qed.

Section ArgExtremum.

Context (I : finType) (i0 : I) (P : {pred I}) (F : I -> T) (Pi0 : P i0).

Lemma arg_minP: extremum_spec le P F (rarg_min i0 P F).
Proof. by apply: extremumP => //; apply: rle_trans. Qed.

Lemma arg_maxP: extremum_spec rge P F (rarg_max i0 P F).
Proof. by apply: extremumP => //; [apply: rge_refl | apply: rge_trans]. Qed.

End ArgExtremum.

End TotalTheory.

#[global] Hint Resolve le_total : core.
#[global] Hint Resolve rge_total : core.
#[global] Hint Resolve rcomparableT : core.
#[global] Hint Resolve rsort_le_sorted : core.

Arguments rmin_idPr {T ord x y}.
Arguments rmax_idPl {T ord x y}.

(* contra lemmas *)

Section ContraTheory.

Context {T1 T2 : eqType} {ord1 : {pOrder T1}} {ord2 : {totalOrder T2}}.
Implicit Types (x y : T1) (z t : T2) (b : bool) (m n : nat) (P : Prop).

Local Notation "x <= y" := (x <=_ord2 y).
Local Notation "x < y" := (x <_ord2 y).

Lemma rcontraTle b z t : (t < z -> ~~ b) -> (b -> z <= t).
Proof. exact: rcomparable_contraTle. Qed.

Lemma rcontraTlt b z t : (t <= z -> ~~ b) -> (b -> z < t).
Proof. exact: rcomparable_contraTlt. Qed.

Lemma rcontraPle P z t : (t < z -> ~ P) -> (P -> z <= t).
Proof. exact: rcomparable_contraPle. Qed.

Lemma rcontraPlt P z t : (t <= z -> ~ P) -> (P -> z < t).
Proof. exact: rcomparable_contraPlt. Qed.

Lemma rcontraNle b z t : (t < z -> b) -> (~~ b -> z <= t).
Proof. exact: rcomparable_contraNle. Qed.

Lemma rcontraNlt b z t : (t <= z -> b) -> (~~ b -> z < t).
Proof. exact: rcomparable_contraNlt. Qed.

Lemma rcontra_not_le P z t : (t < z -> P) -> (~ P -> z <= t).
Proof. exact: rcomparable_contra_not_le. Qed.

Lemma rcontra_not_lt P z t : (t <= z -> P) -> (~ P -> z < t).
Proof. exact: rcomparable_contra_not_lt. Qed.

Lemma rcontraFle b z t : (t < z -> b) -> (b = false -> z <= t).
Proof. exact: rcomparable_contraFle. Qed.

Lemma rcontraFlt b z t : (t <= z -> b) -> (b = false -> z < t).
Proof. exact: rcomparable_contraFlt. Qed.

Lemma rcontra_leq_le m n z t : (t < z -> (n < m)%N) -> ((m <= n)%N -> z <= t).
Proof. exact: rcomparable_contra_leq_le. Qed.

Lemma rcontra_leq_lt m n z t : (t <= z -> (n < m)%N) -> ((m <= n)%N -> z < t).
Proof. exact: rcomparable_contra_leq_lt. Qed.

Lemma rcontra_ltn_le m n z t : (t < z -> (n <= m)%N) -> ((m < n)%N -> z <= t).
Proof. exact: rcomparable_contra_ltn_le. Qed.

Lemma rcontra_ltn_lt m n z t : (t <= z -> (n <= m)%N) -> ((m < n)%N -> z < t).
Proof. exact: rcomparable_contra_ltn_lt. Qed.

Lemma rcontra_le x y z t : (t < z -> y <_ord1 x) -> (x <=_ord1 y -> z <= t).
Proof. exact: rcomparable_contra_le. Qed.

Lemma rcontra_le_lt x y z t : (t <= z -> y <_ord1 x) -> (x <=_ord1 y -> z < t).
Proof. exact: rcomparable_contra_le_lt. Qed.

Lemma rcontra_lt_le x y z t : (t < z -> y <=_ord1 x) -> (x <_ord1 y -> z <= t).
Proof. exact: rcomparable_contra_lt_le. Qed.

Lemma rcontra_lt x y z t : (t <= z -> y <=_ord1 x) -> (x <_ord1 y -> z < t).
Proof. exact: rcomparable_contra_lt. Qed.

End ContraTheory.

Section TotalMonotonyTheory.

Context {T T' : eqType} {ord : {totalOrder T}} {ord' : {pOrder T'}}.
Variables (D : {pred T}) (f : T -> T').

Let leT'_anti   := @rle_anti _ ord'.
Let ltT_neqAle  := @rlt_neqAle _ ord.
Let ltT'_neqAle := @rlt_neqAle _ ord'.
Let ltT_def     := @rlt_def _ ord.
Let leT_total   := @le_total _ ord.

Lemma rle_mono : {homo f : x y / x <_ord y >-> x <_ord' y} ->
                {mono f : x y / x <=_ord y >-> x <=_ord' y}.
Proof. exact: total_homo_mono. Qed.

Lemma rle_nmono : {homo f : x y / y <_ord x >-> x <_ord' y} ->
                 {mono f : x y / y <=_ord x >-> x <=_ord' y}.
Proof. exact: total_homo_mono. Qed.

Lemma rle_mono_in : {in D &, {homo f : x y / x <_ord y >-> x <_ord' y}} ->
                   {in D &, {mono f : x y / x <=_ord y >-> x <=_ord' y}}.
Proof. exact: total_homo_mono_in. Qed.

Lemma rle_nmono_in : {in D &, {homo f : x y / y <_ord x >-> x <_ord' y}} ->
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
  rlt_def   : forall x y, lt x y = (y != x) && (le x y);
  rlexx     : reflexive     le;
  rle_anti  : antisymmetric le;
  rle_trans : transitive    le;
}.

Variable (m : of_).

Lemma rlt_def' (x y : T) : lt m y x = (y != x) && le m y x.
Proof. by rewrite (rlt_def m) eq_sym. Qed.

Lemma rle_anti' x y : le m x y -> le m y x -> x = y.
Proof. by move=> xy yx; apply/(@rle_anti m)/andP. Qed.

Definition porderMixin :=
  POrder.Mixin (rlt_def m) rlt_def' (rlexx m) rle_anti' (@rle_trans m).

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
  rle0x : forall x, bottom <=_ord x;
}.

Definition bPOrderMixin (m : of_) : BPOrder.mixin_of ord (bottom m) := rle0x m.

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
  rlex1 : forall x, x <=_ord top;
}.

Definition tPOrderMixin (m : of_) : TPOrder.mixin_of ord (top m) := rlex1 m.

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
  rmeetC   : commutative meet;
  rmeetA   : associative meet;
  rleEmeet : forall x y, (x <=_ord y) = (meet x y == x);
}.

Definition meetMixin (m : of_) : Meet.mixin_of ord (meet m) :=
  Meet.Mixin (rmeetC m) (rmeetA m) (rleEmeet m).

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
  rjoinC   : commutative join;
  rjoinA   : associative join;
  rleEjoin : forall x y, (y <=_ord x) = (join x y == x);
}.

Definition joinMixin (m : of_) : Join.mixin_of ord (join m) :=
  @Meet.Mixin _ (dual_pOrder ord) _ (rjoinC m) (rjoinA m) (rleEjoin m).

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

Record of_ := Build { rmeetUl : left_distributive (meet ord) (join ord) }.

Variable (m : of_).

Lemma rmeetUr : right_distributive (meet ord) (join ord).
Proof. by move=> x y z; rewrite ![meet _ x _]rmeetC rmeetUl. Qed.

Lemma rjoinIl : left_distributive (join ord) (meet ord).
Proof. by move=> x y z; rewrite rmeetUr rjoinIK rmeetUl // -rjoinA rmeetUKC. Qed.

Definition distrLatticeMixin := DistrLattice.Mixin (rmeetUl m) rjoinIl.

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
  rmeetC : commutative meet;
  rjoinC : commutative join;
  rmeetA : associative meet;
  rjoinA : associative join;
  rjoinKI : forall y x, meet x (join x y) = x;
  rmeetKU : forall y x, join x (meet x y) = x;
  rleEmeet : forall x y, (x <=_ord y) = (meet x y == x);
}.

Variable (m : of_).

Definition meetMixin := MeetRelMixin (rmeetC m) (rmeetA m) (rleEmeet m).

Lemma rleEjoin x y : (y <=_ord x) = (join m x y == x).
Proof.
rewrite (rleEmeet m); apply/eqP/eqP => <-.
  by rewrite rmeetC // rmeetKU.
by rewrite rjoinC // rjoinKI.
Qed.

Definition joinMixin := JoinRelMixin (rjoinC m) (rjoinA m) rleEjoin.

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
  rmeetC : commutative meet;
  rjoinC : commutative join;
  rmeetA : associative meet;
  rjoinA : associative join;
  rjoinKI : forall y x, meet x (join x y) = x;
  rmeetKU : forall y x, join x (meet x y) = x;
  rleEmeet : forall x y, (x <=_ord y) = (meet x y == x);
  rmeetUl : left_distributive meet join;
}.

Variable (m : of_).

Definition latticeMixin : latticePOrderRelMixin ord :=
  LatticePOrderRelMixin
    (rmeetC m) (rjoinC m) (rmeetA m) (rjoinA m) (rjoinKI m) (rmeetKU m) (rleEmeet m).

Definition distrLatticeMixin :=
  @DistrLatticeRelMixin _ (LatticeOfPOrder latticeMixin) (rmeetUl m).

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

Let rcomparableT x y : x >=<_ord y := m x y.

Fact rmeetUl : left_distributive (meet ord) (join ord).
Proof.
pose rleP x y := rlcomparable_leP (rcomparableT x y).
move=> x y z; case: (rleP x z); case: (rleP y z); case: (rleP x y);
  case: (rleP x z); case: (rleP y z); case: (rleP x y) => //= xy yz xz _ _ _;
  rewrite ?rjoinxx //.
- by move: (rle_lt_trans xz (rlt_trans yz xy)); rewrite rltxx.
- by move: (rlt_le_trans xz (rle_trans xy yz)); rewrite rltxx.
Qed.

Definition distrLatticeMixin := DistrLatticeRelMixin rmeetUl.

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

Let meet := rmin ord.
Let join := rmax ord.

Let rcomparableT x y : x >=<_ord y := m x y.

Fact rmeetC : commutative meet. Proof. by move=> *; apply: rcomparable_minC. Qed.
Fact rjoinC : commutative join. Proof. by move=> *; apply: rcomparable_maxC. Qed.
Fact rmeetA : associative meet. Proof. by move=> *; apply: rcomparable_minA. Qed.
Fact rjoinA : associative join. Proof. by move=> *; apply: rcomparable_maxA. Qed.
Fact rjoinKI y x : meet x (join x y) = x. Proof. exact: rcomparable_maxKx. Qed.
Fact rmeetKU y x : join x (meet x y) = x. Proof. exact: rcomparable_minKx. Qed.

Fact rleEmeet x y : (x <=_ord y) = (meet x y == x).
Proof. by rewrite req_minl. Qed.

Definition latticeMixin : latticePOrderRelMixin ord :=
  LatticePOrderRelMixin rmeetC rjoinC rmeetA rjoinA rjoinKI rmeetKU rleEmeet.

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
  rle_def   : forall x y, le x y = (x == y) || lt x y;
  lt_irr   : irreflexive lt;
  rlt_trans : transitive lt;
}.

Variable (m : of_).

Fact rlt_asym x y : (lt m x y && lt m y x) = false.
Proof. by apply/negP => /andP [] xy /(rlt_trans xy); rewrite (lt_irr m x). Qed.

Fact rlt_def x y : lt m x y = (y != x) && le m x y.
Proof. by rewrite rle_def //; case: eqVneq => //= ->; rewrite lt_irr. Qed.

Fact rle_refl : reflexive (le m).
Proof. by move=> ?; rewrite rle_def // eqxx. Qed.

Fact rle_anti : antisymmetric (le m).
Proof.
by move=> ? ?; rewrite !rle_def // eq_sym -orb_andr rlt_asym; case: eqP.
Qed.

Fact rle_trans : transitive (le m).
Proof.
by move=> y x z; rewrite !rle_def // => /predU1P [-> //|ltxy] /predU1P [<-|ltyz];
  rewrite ?ltxy ?(rlt_trans ltxy ltyz) ?orbT.
Qed.

Definition porderMixin : lePOrderMixin T :=
  LePOrderMixin rlt_def rle_refl rle_anti rle_trans.

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
  rle_def : forall x y : T, le x y = (meet x y == x);
  rlt_def : forall x y : T, lt x y = (y != x) && le x y;
  rmeetC : commutative meet;
  rjoinC : commutative join;
  rmeetA : associative meet;
  rjoinA : associative join;
  rjoinKI : forall y x : T, meet x (join x y) = x;
  rmeetKU : forall y x : T, join x (meet x y) = x;
  rmeetxx : idempotent meet;
}.

Variable (m : of_).

Fact rle_refl : reflexive (le m).
Proof. by move=> x; rewrite rle_def ?rmeetxx. Qed.

Fact rle_anti : antisymmetric (le m).
Proof. by move=> x y; rewrite !rle_def // rmeetC // => /andP [] /eqP -> /eqP. Qed.

Fact rle_trans : transitive (le m).
Proof.
move=> y x z; rewrite !rle_def // => /eqP lexy /eqP leyz; apply/eqP.
by rewrite -[in LHS]lexy -rmeetA // leyz.
Qed.

Definition porderMixin : lePOrderMixin T :=
  LePOrderMixin (rlt_def m) rle_refl rle_anti rle_trans.

Definition latticeMixin :
  latticePOrderRelMixin (POrder (le m) (lt m) porderMixin) :=
  @LatticePOrderRelMixin
    _ (POrder (le m) (lt m) porderMixin) (meet m) (join m)
    (rmeetC m) (rjoinC m) (rmeetA m) (rjoinA m) (rjoinKI m) (rmeetKU m) (rle_def m).

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
  rle_def : forall x y : T, le x y = (meet x y == x);
  rlt_def : forall x y : T, lt x y = (y != x) && le x y;
  rmeetC : commutative meet;
  rjoinC : commutative join;
  rmeetA : associative meet;
  rjoinA : associative join;
  rjoinKI : forall y x : T, meet x (join x y) = x;
  rmeetKU : forall y x : T, join x (meet x y) = x;
  rmeetUl : left_distributive meet join;
  rmeetxx : idempotent meet;
}.

Variable (m : of_).

Definition latticeMixin : meetJoinMixin T :=
  MeetJoinMixin (rle_def m) (rlt_def m) (rmeetC m) (rjoinC m) (rmeetA m) (rjoinA m)
                (rjoinKI m) (rmeetKU m) (rmeetxx m).

Let le_lattice := LatticeOfPOrder latticeMixin.

Definition distrLatticeMixin : distrLatticeRelMixin le_lattice :=
  @DistrLatticeRelMixin _ le_lattice (rmeetUl m).

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
  rlt_def : forall x y, lt x y = (y != x) && le x y;
  meet_def : forall x y, meet x y = if lt x y then x else y;
  join_def : forall x y, join x y = if lt x y then y else x;
  rle_anti : antisymmetric le;
  rle_trans : transitive le;
  le_total : total le;
}.

Variables (m : of_).

Fact rle_refl : reflexive (le m).
Proof. by move=> x; case: (le m x x) (le_total m x x). Qed.

Definition porderMixin :=
  LePOrderMixin (rlt_def m) rle_refl (@rle_anti m) (@rle_trans m).

Let le_order :=
  OrderOfLattice
    (le_total m : totalPOrderRelMixin (POrder (le m) (lt m) porderMixin)).

Let meetE x y : meet m x y = RelOrder.meet le_order x y := meet_def m x y.
Let joinE x y : join m x y = RelOrder.join le_order x y := join_def m x y.

Fact rmeetC : commutative (meet m).
Proof. by move=> *; rewrite !meetE rmeetC. Qed.

Fact rjoinC : commutative (join m).
Proof. by move=> *; rewrite !joinE rjoinC. Qed.

Fact rmeetA : associative (meet m).
Proof. by move=> *; rewrite !meetE rmeetA. Qed.

Fact rjoinA : associative (join m).
Proof. by move=> *; rewrite !joinE rjoinA. Qed.

Fact rjoinKI y x : meet m x (join m x y) = x.
Proof. by rewrite meetE joinE rjoinKI. Qed.

Fact rmeetKU y x : join m x (meet m x y) = x.
Proof. by rewrite meetE joinE rmeetKU. Qed.

Fact rmeetxx : idempotent (meet m).
Proof. by move=> *; rewrite meetE rmeetxx. Qed.

Fact rle_def x y : le m x y = (meet m x y == x).
Proof. by rewrite meetE req_meetl. Qed.

Definition latticeMixin : meetJoinMixin T :=
  MeetJoinMixin
    rle_def (rlt_def m) rmeetC rjoinC rmeetA rjoinA rjoinKI rmeetKU rmeetxx.

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
  rle_def   : forall x y, le x y = (x == y) || lt x y;
  meet_def : forall x y, meet x y = if lt x y then x else y;
  join_def : forall x y, join x y = if lt x y then y else x;
  lt_irr   : irreflexive lt;
  rlt_trans : transitive lt;
  rlt_total : forall x y, x != y -> lt x y || lt y x;
}.

Variables (m : of_).

Fact rlt_def x y : lt m x y = (y != x) && le m x y.
Proof. by rewrite rle_def //; case: eqVneq => //= ->; rewrite lt_irr. Qed.

Fact rmeet_def_le x y : meet m x y = if lt m x y then x else y.
Proof. by rewrite meet_def // rlt_def; case: eqP. Qed.

Fact rjoin_def_le x y : join m x y = if lt m x y then y else x.
Proof. by rewrite join_def // rlt_def; case: eqP. Qed.

Fact rle_anti : antisymmetric (le m).
Proof.
move=> x y; rewrite !rle_def //.
by case: eqVneq => //= _ /andP [] hxy /(rlt_trans hxy); rewrite lt_irr.
Qed.

Fact rle_trans : transitive (le m).
Proof.
move=> y x z; rewrite !rle_def //; case: eqVneq => [->|_] //=.
by case: eqVneq => [-> ->|_ hxy /(rlt_trans hxy) ->]; rewrite orbT.
Qed.

Fact le_total : total (le m).
Proof.
by move=> x y; rewrite !rle_def //; case: eqVneq => //=; exact: rlt_total.
Qed.

Definition orderMixin : leOrderMixin T :=
  LeOrderMixin rlt_def rmeet_def_le rjoin_def_le rle_anti rle_trans le_total.

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

Lemma rltn_def x y : (x < y)%N = (y != x)%N && (x <= y)%N.
Proof. by case: ltngtP. Qed.

Definition nat_pOrderMixin := LePOrderMixin rltn_def leqnn anti_leq leq_trans.

Local Canonical nat_pOrder := POrder leq ltn nat_pOrderMixin.
(* BUG, TODO: the packager [BPOrder] can infer the [pOrder] instance only     *)
(* from the symbol [leq]. If [leq] is replaced with [unkeyed leq] above, the  *)
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
Export RelOrder.DualOrder.Exports.
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
