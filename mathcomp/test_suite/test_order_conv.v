From mathcomp Require Import all_ssreflect.
Import Order.Theory.

Notation "ord ^~" := (dual_pOrder ord) (at level 8, format "ord ^~").

Module DualOrderTest.
Section DualOrderTest.
Variable (T : eqType) (ord : {pOrder T}).

Lemma le_dual_inv x y: x <=_((ord^~)^~) y = x <=_ord y.
Proof. by []. Qed.

Lemma lt_dual_inv x y: x <_((ord^~)^~) y = x <_ord y.
Proof. by []. Qed.

Goal ord = (ord^~)^~.
Proof. by []. Qed.

Goal [leo: (dual_rel <=:ord)] = ord^~.
Proof. by []. Qed.

Goal [lto: (dual_rel <:ord)] = ord^~.
Proof. by []. Qed.

Goal forall x y, x <_ord y -> y <_(ord^~) x.
Proof. by []. Qed.

Goal forall x y, x <=_ord y = y <=_(ord^~) x.
Proof. by []. Qed.

End DualOrderTest.
End DualOrderTest.

(*Section DualMeetJoinTest.

End BJoinTheory.

(* ==================================================================== *)
Context {T: eqType}. (*(M : {meetSemiLattice T}) (J : {joinSemiLattice T}).*)
Axiom dualK: forall r : {porder T}, r^~^~ = r.
Context (M : {meetSemiLattice T}) (J : {joinSemiLattice T}).
Goal M^~^~= M.
by rewrite dualK.
Qed.


Check @Meet.clone _ (Phant _) M _ id.
Check @Join.clone _ (Phant _) M^~ _ id.
Check @Meet.clone _ (Phant _) (M^~)^~ _ id.
Set Printing All.
Goal M = @Meet.clone _ (Phant _) (M^~)^~ _ id.
reflexivity.
Qed.
(*Goal M = (M^~)^~ :> { meetSemiLattice T}.*)
(*Check (M^~)^~ : { meetSemiLattice T}.*)
Set Printing All.
Fail Check erefl J : ((J^~j)^~m) = J.

End DualMeetJoinTest.*)

Section dual_of_dual.
Variable (disp : unit).

Let eq_dual_dual_porderType (T : porderType disp) :=
  erefl _ : Order.POrder.class T = Order.POrder.class [porderType of T^d^d].

Let eq_dual_dual_bPOrderType (T : bPOrderType disp) :=
  erefl _ : Order.BPOrder.class T = Order.BPOrder.class [bPOrderType of T^d^d].

Let eq_dual_dual_tPOrderType (T : tPOrderType disp) :=
  erefl _ : Order.TPOrder.class T = Order.TPOrder.class [tPOrderType of T^d^d].

Let eq_dual_dual_tbPOrderType (T : tbPOrderType disp) :=
  erefl _ : Order.TBPOrder.class T =
            Order.TBPOrder.class [tbPOrderType of T^d^d].

Let eq_dual_dual_meetSemilatticeType (T : meetSemilatticeType disp) :=
  erefl _ : Order.MeetSemilattice.class T =
            Order.MeetSemilattice.class [meetSemilatticeType of T^d^d].

Let eq_dual_dual_bMeetSemilatticeType (T : bMeetSemilatticeType disp) :=
  erefl _ : Order.BMeetSemilattice.class T =
            Order.BMeetSemilattice.class [bMeetSemilatticeType of T^d^d].

Let eq_dual_dual_tMeetSemilatticeType (T : tMeetSemilatticeType disp) :=
  erefl _ : Order.TMeetSemilattice.class T =
            Order.TMeetSemilattice.class [tMeetSemilatticeType of T^d^d].

Let eq_dual_dual_tbMeetSemilatticeType (T : tbMeetSemilatticeType disp) :=
  erefl _ : Order.TBMeetSemilattice.class T =
            Order.TBMeetSemilattice.class [tbMeetSemilatticeType of T^d^d].

Let eq_dual_dual_joinSemilatticeType (T : joinSemilatticeType disp) :=
  erefl _ : Order.JoinSemilattice.class T =
            Order.JoinSemilattice.class [joinSemilatticeType of T^d^d].

Let eq_dual_dual_bJoinSemilatticeType (T : bJoinSemilatticeType disp) :=
  erefl _ : Order.BJoinSemilattice.class T =
            Order.BJoinSemilattice.class [bJoinSemilatticeType of T^d^d].

Let eq_dual_dual_tJoinSemilatticeType (T : tJoinSemilatticeType disp) :=
  erefl _ : Order.TJoinSemilattice.class T =
            Order.TJoinSemilattice.class [tJoinSemilatticeType of T^d^d].

Let eq_dual_dual_tbJoinSemilatticeType (T : tbJoinSemilatticeType disp) :=
  erefl _ : Order.TBJoinSemilattice.class T =
            Order.TBJoinSemilattice.class [tbJoinSemilatticeType of T^d^d].

Let eq_dual_dual_latticeType (T : latticeType disp) :=
  erefl _ : Order.Lattice.class T = Order.Lattice.class [latticeType of T^d^d].

Let eq_dual_dual_bLatticeType (T : bLatticeType disp) :=
  erefl _ : Order.BLattice.class T =
            Order.BLattice.class [bLatticeType of T^d^d].

Let eq_dual_dual_tLatticeType (T : tLatticeType disp) :=
  erefl _ : Order.TLattice.class T =
            Order.TLattice.class [tLatticeType of T^d^d].

Let eq_dual_dual_tbLatticeType (T : tbLatticeType disp) :=
  erefl _ : Order.TBLattice.class T =
            Order.TBLattice.class [tbLatticeType of T^d^d].

Let eq_dual_dual_distrLatticeType (T : distrLatticeType disp) :=
  erefl _ : Order.DistrLattice.class T =
            Order.DistrLattice.class [distrLatticeType of T^d^d].

Let eq_dual_dual_bDistrLatticeType (T : bDistrLatticeType disp) :=
  erefl _ : Order.BDistrLattice.class T =
            Order.BDistrLattice.class [bDistrLatticeType of T^d^d].

Let eq_dual_dual_tDistrLatticeType (T : tDistrLatticeType disp) :=
  erefl _ : Order.TDistrLattice.class T =
            Order.TDistrLattice.class [tDistrLatticeType of T^d^d].

Let eq_dual_dual_tbDistrLatticeType (T : tbDistrLatticeType disp) :=
  erefl _ : Order.TBDistrLattice.class T =
            Order.TBDistrLattice.class [tbDistrLatticeType of T^d^d].

Let eq_dual_dual_orderType (T : orderType disp) :=
  erefl _ : Order.Total.class T = Order.Total.class [orderType of T^d^d].

Let eq_dual_dual_bOrderType (T : bOrderType disp) :=
  erefl _ : Order.BTotal.class T = Order.BTotal.class [bOrderType of T^d^d].

Let eq_dual_dual_tOrderType (T : tOrderType disp) :=
  erefl _ : Order.TTotal.class T = Order.TTotal.class [tOrderType of T^d^d].

Let eq_dual_dual_tbOrderType (T : tbOrderType disp) :=
  erefl _ : Order.TBTotal.class T = Order.TBTotal.class [tbOrderType of T^d^d].

Let eq_dual_dual_finPOrderType (T : finPOrderType disp) :=
  erefl _ : Order.FinPOrder.class T =
            Order.FinPOrder.class [finPOrderType of T^d^d].

Let eq_dual_dual_finBPOrderType (T : finBPOrderType disp) :=
  erefl _ : Order.FinBPOrder.class T =
            Order.FinBPOrder.class [finBPOrderType of T^d^d].

Let eq_dual_dual_finTPOrderType (T : finTPOrderType disp) :=
  erefl _ : Order.FinTPOrder.class T =
            Order.FinTPOrder.class [finTPOrderType of T^d^d].

Let eq_dual_dual_finTBPOrderType (T : finTBPOrderType disp) :=
  erefl _ : Order.FinTBPOrder.class T =
            Order.FinTBPOrder.class [finTBPOrderType of T^d^d].

Let eq_dual_dual_finMeetSemilatticeType (T : finMeetSemilatticeType disp) :=
  erefl _ : Order.FinMeetSemilattice.class T =
            Order.FinMeetSemilattice.class [finMeetSemilatticeType of T^d^d].

Let eq_dual_dual_finBMeetSemilatticeType (T : finBMeetSemilatticeType disp) :=
  erefl _ : Order.BMeetSemilattice.class T =
            Order.BMeetSemilattice.class [finBMeetSemilatticeType of T^d^d].

Let eq_dual_dual_finJoinSemilatticeType (T : finJoinSemilatticeType disp) :=
  erefl _ : Order.FinJoinSemilattice.class T =
            Order.FinJoinSemilattice.class [finJoinSemilatticeType of T^d^d].

Let eq_dual_dual_finTJoinSemilatticeType (T : finTJoinSemilatticeType disp) :=
  erefl _ : Order.TJoinSemilattice.class T =
            Order.TJoinSemilattice.class [finTJoinSemilatticeType of T^d^d].

Let eq_dual_dual_FinLatticeType (T : finLatticeType disp) :=
  erefl _ : Order.FinLattice.class T =
            Order.FinLattice.class [finLatticeType of T^d^d].

Let eq_dual_dual_FinTBLatticeType (T : finTBLatticeType disp) :=
  erefl _ : Order.FinTBLattice.class T =
            Order.FinTBLattice.class [finTBLatticeType of T^d^d].

Let eq_dual_dual_finDistrLatticeType (T : finDistrLatticeType disp) :=
  erefl _ : Order.FinDistrLattice.class T =
            Order.FinDistrLattice.class [finDistrLatticeType of T^d^d].

Let eq_dual_dual_finTBDistrLatticeType (T : finTBDistrLatticeType disp) :=
  erefl _ : Order.FinTBDistrLattice.class T =
            Order.FinTBDistrLattice.class [finTBDistrLatticeType of T^d^d].

Let eq_dual_dual_finOrderType (T : finOrderType disp) :=
  erefl _ : Order.FinTotal.class T =
            Order.FinTotal.class [finOrderType of T^d^d].

Let eq_dual_dual_finTBOrderType (T : finTBOrderType disp) :=
  erefl _ : Order.FinTBTotal.class T =
            Order.FinTBTotal.class [finTBOrderType of T^d^d].

End dual_of_dual.
