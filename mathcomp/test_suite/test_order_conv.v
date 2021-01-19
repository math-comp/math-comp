From mathcomp Require Import all_ssreflect.
Import Order.Theory.

Section relorder.
Variable (T : eqType).

Let eq_dual_dual_pOrder (ord : {pOrder T}) :
  RelOrder.dual_pOrder (RelOrder.dual_pOrder ord) = ord := erefl.

Let eq_dual_dual_bPOrder (ord : {bPOrder T}) :
  RelOrder.dual_bPOrder (RelOrder.dual_tPOrder ord) = ord := erefl.

Let eq_dual_dual_tPOrder (ord : {tPOrder T}) :
  RelOrder.dual_tPOrder (RelOrder.dual_bPOrder ord) = ord := erefl.

Let eq_dual_dual_tbPOrder (ord : {tbPOrder T}) :
  RelOrder.dual_tbPOrder (RelOrder.dual_tbPOrder ord) = ord := erefl.

Let eq_dual_dual_meetOrder (ord : {meetOrder T}) :
  RelOrder.dual_meetOrder (RelOrder.dual_joinOrder ord) = ord := erefl.

Let eq_dual_dual_bMeetOrder (ord : {bMeetOrder T}) :
  RelOrder.dual_bMeetOrder (RelOrder.dual_tJoinOrder ord) = ord := erefl.

Let eq_dual_dual_tMeetOrder (ord : {tMeetOrder T}) :
  RelOrder.dual_tMeetOrder (RelOrder.dual_bJoinOrder ord) = ord := erefl.

Let eq_dual_dual_tbMeetOrder (ord : {tbMeetOrder T}) :
  RelOrder.dual_tbMeetOrder (RelOrder.dual_tbJoinOrder ord) = ord := erefl.

Let eq_dual_dual_joinOrder (ord : {joinOrder T}) :
  RelOrder.dual_joinOrder (RelOrder.dual_meetOrder ord) = ord := erefl.

Let eq_dual_dual_bJoinOrder (ord : {bJoinOrder T}) :
  RelOrder.dual_bJoinOrder (RelOrder.dual_tMeetOrder ord) = ord := erefl.

Let eq_dual_dual_tJoinOrder (ord : {tJoinOrder T}) :
  RelOrder.dual_tJoinOrder (RelOrder.dual_bMeetOrder ord) = ord := erefl.

Let eq_dual_dual_tbJoinOrder (ord : {tbJoinOrder T}) :
  RelOrder.dual_tbJoinOrder (RelOrder.dual_tbMeetOrder ord) = ord := erefl.

Let eq_dual_dual_lattice (ord : {lattice T}) :
  RelOrder.dual_lattice (RelOrder.dual_lattice ord) = ord := erefl.

Let eq_dual_dual_bLattice (ord : {bLattice T}) :
  RelOrder.dual_bLattice (RelOrder.dual_tLattice ord) = ord := erefl.

Let eq_dual_dual_tLattice (ord : {tLattice T}) :
  RelOrder.dual_tLattice (RelOrder.dual_bLattice ord) = ord := erefl.

Let eq_dual_dual_tbLattice (ord : {tbLattice T}) :
  RelOrder.dual_tbLattice (RelOrder.dual_tbLattice ord) = ord := erefl.

Let eq_dual_dual_distrLattice (ord : {distrLattice T}) :
  RelOrder.dual_distrLattice (RelOrder.dual_distrLattice ord) = ord := erefl.

Let eq_dual_dual_bDistrLattice (ord : {bDistrLattice T}) :
  RelOrder.dual_bDistrLattice (RelOrder.dual_tDistrLattice ord) = ord := erefl.

Let eq_dual_dual_tDistrLattice (ord : {tDistrLattice T}) :
  RelOrder.dual_tDistrLattice (RelOrder.dual_bDistrLattice ord) = ord := erefl.

Let eq_dual_dual_tbDistrLattice (ord : {tbDistrLattice T}) :
  RelOrder.dual_tbDistrLattice (RelOrder.dual_tbDistrLattice ord) = ord :=
  erefl.

Let eq_dual_dual_totalOrder (ord : {totalOrder T}) :
  RelOrder.dual_totalOrder (RelOrder.dual_totalOrder ord) = ord := erefl.

Let eq_dual_dual_bTotalOrder (ord : {bTotalOrder T}) :
  RelOrder.dual_bTotalOrder (RelOrder.dual_tTotalOrder ord) = ord := erefl.

Let eq_dual_dual_tTotalOrder (ord : {tTotalOrder T}) :
  RelOrder.dual_tTotalOrder (RelOrder.dual_bTotalOrder ord) = ord := erefl.

Let eq_dual_dual_tbTotalOrder (ord : {tbTotalOrder T}) :
  RelOrder.dual_tbTotalOrder (RelOrder.dual_tbTotalOrder ord) = ord := erefl.

End relorder.

Section order.
Variable (disp : unit).

Let eq_dual_dual_porderType (T : porderType disp) :
  Order.POrder.class T = Order.POrder.class [porderType of T^d^d] := erefl.

Let eq_dual_dual_bPOrderType (T : bPOrderType disp) :
  Order.BPOrder.class T = Order.BPOrder.class [bPOrderType of T^d^d] := erefl.

Let eq_dual_dual_tPOrderType (T : tPOrderType disp) :
  Order.TPOrder.class T = Order.TPOrder.class [tPOrderType of T^d^d] := erefl.

Let eq_dual_dual_tbPOrderType (T : tbPOrderType disp) :
  Order.TBPOrder.class T = Order.TBPOrder.class [tbPOrderType of T^d^d] :=
  erefl.

Let eq_dual_dual_meetSemilatticeType (T : meetSemilatticeType disp) :
  Order.MeetSemilattice.class T =
  Order.MeetSemilattice.class [meetSemilatticeType of T^d^d] := erefl.

Let eq_dual_dual_bMeetSemilatticeType (T : bMeetSemilatticeType disp) :
  Order.BMeetSemilattice.class T =
  Order.BMeetSemilattice.class [bMeetSemilatticeType of T^d^d] := erefl.

Let eq_dual_dual_tMeetSemilatticeType (T : tMeetSemilatticeType disp) :
  Order.TMeetSemilattice.class T =
  Order.TMeetSemilattice.class [tMeetSemilatticeType of T^d^d] := erefl.

Let eq_dual_dual_tbMeetSemilatticeType (T : tbMeetSemilatticeType disp) :
  Order.TBMeetSemilattice.class T =
  Order.TBMeetSemilattice.class [tbMeetSemilatticeType of T^d^d] := erefl.

Let eq_dual_dual_joinSemilatticeType (T : joinSemilatticeType disp) :
  Order.JoinSemilattice.class T =
  Order.JoinSemilattice.class [joinSemilatticeType of T^d^d] := erefl.

Let eq_dual_dual_bJoinSemilatticeType (T : bJoinSemilatticeType disp) :
  Order.BJoinSemilattice.class T =
  Order.BJoinSemilattice.class [bJoinSemilatticeType of T^d^d] := erefl.

Let eq_dual_dual_tJoinSemilatticeType (T : tJoinSemilatticeType disp) :
  Order.TJoinSemilattice.class T =
  Order.TJoinSemilattice.class [tJoinSemilatticeType of T^d^d] := erefl.

Let eq_dual_dual_tbJoinSemilatticeType (T : tbJoinSemilatticeType disp) :
  Order.TBJoinSemilattice.class T =
  Order.TBJoinSemilattice.class [tbJoinSemilatticeType of T^d^d] := erefl.

Let eq_dual_dual_latticeType (T : latticeType disp) :
  Order.Lattice.class T = Order.Lattice.class [latticeType of T^d^d] := erefl.

Let eq_dual_dual_bLatticeType (T : bLatticeType disp) :
  Order.BLattice.class T = Order.BLattice.class [bLatticeType of T^d^d] :=
  erefl.

Let eq_dual_dual_tLatticeType (T : tLatticeType disp) :
  Order.TLattice.class T = Order.TLattice.class [tLatticeType of T^d^d] :=
  erefl.

Let eq_dual_dual_tbLatticeType (T : tbLatticeType disp) :
  Order.TBLattice.class T = Order.TBLattice.class [tbLatticeType of T^d^d] :=
  erefl.

Let eq_dual_dual_distrLatticeType (T : distrLatticeType disp) :
  Order.DistrLattice.class T =
  Order.DistrLattice.class [distrLatticeType of T^d^d] := erefl.

Let eq_dual_dual_bDistrLatticeType (T : bDistrLatticeType disp) :
  Order.BDistrLattice.class T =
  Order.BDistrLattice.class [bDistrLatticeType of T^d^d] := erefl.

Let eq_dual_dual_tDistrLatticeType (T : tDistrLatticeType disp) :
  Order.TDistrLattice.class T =
  Order.TDistrLattice.class [tDistrLatticeType of T^d^d] := erefl.

Let eq_dual_dual_tbDistrLatticeType (T : tbDistrLatticeType disp) :
  Order.TBDistrLattice.class T =
  Order.TBDistrLattice.class [tbDistrLatticeType of T^d^d] := erefl.

Let eq_dual_dual_orderType (T : orderType disp) :
  Order.Total.class T = Order.Total.class [orderType of T^d^d] := erefl.

Let eq_dual_dual_bOrderType (T : bOrderType disp) :
  Order.BTotal.class T = Order.BTotal.class [bOrderType of T^d^d] := erefl.

Let eq_dual_dual_tOrderType (T : tOrderType disp) :
  Order.TTotal.class T = Order.TTotal.class [tOrderType of T^d^d] := erefl.

Let eq_dual_dual_tbOrderType (T : tbOrderType disp) :
  Order.TBTotal.class T = Order.TBTotal.class [tbOrderType of T^d^d] := erefl.

Let eq_dual_dual_finPOrderType (T : finPOrderType disp) :
  Order.FinPOrder.class T = Order.FinPOrder.class [finPOrderType of T^d^d] :=
  erefl.

Let eq_dual_dual_finBPOrderType (T : finBPOrderType disp) :
  Order.FinBPOrder.class T = Order.FinBPOrder.class [finBPOrderType of T^d^d] :=
  erefl.

Let eq_dual_dual_finTPOrderType (T : finTPOrderType disp) :
  Order.FinTPOrder.class T = Order.FinTPOrder.class [finTPOrderType of T^d^d] :=
  erefl.

Let eq_dual_dual_finTBPOrderType (T : finTBPOrderType disp) :
  Order.FinTBPOrder.class T =
  Order.FinTBPOrder.class [finTBPOrderType of T^d^d] := erefl.

Let eq_dual_dual_finMeetSemilatticeType (T : finMeetSemilatticeType disp) :
  Order.FinMeetSemilattice.class T =
  Order.FinMeetSemilattice.class [finMeetSemilatticeType of T^d^d] := erefl.

Let eq_dual_dual_finBMeetSemilatticeType (T : finBMeetSemilatticeType disp) :
  Order.BMeetSemilattice.class T =
  Order.BMeetSemilattice.class [finBMeetSemilatticeType of T^d^d] := erefl.

Let eq_dual_dual_finJoinSemilatticeType (T : finJoinSemilatticeType disp) :
  Order.FinJoinSemilattice.class T =
  Order.FinJoinSemilattice.class [finJoinSemilatticeType of T^d^d] := erefl.

Let eq_dual_dual_finTJoinSemilatticeType (T : finTJoinSemilatticeType disp) :
  Order.TJoinSemilattice.class T =
  Order.TJoinSemilattice.class [finTJoinSemilatticeType of T^d^d] := erefl.

Let eq_dual_dual_FinLatticeType (T : finLatticeType disp) :
  Order.FinLattice.class T = Order.FinLattice.class [finLatticeType of T^d^d] :=
  erefl.

Let eq_dual_dual_FinTBLatticeType (T : finTBLatticeType disp) :
  Order.FinTBLattice.class T =
  Order.FinTBLattice.class [finTBLatticeType of T^d^d] := erefl.

Let eq_dual_dual_finDistrLatticeType (T : finDistrLatticeType disp) :
  Order.FinDistrLattice.class T =
  Order.FinDistrLattice.class [finDistrLatticeType of T^d^d] := erefl.

Let eq_dual_dual_finTBDistrLatticeType (T : finTBDistrLatticeType disp) :
  Order.FinTBDistrLattice.class T =
  Order.FinTBDistrLattice.class [finTBDistrLatticeType of T^d^d] := erefl.

Let eq_dual_dual_finOrderType (T : finOrderType disp) :
  Order.FinTotal.class T = Order.FinTotal.class [finOrderType of T^d^d] :=
  erefl.

Let eq_dual_dual_finTBOrderType (T : finTBOrderType disp) :
  Order.FinTBTotal.class T = Order.FinTBTotal.class [finTBOrderType of T^d^d] :=
  erefl.

End order.
