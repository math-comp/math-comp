From mathcomp Require Import all_ssreflect.
Import Order.Theory.

Section dual_of_dual.
Context (disp : Order.disp_t).

Let eq_dual_dual_porderType (T : porderType disp) :
  Order.POrder.on T = Order.POrder.on T^d^d := erefl.

Let eq_dual_dual_bPOrderType (T : bPOrderType disp) :
  Order.BPOrder.on T = Order.BPOrder.on T^d^d := erefl.

Let eq_dual_dual_tPOrderType (T : tPOrderType disp) :
  Order.TPOrder.on T = Order.TPOrder.on T^d^d := erefl.

Let eq_dual_dual_tbPOrderType (T : tbPOrderType disp) :
  Order.TBPOrder.on T = Order.TBPOrder.on T^d^d := erefl.

Let eq_dual_dual_meetSemilatticeType (T : meetSemilatticeType disp) :
  Order.MeetSemilattice.on T = Order.MeetSemilattice.on T^d^d := erefl.

Let eq_dual_dual_bMeetSemilatticeType (T : bMeetSemilatticeType disp) :
  Order.BMeetSemilattice.on T = Order.BMeetSemilattice.on T^d^d := erefl.

Let eq_dual_dual_tMeetSemilatticeType (T : tMeetSemilatticeType disp) :
  Order.TMeetSemilattice.on T = Order.TMeetSemilattice.on T^d^d := erefl.

Let eq_dual_dual_tbMeetSemilatticeType (T : tbMeetSemilatticeType disp) :
  Order.TBMeetSemilattice.on T = Order.TBMeetSemilattice.on T^d^d := erefl.

Let eq_dual_dual_joinSemilatticeType (T : joinSemilatticeType disp) :
  Order.JoinSemilattice.on T = Order.JoinSemilattice.on T^d^d := erefl.

Let eq_dual_dual_bJoinSemilatticeType (T : bJoinSemilatticeType disp) :
  Order.BJoinSemilattice.on T = Order.BJoinSemilattice.on T^d^d := erefl.

Let eq_dual_dual_tJoinSemilatticeType (T : tJoinSemilatticeType disp) :
  Order.TJoinSemilattice.on T = Order.TJoinSemilattice.on T^d^d := erefl.

Let eq_dual_dual_tbJoinSemilatticeType (T : tbJoinSemilatticeType disp) :
  Order.TBJoinSemilattice.on T = Order.TBJoinSemilattice.on T^d^d := erefl.

Let eq_dual_dual_latticeType (T : latticeType disp) :
  Order.Lattice.on T = Order.Lattice.on T^d^d := erefl.

Let eq_dual_dual_bLatticeType (T : bLatticeType disp) :
  Order.BLattice.on T = Order.BLattice.on T^d^d := erefl.

Let eq_dual_dual_tLatticeType (T : tLatticeType disp) :
  Order.TLattice.on T = Order.TLattice.on T^d^d := erefl.

Let eq_dual_dual_tbLatticeType (T : tbLatticeType disp) :
  Order.TBLattice.on T = Order.TBLattice.on T^d^d := erefl.

Let eq_dual_dual_distrLatticeType (T : distrLatticeType disp) :
  Order.DistrLattice.on T = Order.DistrLattice.on T^d^d := erefl.

Let eq_dual_dual_bDistrLatticeType (T : bDistrLatticeType disp) :
  Order.BDistrLattice.on T = Order.BDistrLattice.on T^d^d := erefl.

Let eq_dual_dual_tDistrLatticeType (T : tDistrLatticeType disp) :
  Order.TDistrLattice.on T = Order.TDistrLattice.on T^d^d := erefl.

Let eq_dual_dual_tbDistrLatticeType (T : tbDistrLatticeType disp) :
  Order.TBDistrLattice.on T = Order.TBDistrLattice.on T^d^d := erefl.

Let eq_dual_dual_cDistrLatticeType (T : cDistrLatticeType disp) :
  Order.CDistrLattice.on T = Order.CDistrLattice.on T^d^d := erefl.

Let eq_dual_dual_cbDistrLatticeType (T : cbDistrLatticeType disp) :
  Order.CBDistrLattice.on T = Order.CBDistrLattice.on T^d^d := erefl.

Let eq_dual_dual_ctDistrLatticeType (T : ctDistrLatticeType disp) :
  Order.CTDistrLattice.on T = Order.CTDistrLattice.on T^d^d := erefl.

Let eq_dual_dual_ctbDistrLatticeType (T : ctbDistrLatticeType disp) :
  Order.CTBDistrLattice.on T = Order.CTBDistrLattice.on T^d^d := erefl.

Let eq_dual_dual_orderType (T : orderType disp) :
  Order.Total.on T = Order.Total.on T^d^d := erefl.

Let eq_dual_dual_bOrderType (T : bOrderType disp) :
  Order.BTotal.on T = Order.BTotal.on T^d^d := erefl.

Let eq_dual_dual_tOrderType (T : tOrderType disp) :
  Order.TTotal.on T = Order.TTotal.on T^d^d := erefl.

Let eq_dual_dual_tbOrderType (T : tbOrderType disp) :
  Order.TBTotal.on T = Order.TBTotal.on T^d^d := erefl.

Let eq_dual_dual_finPOrderType (T : finPOrderType disp) :
  Order.FinPOrder.on T = Order.FinPOrder.on T^d^d := erefl.

Let eq_dual_dual_finBPOrderType (T : finBPOrderType disp) :
  Order.FinBPOrder.on T = Order.FinBPOrder.on T^d^d := erefl.

Let eq_dual_dual_finTPOrderType (T : finTPOrderType disp) :
  Order.FinTPOrder.on T = Order.FinTPOrder.on T^d^d := erefl.

Let eq_dual_dual_finTBPOrderType (T : finTBPOrderType disp) :
  Order.FinTBPOrder.on T = Order.FinTBPOrder.on T^d^d := erefl.

Let eq_dual_dual_finMeetSemilatticeType (T : finMeetSemilatticeType disp) :
  Order.FinMeetSemilattice.on T = Order.FinMeetSemilattice.on T^d^d := erefl.

Let eq_dual_dual_finBMeetSemilatticeType (T : finBMeetSemilatticeType disp) :
  Order.FinBMeetSemilattice.on T = Order.FinBMeetSemilattice.on T^d^d := erefl.

Let eq_dual_dual_finJoinSemilatticeType (T : finJoinSemilatticeType disp) :
  Order.FinJoinSemilattice.on T = Order.FinJoinSemilattice.on T^d^d := erefl.

Let eq_dual_dual_finTJoinSemilatticeType (T : finTJoinSemilatticeType disp) :
  Order.FinTJoinSemilattice.on T = Order.FinTJoinSemilattice.on T^d^d := erefl.

Let eq_dual_dual_FinLatticeType (T : finLatticeType disp) :
  Order.FinLattice.on T = Order.FinLattice.on T^d^d := erefl.

Let eq_dual_dual_FinTBLatticeType (T : finTBLatticeType disp) :
  Order.FinTBLattice.on T = Order.FinTBLattice.on T^d^d := erefl.

Let eq_dual_dual_FinDistrLatticeType (T : finDistrLatticeType disp) :
  Order.FinDistrLattice.on T = Order.FinDistrLattice.on T^d^d := erefl.

Let eq_dual_dual_FinTBDistrLatticeType (T : finTBDistrLatticeType disp) :
  Order.FinTBDistrLattice.on T = Order.FinTBDistrLattice.on T^d^d := erefl.

Let eq_dual_dual_finCDistrLatticeType (T : finCDistrLatticeType disp) :
  Order.FinCDistrLattice.on T = Order.FinCDistrLattice.on T^d^d := erefl.

Let eq_dual_dual_finCTBDistrLatticeType (T : finCTBDistrLatticeType disp) :
  Order.FinCTBDistrLattice.on T = Order.FinCTBDistrLattice.on T^d^d := erefl.

Let eq_dual_dual_finOrderType (T : finOrderType disp) :
  Order.FinTotal.on T = Order.FinTotal.on T^d^d := erefl.

Let eq_dual_dual_finTBOrderType (T : finTBOrderType disp) :
  Order.FinTBTotal.on T = Order.FinTBTotal.on T^d^d := erefl.

End dual_of_dual.
