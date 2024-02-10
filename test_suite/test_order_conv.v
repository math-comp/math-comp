From mathcomp Require Import all_ssreflect.
Import Order.Theory.

Section dual_of_dual.
Context (disp : Order.disp_t).

Let eq_dual_dual_preorderType (T : preorderType disp) :
  Order.Preorder.on T = Order.Preorder.on T^d^d := erefl.

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

Section dual_of_prod.
Context (disp1 disp2 : Order.disp_t).

Import DefaultProdOrder.

Let eq_dual_prod_porderType (T1 : porderType disp1) (T2 : porderType disp2) :
  Order.POrder.on (T1 * T2)^d = Order.POrder.on (T1^d * T2^d)%type := erefl.

Let eq_dual_prod_bPreorderType (T1 : bPreorderType disp1) (T2 : bPreorderType disp2) :
  Order.BPreorder.on (T1 * T2)^d = Order.BPreorder.on (T1^d * T2^d)%type := erefl.

Let eq_dual_prod_tPreorderType (T1 : tPreorderType disp1) (T2 : tPreorderType disp2) :
  Order.TPreorder.on (T1 * T2)^d = Order.TPreorder.on (T1^d * T2^d)%type := erefl.

Let eq_dual_prod_tbPreorderType
  (T1 : tbPreorderType disp1) (T2 : tbPreorderType disp2) :
  Order.TBPreorder.on (T1 * T2)^d = Order.TBPreorder.on (T1^d * T2^d)%type := erefl.

Let eq_dual_prod_bPOrderType (T1 : bPOrderType disp1) (T2 : bPOrderType disp2) :
  Order.BPOrder.on (T1 * T2)^d = Order.BPOrder.on (T1^d * T2^d)%type := erefl.

Let eq_dual_prod_tPOrderType (T1 : tPOrderType disp1) (T2 : tPOrderType disp2) :
  Order.TPOrder.on (T1 * T2)^d = Order.TPOrder.on (T1^d * T2^d)%type := erefl.

Let eq_dual_prod_tbPOrderType
  (T1 : tbPOrderType disp1) (T2 : tbPOrderType disp2) :
  Order.TBPOrder.on (T1 * T2)^d = Order.TBPOrder.on (T1^d * T2^d)%type := erefl.

Let eq_dual_prod_meetSemilatticeType
  (T1 : meetSemilatticeType disp1) (T2 : meetSemilatticeType disp2) :
  Order.MeetSemilattice.on (T1 * T2)^d
  = Order.MeetSemilattice.on (T1^d * T2^d)%type := erefl.

Let eq_dual_prod_bMeetSemilatticeType
  (T1 : bMeetSemilatticeType disp1) (T2 : bMeetSemilatticeType disp2) :
  Order.BMeetSemilattice.on (T1 * T2)^d
  = Order.BMeetSemilattice.on (T1^d * T2^d)%type := erefl.

Let eq_dual_prod_tMeetSemilatticeType
  (T1 : tMeetSemilatticeType disp1) (T2 : tMeetSemilatticeType disp2) :
  Order.TMeetSemilattice.on (T1 * T2)^d
  = Order.TMeetSemilattice.on (T1^d * T2^d)%type := erefl.

Let eq_dual_prod_tbMeetSemilatticeType
  (T1 : tbMeetSemilatticeType disp1) (T2 : tbMeetSemilatticeType disp2) :
  Order.TBMeetSemilattice.on (T1 * T2)^d
  = Order.TBMeetSemilattice.on (T1^d * T2^d)%type := erefl.

Let eq_dual_prod_joinSemilatticeType
  (T1 : joinSemilatticeType disp1) (T2 : joinSemilatticeType disp2) :
  Order.JoinSemilattice.on (T1 * T2)^d
  = Order.JoinSemilattice.on (T1^d * T2^d)%type := erefl.

Let eq_dual_prod_bJoinSemilatticeType
  (T1 : bJoinSemilatticeType disp1) (T2 : bJoinSemilatticeType disp2) :
  Order.BJoinSemilattice.on (T1 * T2)^d
  = Order.BJoinSemilattice.on (T1^d * T2^d)%type := erefl.

Let eq_dual_prod_tJoinSemilatticeType
  (T1 : tJoinSemilatticeType disp1) (T2 : tJoinSemilatticeType disp2) :
  Order.TJoinSemilattice.on (T1 * T2)^d
  = Order.TJoinSemilattice.on (T1^d * T2^d)%type := erefl.

Let eq_dual_prod_tbJoinSemilatticeType
  (T1 : tbJoinSemilatticeType disp1) (T2 : tbJoinSemilatticeType disp2) :
  Order.TBJoinSemilattice.on (T1 * T2)^d
  = Order.TBJoinSemilattice.on (T1^d * T2^d)%type := erefl.

Let eq_dual_prod_latticeType (T1 : latticeType disp1) (T2 : latticeType disp2) :
  Order.Lattice.on (T1 * T2)^d = Order.Lattice.on (T1^d * T2^d)%type := erefl.

Let eq_dual_prod_bLatticeType
  (T1 : bLatticeType disp1) (T2 : bLatticeType disp2) :
  Order.BLattice.on (T1 * T2)^d = Order.BLattice.on (T1^d * T2^d)%type := erefl.

Let eq_dual_prod_tLatticeType
  (T1 : tLatticeType disp1) (T2 : tLatticeType disp2) :
  Order.TLattice.on (T1 * T2)^d = Order.TLattice.on (T1^d * T2^d)%type := erefl.

Let eq_dual_prod_tbLatticeType
  (T1 : tbLatticeType disp1) (T2 : tbLatticeType disp2) :
  Order.TBLattice.on (T1 * T2)^d
  = Order.TBLattice.on (T1^d * T2^d)%type := erefl.

Let eq_dual_prod_distrLatticeType
  (T1 : distrLatticeType disp1) (T2 : distrLatticeType disp2) :
  Order.DistrLattice.on (T1 * T2)^d
  = Order.DistrLattice.on (T1^d * T2^d)%type := erefl.

Let eq_dual_prod_bDistrLatticeType
  (T1 : bDistrLatticeType disp1) (T2 : bDistrLatticeType disp2) :
  Order.BDistrLattice.on (T1 * T2)^d
  = Order.BDistrLattice.on (T1^d * T2^d)%type := erefl.

Let eq_dual_prod_tDistrLatticeType
  (T1 : tDistrLatticeType disp1) (T2 : tDistrLatticeType disp2) :
  Order.TDistrLattice.on (T1 * T2)^d
  = Order.TDistrLattice.on (T1^d * T2^d)%type := erefl.

Let eq_dual_prod_tbDistrLatticeType
  (T1 : tbDistrLatticeType disp1) (T2 : tbDistrLatticeType disp2) :
  Order.TBDistrLattice.on (T1 * T2)^d
  = Order.TBDistrLattice.on (T1^d * T2^d)%type := erefl.

Let eq_dual_prod_cDistrLatticeType
  (T1 : cDistrLatticeType disp1) (T2 : cDistrLatticeType disp2) :
  Order.CDistrLattice.on (T1 * T2)^d
  = Order.CDistrLattice.on (T1^d * T2^d)%type := erefl.

Let eq_dual_prod_cbDistrLatticeType
  (T1 : cbDistrLatticeType disp1) (T2 : cbDistrLatticeType disp2) :
  Order.CBDistrLattice.on (T1 * T2)^d
  = Order.CBDistrLattice.on (T1^d * T2^d)%type := erefl.

Let eq_dual_prod_ctDistrLatticeType
  (T1 : ctDistrLatticeType disp1) (T2 : ctDistrLatticeType disp2) :
  Order.CTDistrLattice.on (T1 * T2)^d
  = Order.CTDistrLattice.on (T1^d * T2^d)%type := erefl.

Let eq_dual_prod_ctbDistrLatticeType
  (T1 : ctbDistrLatticeType disp1) (T2 : ctbDistrLatticeType disp2) :
  Order.CTBDistrLattice.on (T1 * T2)^d
  = Order.CTBDistrLattice.on (T1^d * T2^d)%type := erefl.

End dual_of_prod.
