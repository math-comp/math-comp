From mathcomp Require Import all_ssreflect.
Import Order.Theory.

Section dual_of_dual.

Let eq_dual_dual_porderType (disp : unit) (T : porderType disp) :=
  erefl _ : Order.POrder.class T = Order.POrder.class [porderType of T^d^d].

Let eq_dual_dual_bPOrderType (disp : unit) (T : bPOrderType disp) :=
  erefl _ : Order.BPOrder.class T = Order.BPOrder.class [bPOrderType of T^d^d].

Let eq_dual_dual_tPOrderType (disp : unit) (T : tPOrderType disp) :=
  erefl _ : Order.TPOrder.class T = Order.TPOrder.class [tPOrderType of T^d^d].

Let eq_dual_dual_tbPOrderType (disp : unit) (T : tbPOrderType disp) :=
  erefl _ : Order.TBPOrder.class T =
            Order.TBPOrder.class [tbPOrderType of T^d^d].

Let eq_dual_dual_latticeType (disp : unit) (T : latticeType disp) :=
  erefl _ : Order.Lattice.class T = Order.Lattice.class [latticeType of T^d^d].

Let eq_dual_dual_bLatticeType (disp : unit) (T : bLatticeType disp) :=
  erefl _ : Order.BLattice.class T =
            Order.BLattice.class [bLatticeType of T^d^d].

Let eq_dual_dual_tLatticeType (disp : unit) (T : tLatticeType disp) :=
  erefl _ : Order.TLattice.class T =
            Order.TLattice.class [tLatticeType of T^d^d].

Let eq_dual_dual_tbLatticeType (disp : unit) (T : tbLatticeType disp) :=
  erefl _ : Order.TBLattice.class T =
            Order.TBLattice.class [tbLatticeType of T^d^d].

Let eq_dual_dual_distrLatticeType (disp : unit) (T : distrLatticeType disp) :=
  erefl _ : Order.DistrLattice.class T =
            Order.DistrLattice.class [distrLatticeType of T^d^d].

Let eq_dual_dual_bDistrLatticeType (disp : unit) (T : bDistrLatticeType disp) :=
  erefl _ : Order.BDistrLattice.class T =
            Order.BDistrLattice.class [bDistrLatticeType of T^d^d].

Let eq_dual_dual_tDistrLatticeType (disp : unit) (T : tDistrLatticeType disp) :=
  erefl _ : Order.TDistrLattice.class T =
            Order.TDistrLattice.class [tDistrLatticeType of T^d^d].

Let eq_dual_dual_tbDistrLatticeType
    (disp : unit) (T : tbDistrLatticeType disp) :=
  erefl _ : Order.TBDistrLattice.class T =
            Order.TBDistrLattice.class [tbDistrLatticeType of T^d^d].

Let eq_dual_dual_orderType (disp : unit) (T : orderType disp) :=
  erefl _ : Order.Total.class T = Order.Total.class [orderType of T^d^d].

Let eq_dual_dual_finPOrderType (disp : unit) (T : finPOrderType disp) :=
  erefl _ : Order.FinPOrder.class T =
            Order.FinPOrder.class [finPOrderType of T^d^d].

Let eq_dual_dual_finBPOrderType (disp : unit) (T : finBPOrderType disp) :=
  erefl _ : Order.FinBPOrder.class T =
            Order.FinBPOrder.class [finBPOrderType of T^d^d].

Let eq_dual_dual_finTPOrderType (disp : unit) (T : finTPOrderType disp) :=
  erefl _ : Order.FinTPOrder.class T =
            Order.FinTPOrder.class [finTPOrderType of T^d^d].

Let eq_dual_dual_finTBPOrderType (disp : unit) (T : finTBPOrderType disp) :=
  erefl _ : Order.FinTBPOrder.class T =
            Order.FinTBPOrder.class [finTBPOrderType of T^d^d].

Let eq_dual_dual_FinLatticeType (disp : unit) (T : finLatticeType disp) :=
  erefl _ : Order.FinLattice.class T =
            Order.FinLattice.class [finLatticeType of T^d^d].

Let eq_dual_dual_finDistrLatticeType
    (disp : unit) (T : finDistrLatticeType disp) :=
  erefl _ : Order.FinDistrLattice.class T =
            Order.FinDistrLattice.class [finDistrLatticeType of T^d^d].

Let eq_dual_dual_finOrderType (disp : unit) (T : finOrderType disp) :=
  erefl _ : Order.FinTotal.class T =
            Order.FinTotal.class [finOrderType of T^d^d].

End dual_of_dual.
