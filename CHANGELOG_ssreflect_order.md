### Added

- in `order.v`
  + structures `OrderMorphism`, `MeetLatticeMorphism`,
      `JoinLatticeMorphism`, `LatticeMorphism`, `BLatticeMorphism`,
      `TLatticeMorphism`, `TBLatticeMorphism`, `MeetLatticeClosed`,
      `JoinLatticeClosed`, `LatticeClosed`, `BLatticeClosed`,
      `BJoinLatticeClosed`, `TLatticeClosed`, `TMeetLatticeClosed`,
      `TBLatticeClosed`, `SubPOrder`, `SubPOrderLattice`,
      `SubPOrderBLattice`, `SubPOrderTLattice`, `SubPOrderTBLattice`,
      `MeetSubLattice`, `MeetSubBLattice`, `MeetSubTLattice`,
      `MeetSubTBLattice`, `JoinSubLattice`, `JoinSubBLattice`,
      `JoinSubTLattice`, `JoinSubTBLattice`, `SubLattice`,
      `SubBLattice`, `SubTLattice`, `SubTBLattice`, `BJoinSubLattice`,
      `BJoinSubTLattice`, `BSubLattice`, `BSubTLattice`,
      `TMeetSubLattice`, `TMeetSubBLattice`, `TSubLattice`,
      `TSubBLattice`, `TBSubLattice`, `SubOrder`
  + predicate `meet_morphism`, `join_morphism`, `meet_closed`,
    `join_closed`

### Changed

- in `order.v`
  + the structures `POrder`, `Lattice`, `BLattice`, `TLattice`,
    `TBLattice`, `DistrLattice`, `BDistrLattice`, `TBDistrLattice`,
    `CBDistrLattice`, `CTBDDistrLattice`, `Total`, `FinPOrder`, `FinLattice`,
    `FinDistrLattice`, `FinCDistrLattice`, `FinTotal`
  + `PcanPOrderMixin` is replaced by `Order.PcanPartial`
  + `CanPOrderMixin` is replaced by `Order.CanPartial`
  + `MonoTotalMixin` is replaced by `MonoTotal`
  + `IsoLatticeMixin` is replaced by `Order.IsoLattice`

### Renamed

- in `order.v`:
  + `[porderMixin of T by <:]` -> `[POrder of T by <:]`
  + `[totalOrderMixin of T by <:]` -> `[Order of T by <:]`

### Removed

- in `order.v`:
  + `LtOrderMixin` (see factory `LtOrder`)
  + `OrderType`
  + `POrderType`
  + `LatticeType`
  + `BLatticeType`
  + `TBLatticeType`
  + `DistrLatticeType`
  + `CBDistrLatticeType`
  + `CTBDistrLatticeType`
  + factory `lePOrderMixin` (use factory `isLePOrdered` instead)
  + factory `ltPOrderMixin` (use factory `isLtPOrdered` instead)
  + factory `latticeMixin` (use mixin `POrder_isLattice` instead)
  + factory `distrLatticeMixin` (use mixin `Lattice_MeetIsDistributive` instead)
  + factory `distrLatticePOrderMixin` (use factory `POrder_isMeetDistrLattice` instead)
  + factory `meetJoinMixin` (use factory `isMeetJoinDistrLattice` instead)
  + factory `meetJoinLeMixin` (use factory `POrder_isMeetJoinLattice` instead)
  + factory `leOrderMixin` (use factory `isOrdered` instead)
  + factory `ltOrderMixin` (use factory `LtOrder` instead)
  + factory `meetJoinLeMixin` (use factory `Porder_isMeetJoinLattice` instead)
  + factory `totalPOrderMixin` (use factory `POrder_isTotal` instead)
  + factory `totalLatticeMixin` (use factory `Lattice_isTotal` instead)
  + factory `totalOrderMixin` (use factory `DistrLattice_isTotal` instead)
  + factory `bottomMixin` (use mixin `hasBottom` instead)
  + factory `topMixin` (use mixin `hasTop` instead)
  + factory `cbDistrLatticeMixin` (use mixin `hasSub` instead)
  + factory `ctbDistrLatticeMixin` (use mixin `hasCompl` instead)
  + `DistrLatticeOfChoiceType` (use `isMeetJoinDistrLattice.Build` and `HB.pack` instead),
    `DistrLatticeOfPOrderType` (use `POrder_isMeetDistrLattice.Build`)
    `OrderOfChoiceType` (use `isOrdered.Build`),
    `OrderOfPOrder` (use `POrder_isTotal.Build`),
    `OrderOfLattice` (use `Lattice_isTotal.Build`)

### Deprecated

- in `order.v`
  + notation `[porderType of T for cT]`, use `POrder.clone _ T cT`
  + notation `[porderType of T for cT with disp]`, use `POrder.clone disp T cT`
  + notation `[porderType of T]`, use `POrder.clone _ T _` or `T : porderType`
  + notation `[porderType of T with disp]`, use `POrder.clone disp T _`
  + notation `[latticeType of T for cT]`, use `Lattice.clone _ T cT`
  + notation `[latticeType of T for cT with disp]`, use `Lattice.clone disp T cT`
  + notation `[latticeType of T]`, use `Lattice.clone _ T _` or `T : latticeType`
  + notation `[latticeType of T with disp]`, use `Lattice.clone disp T _`
  + notation `[bLatticeType of T for cT]`, use `BLattice.clone _ T cT`
  + notation `[bLatticeType of T]`, use `BLattice.clone _ T _` or `T : bLatticeType`
  + notation `[bDistrLatticeType of T]`, use `BDistrLattice.clone _ T _` or `T : bDistrLatticeType`
  + notation `[tbDistrLatticeType of T]`, use `TBDistrLattice.clone _ T _` or `T : tbDistrLatticeType`
  + notation `[finPOrderType of T]`, use `FinPOrder.clone _ T _` or `T : finPOrderType`
  + notation `[finLatticeType of T]`, use `FinLattice.clone _ T _` or `T : finLatticeType`
  + notation `[finDistrLatticeType of T]`, use `FinDistrLattice.clone _ T _` or `T : finDistrLatticeType`
  + notation `[finCDistrLatticeType of T]`, use `FinCDistrLattice.clone _ T _` or `T : finCDistrLatticeType`
  + notation `[finOrderType of T]`, use `FinTotal.clone _ T _` or `T : finOrderType`
