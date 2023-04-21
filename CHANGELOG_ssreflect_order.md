### Added

### Changed

### Renamed

### Removed

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
