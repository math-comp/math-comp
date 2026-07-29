- in `order/`
  + the `Order.LTheory`, `Order.TTheory`, and `Order.CTheory` modules:
    import the required theory files (`preorder.v`, `porder.v`, `lattice.v`,
    `total_order.v`, `complemented_lattice.v`, and `order.v`) in the dependency
    order and use `Order.Theory` instead
  + the `Order.Syntax` module is subsumed by `Order.Exports`:
    there is no need to adapt users' code since they are exported by default
    ([#1580](https://github.com/math-comp/math-comp/pull/1580)).
