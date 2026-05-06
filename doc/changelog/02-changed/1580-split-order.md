- `order.v` is split into the following files in `order/`:
  + `porder.v` contains partial order structures and their theory,
  + `lattice.v` contains semilattice and lattice structures and their theory,
  + `total_order.v` contains total order structures and their theory,
  + `complemented_lattice.v` contains complemented lattice structures and their
    theory,
  + `lattice_instances.v` contains order structure instances that are at most
    lattices, i.e., the product order on lists, and `nat` ordered by
    divisibility,
  + `total_order_instances.v` contains order structure instances that are at
    most total orders, i.e., the lexicographic orders on the product type and
    lists, `nat`, and finite ordinals,
  + `complemented_lattice_instances.v` contains order structure instances that
    are at most complemented lattices, i.e., the product order on the product
    types and tuples,
  + `order_instances.v` re-exports the above "instance" files, and provide
    order structure instances on `bool`, which is both totally ordered and
    a complemented lattice
  + `order.v` re-exports all the files above: it is recommended to import this
    file when one needs both `total_order.v` and `complemented_lattice.v`;
    otherwise, `Import Order.Theory` may not give access to some lemmas
    ([#1580](https://github.com/math-comp/math-comp/pull/1580),
    fixes [#1508](https://github.com/math-comp/math-comp/issues/1508)).
