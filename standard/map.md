# standard::map

`Map[Key, Value]` maps keys to values. Its entries are `Entry[Key, Value]`
records.

- A key is `Hash` and `Ordered`. A lookup, an insertion, or a removal costs
  O(log n) in the worst case and O(1) in typical use: a bucket that fills
  up becomes a balanced tree.
- A map iterates in insertion order.
- `ports[name]` requires the key; `ports.get(name)` returns `Some(value)` or
  `None`. `ports[own name] = value` inserts or replaces.
- `Map.seeded()` makes an empty map whose hashing takes a key from the
  `Random` capability, so it declares `uses Random`. It gives the same
  results as an ordinary map.

`Set[Element]`, in `standard::set`, follows the same rules for its elements.
