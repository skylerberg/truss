# standard::core

Records for grouping values, and ranges.

```truss
public type Indexed[Element](index: USize, element: Element)
public type Pair[First, Second](first: First, second: Second)
```

- The elements of `enumerate` are `Indexed` values, and those of `zip` are
  `Pair` values. They are not in the prelude: a pattern never names them,
  and a signature writes `core::Pair`.
- `(0..count).reversed()` is a range's values in reverse order, and
  `(0..count).step_by(2)` every second value.
- `enumerate`, `zip`, and `reversed` read their collections. A loop over the
  positions changes two collections side by side:
  `for index in 0..totals.count() { totals[index] += amounts[index] }`.
