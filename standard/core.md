# standard::core

Records for grouping values, and ranges.

```truss
public type Indexed[Element](index: USize, element: Element)
public type Pair[First, Second](first: First, second: Second)
```

- `enumerate` yields `Indexed` values and `zip` yields `Pair` values. They
  are not in the prelude: a pattern never names them, and a signature writes
  `core::Pair`.
- `(0..count).reversed()` yields a range's values in reverse order, and
  `(0..count).step_by(2)` every second value.
- `zip` of two indexable collections changes both side by side:
  `for (first, second) in mut names.zip(mut ages)`.
