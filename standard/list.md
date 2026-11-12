# standard::list

`List`, `Slice`, and `Array`.

- `items.get(i)` returns `Some(element)`, or `None` if `i` is out of bounds,
  where `items[i]` requires the index.
- `Array.filled(value)` and `Array.generate(fn(index) { ... })` take the
  length from the expected type:

  ```truss
  let digest: Array[UInt8, 32] = Array.filled(0)
  let squares: Array[USize, 8] = Array.generate(fn(index) { index * index })

  fn sum[count: USize](values: Array[Int64, count]) -> Int64
  ```

- Every method of `Slice` that reads or changes elements in place exists on
  `List` and `Array` too, so `mut names.sort()` needs no slice.
