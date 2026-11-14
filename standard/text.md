# standard::text

Methods of `String` and `StringSlice`, and the types of tagged templates.

- `trim()` returns a `StringSlice`, a view of the string, and `split()` and
  `lines()` return a `List` of them.
- `fields.join(", ")` and `mut text.push(more)` build text; strings have no
  concatenation operator.
- `text.bytes()` gives the bytes, `text.characters()` the `Character`s, and
  `text.graphemes()` the grapheme clusters as `StringSlice`s, since one character as a
  reader sees it can be several scalar values.
- `Template[Part]` holds a tagged template's `literals`, as `Literal`
  values, and its converted `parts`. A tag's check reads a literal's text
  with `literal.text()`, and its bytes with `text.byte(index)`.
