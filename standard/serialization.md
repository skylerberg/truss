# standard::serialization

`Serialize` and `Deserialize` can be derived. Their methods are generic over
a `Serializer` or a `Deserializer`, so one derived implementation writes to
and reads from every format.

- A derived `Serialize` writes a record as its fields by name, in
  declaration order, a variant with no fields as its name, and a variant
  with fields as a record of them under its name.
- A derived `Deserialize` accepts a missing field that has a default, and
  reads a missing field of type `Option` as `None`.
- A format may rename every field, as `Names.CamelCase` does.
- A format whose values form a tree implements `Tree`, as `json::Value` and
  `toml::Value` do; `TreeWriter` and `TreeReader` then serialize to and from
  it.
