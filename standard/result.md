# standard::result

- `result.map_error(convert)` converts the error, as before a `?`:
  `toml::parse(text).map_error(ConfigError.Malformed)?`.
- `result.ok()` turns a `Result` into an `Option`, and `option.ok_or(error)`,
  in `standard::option`, the reverse.
