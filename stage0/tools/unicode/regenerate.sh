#!/bin/sh
set -eu

here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
data=${TRUSS_UNICODE_DATA:-$here/data}
mkdir -p "$data"

while read -r hash url; do
  file=$data/$(basename "$url")
  [ -f "$file" ] || curl --fail --silent --show-error --location --output "$file" "$url"
  actual=$(shasum -a 256 "$file" | cut -d ' ' -f 1)
  if [ "$actual" != "$hash" ]; then
    echo "$file: expected SHA-256 $hash, found $actual" >&2
    exit 1
  fi
done < "$here/sources.txt"

cd "$root"
dune build stage0/tools/unicode/generate.exe
./_build/default/stage0/tools/unicode/generate.exe "$data" > stage0/support/unicode/unicode_tables.ml.new
mv stage0/support/unicode/unicode_tables.ml.new stage0/support/unicode/unicode_tables.ml
dune build stage0/tools/unicode/library_tables.exe
./_build/default/stage0/tools/unicode/library_tables.exe "$data" > standard/text/unicode_data/unicode_data.truss.new
mv standard/text/unicode_data/unicode_data.truss.new standard/text/unicode_data/unicode_data.truss
dune build stage0/tools/unicode/conformance.exe
./_build/default/stage0/tools/unicode/conformance.exe "$data"
