#!/bin/sh
# Downloads the Unicode data files listed in sources.txt, checks each against
# its recorded SHA-256 hash, writes the compiler's tables in
# stage0/unicode/unicode_tables.ml and the standard library's in
# standard/text/unicode_data.truss from them, and then checks every table of
# the compiler against the file it came from.
#
# Building the compiler never runs this. Run it only to regenerate the tables.
# The files are kept in tools/unicode/data, or in $TRUSS_UNICODE_DATA if set.
set -eu

here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
data=${TRUSS_UNICODE_DATA:-$here/data}
mkdir -p "$data"

grep -v '^#' "$here/sources.txt" | while read -r hash url; do
  [ -n "$hash" ] || continue
  file=$data/$(basename "$url")
  [ -f "$file" ] || curl --fail --silent --show-error --location --output "$file" "$url"
  actual=$(shasum -a 256 "$file" | cut -d ' ' -f 1)
  if [ "$actual" != "$hash" ]; then
    echo "$file: expected SHA-256 $hash, found $actual" >&2
    exit 1
  fi
done

cd "$root"
dune build stage0/tools/unicode/generate.exe
./_build/default/stage0/tools/unicode/generate.exe "$data" > stage0/unicode/unicode_tables.ml.new
mv stage0/unicode/unicode_tables.ml.new stage0/unicode/unicode_tables.ml
dune build stage0/tools/unicode/library_tables.exe
./_build/default/stage0/tools/unicode/library_tables.exe "$data" > standard/text/unicode_data.truss.new
mv standard/text/unicode_data.truss.new standard/text/unicode_data.truss
dune build stage0/tools/unicode/conformance.exe
./_build/default/stage0/tools/unicode/conformance.exe "$data"
