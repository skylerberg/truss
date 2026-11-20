#!/usr/bin/env bash
set -euo pipefail

root="$(git -C "$(dirname "$0")" rev-parse --show-toplevel)"
cd "$root"
mode="${1:-print}"
output="${2:-$(mktemp -d)}"
mkdir -p "$output"

dune build experimental/compare/compare.exe stage0/driver/truss/truss.exe
(cd experimental/frontend && "$root/_build/default/stage0/driver/truss/truss.exe" build)

git ls-files '*.truss' > "$output/corpus.txt"
xargs ./_build/default/experimental/compare/compare.exe "$mode" < "$output/corpus.txt" > "$output/ocaml.txt"
xargs ./experimental/frontend/frontend "$mode" < "$output/corpus.txt" > "$output/truss.txt"

if cmp -s "$output/ocaml.txt" "$output/truss.txt"; then
  echo "The two $mode outputs are identical: $(wc -l < "$output/ocaml.txt") lines over $(wc -l < "$output/corpus.txt") files."
else
  diff -a "$output/ocaml.txt" "$output/truss.txt" > "$output/difference.txt" || true
  echo "The $mode outputs differ; see $output/difference.txt."
  exit 1
fi
