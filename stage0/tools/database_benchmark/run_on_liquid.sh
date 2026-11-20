#!/bin/bash
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

arguments=""
for argument in "$@"; do
  arguments="$arguments '$argument'"
done

run_directory="database-benchmark-$(date +%s)-$$"

git ls-files -z --cached --others --exclude-standard |
  while IFS= read -r -d '' file; do
    if [ -f "$file" ]; then printf '%s\0' "$file"; fi
  done |
  COPYFILE_DISABLE=1 tar --null -T - -cf - |
  ssh -o BatchMode=yes liquid "
    set -eu
    mkdir -p benchmark
    cd benchmark
    exec 9> truss.lock
    flock -w 3600 9
    mkdir $run_directory
    trap 'rm -rf \$HOME/benchmark/$run_directory' EXIT
    cd $run_directory
    tar -xf - --warning=no-unknown-keyword
    mkdir scratch
    eval \$(opam env --switch=default)
    dune build ./stage0/tools/database_benchmark/database_benchmark.exe >&2
    TMPDIR=\$HOME/benchmark/$run_directory/scratch ./_build/default/stage0/tools/database_benchmark/database_benchmark.exe $arguments
  "
