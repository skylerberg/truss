#!/bin/bash
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

arguments=""
for argument in "$@"; do
  arguments="$arguments '$argument'"
done

git ls-files -z --cached --others --exclude-standard |
  while IFS= read -r -d '' file; do
    if [ -f "$file" ]; then printf '%s\0' "$file"; fi
  done |
  COPYFILE_DISABLE=1 tar --null -T - -cf - |
  ssh -o BatchMode=yes liquid "
    set -eu
    mkdir -p benchmark/truss benchmark/scratch
    exec 9> benchmark/truss.lock
    flock -w 3600 9
    cd benchmark/truss
    find . -mindepth 1 -maxdepth 1 ! -name _build -exec rm -rf {} +
    tar -xf - --warning=no-unknown-keyword
    eval \$(opam env --switch=default)
    dune build ./stage0/tools/database_benchmark/database_benchmark.exe
    rm -rf ../scratch/*
    TMPDIR=\$HOME/benchmark/scratch ./_build/default/stage0/tools/database_benchmark/database_benchmark.exe $arguments
  "
