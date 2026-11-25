#!/bin/sh
set -eu

uses=$(find stage0 -name '*.ml' -not -path 'stage0/diagnostics/description/*' \
  -not -path 'stage0/test/*' -not -path 'stage0/tools/*' -not -path '*/_build/*' -exec awk '
    /^module For_rendering = struct/ { inside = 1; next }
    inside && /^end/ { inside = 0; next }
    !inside && /For_rendering\./ { print FILENAME ":" FNR ": " $0 }
  ' {} +)

if [ -n "$uses" ]; then
  echo "Only the description library, tests, and tools may use For_rendering:"
  echo "$uses"
  exit 1
fi
