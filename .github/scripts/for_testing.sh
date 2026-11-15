#!/bin/sh
set -eu

uses=$(find stage0 grammar -name '*.ml' -not -path 'stage0/test/*' -not -path 'stage0/tools/*' \
  -not -path '*/_build/*' -exec awk '
    /^module For_testing = struct/ { inside = 1; next }
    inside && /^end/ { inside = 0; next }
    !inside && /For_testing\./ { print FILENAME ":" FNR ": " $0 }
  ' {} +)

if [ -n "$uses" ]; then
  echo "Only tests and tools may use For_testing:"
  echo "$uses"
  exit 1
fi
