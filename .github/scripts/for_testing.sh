#!/bin/sh
# Fails when compiler code uses a module's For_testing submodule. Those
# exports exist only for the tests in stage0/test and the developer tools in
# stage0/tools; a library that reads them couples itself to another
# module's internals. A For_testing struct may read the For_testing of a
# module it re-exports.
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
