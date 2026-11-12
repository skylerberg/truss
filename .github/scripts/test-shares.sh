#!/bin/sh
# Runs test executables, `test-shares.sh count executable...`, each as
# `count` processes at once, each with TRUSS_TEST_SHARE set to its share of
# the executable's tests, since one process runs its tests on one core.
# Each process's log is printed once it ends, folded where it passed, and
# the step fails if any process failed.
set -eu

count=$1
shift
logs=$(mktemp -d)

pids=""
for executable in "$@"; do
  share=0
  while [ "$share" -lt "$count" ]; do
    TRUSS_TEST_SHARE="$share/$count" "$executable" >"$logs/$(basename "$executable")-$share" 2>&1 &
    pids="$pids $!:$(basename "$executable")-$share"
    share=$((share + 1))
  done
done

status=0
for entry in $pids; do
  pid=${entry%%:*}
  log=${entry#*:}
  if wait "$pid"; then
    echo "::group::$log"
    cat "$logs/$log"
    echo "::endgroup::"
  else
    status=1
    echo "$log failed:"
    cat "$logs/$log"
  fi
done
exit "$status"
