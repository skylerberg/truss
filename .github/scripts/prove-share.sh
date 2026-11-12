#!/bin/sh
# Proves one runner's share of the standard library, `prove-share.sh index
# count`, from the directory that holds standard_library_tests.exe. The
# prover translates on one core, so the runner's share is proven by one
# process for each core, each a share of its own with a state of its own.
# Each process's log is printed once it ends, folded where it passed, and
# the step fails if any process failed.
set -eu

runner=$1
runners=$2
processes=$(nproc)
logs=$(mktemp -d)

pids=""
process=0
while [ "$process" -lt "$processes" ]; do
  share=$((runner * processes + process))
  TRUSS_PROOF_SHARE="$share/$((runners * processes))" TRUSS_PROOF_STATE="share-$share" \
    ./standard_library_tests.exe >"$logs/$share" 2>&1 &
  pids="$pids $!:$share"
  process=$((process + 1))
done

status=0
for entry in $pids; do
  pid=${entry%%:*}
  share=${entry#*:}
  if wait "$pid"; then
    echo "::group::Share $share"
    cat "$logs/$share"
    echo "::endgroup::"
  else
    status=1
    echo "Share $share failed:"
    cat "$logs/$share"
  fi
done
exit "$status"
