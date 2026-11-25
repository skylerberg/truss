#!/bin/sh
set -eu

runner=$1
runners=$2
executable=$3
processes=$(nproc)
shares=$((runners * processes))
logs=$(mktemp -d)

pids=""
process=0
while [ "$process" -lt "$processes" ]; do
  share=$((runner * processes + process))
  TRUSS_TEST_SHARE="$share/$shares" "$executable" >"$logs/$share" 2>&1 &
  pids="$pids $!:$share"
  process=$((process + 1))
done

status=0
for entry in $pids; do
  pid=${entry%%:*}
  share=${entry#*:}
  if wait "$pid"; then
    echo "::group::Share $share of $shares"
    cat "$logs/$share"
    echo "::endgroup::"
  else
    status=1
    echo "Share $share of $shares failed:"
    cat "$logs/$share"
  fi
done
exit "$status"
