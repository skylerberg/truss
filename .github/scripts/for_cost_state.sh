#!/bin/sh
set -eu

uses=$(grep -n -E '\.cost\.' stage0/prover/core/*.ml |
  grep -v -E '^stage0/prover/core/(counters|cost_promises|potentials|amounts|loop_costs)\.ml:' ||
  true)

if [ -n "$uses" ]; then
  echo "Only the cost modules may read or write the state of cost checking:"
  echo "$uses"
  exit 1
fi
