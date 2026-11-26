#!/bin/sh
set -eu

status=0

check_owners() {
  record=$1
  owners=$2
  uses=$(grep -n -E "\.$record\." stage0/prover/core/*.ml |
    grep -v -E "^stage0/prover/core/($owners)\.ml:" ||
    true)
  if [ -n "$uses" ]; then
    echo "Only the modules $owners may read or write the prover's \`$record\` state:"
    echo "$uses"
    status=1
  fi
}

check_owners cost 'counters|cost_promises|potentials|amounts|loop_costs'
check_owners axioms 'contract_axioms'
check_owners termination 'termination'
check_owners validity 'validity'
check_owners callbacks 'callbacks'

exit $status
