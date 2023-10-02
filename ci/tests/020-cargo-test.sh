#!/bin/bash
# shellcheck disable=SC2086
set -eo pipefail

# Running cargo tests
echo "" && echo "=== Running cargo tests ===" && echo ""
cargo $CARGOARGS test --all-features --release
