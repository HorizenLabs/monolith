#!/bin/bash
# shellcheck disable=SC2086
set -eo pipefail

# Running cargo fmt
echo "" && echo "=== Running cargo fmt --check ===" && echo ""
cargo $CARGOARGS fmt --check
