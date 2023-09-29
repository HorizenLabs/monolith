#!/bin/bash
# shellcheck disable=SC2086
set -eo pipefail

echo "" && echo "=== Running cargo build ===" && echo ""
cargo $CARGOARGS build --release
