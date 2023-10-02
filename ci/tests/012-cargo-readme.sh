#!/bin/bash
# shellcheck disable=SC2086
set -eo pipefail

readme=$(mktemp)

# Running cargo readme
echo "" && echo "=== Running cargo readme check ===" && echo ""

cargo $CARGOARGS readme -o ${readme}

if ! cmp -s README.md ${readme} ; then
    echo "You should update README.md: run"
    echo "> cargo readme > README.md"
    echo "and update your PR"
    exit "1" 
fi
exit 0
