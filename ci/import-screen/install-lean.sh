#!/usr/bin/env bash
set -euo pipefail
installer="$RUNNER_TEMP/rh-elan-init.sh"
curl --fail --silent --show-error --location --retry 3   https://raw.githubusercontent.com/leanprover/elan/3cc76985a1becb3c03cd65c1c5007e6f186ae474/elan-init.sh -o "$installer"
sh "$installer" -y --default-toolchain none
"$HOME/.elan/bin/elan" toolchain install "$(cat lean-toolchain)"
echo "$HOME/.elan/bin" >> "$GITHUB_PATH"
