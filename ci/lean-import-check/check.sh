#!/usr/bin/env bash
# Compile the selected candidate sources and compare all rebuilt interfaces.
set -euo pipefail
panel=$1
work=$2
ci=$3
roots=()
targets=()
while IFS= read -r name; do
  roots+=("$name")
  targets+=("+$name:olean")
done < "$ci/$panel-roots.txt"
lake --no-cache --fail-fast build "${targets[@]}" 2>&1 | tee "$work/build.log"
lake -q --log-level=error --no-cache --no-build build "${targets[@]}"
(
  cd "$ci"
  lean -c "$work/CheckInterface.c" CheckInterface.lean
  leanc -o "$work/check-interface" "$work/CheckInterface.c"
)
mkdir -p "$work/comparison"
: > "$work/comparisons.tsv"
while IFS= read -r name; do
  output=.lake/build/lib/lean/${name//./\/}.olean
  test -s "$output"
  printf '%s\t' "$name" >> "$work/comparisons.tsv"
  if ! "$work/check-interface" "$name" "$work/parent/$name.olean" "$output" "$work/comparison" >> "$work/comparisons.tsv"; then
    tail -n 1 "$work/comparisons.tsv" >&2
    exit 1
  fi
done < "$work/compare.txt"
cat "$work/comparisons.tsv"
# Replay three named roots with the pinned kernel. Each module was also
# checked during the stock Lake build.
lake env leanchecker -v "${roots[@]:0:3}" 2>&1 | tee "$work/replay.log"
