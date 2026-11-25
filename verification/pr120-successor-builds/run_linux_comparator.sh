#!/bin/sh
set -eu

expected=${1:?Pass the expected full Git commit as the first argument}
parent=${2:?Pass an existing results directory as the second argument}
revision=$(git rev-parse --verify HEAD)
changes=$(git status --porcelain)
if [ "$revision" != "$expected" ] || [ -n "$changes" ]; then
    printf 'Use a clean checkout of %s. HEAD is %s.\n' "$expected" "$revision" >&2
    exit 2
fi

out=$(mktemp -d "$parent/rh-comparator.XXXXXXXX")
printf '%s\n' "$out"
printf '%s\n' "$revision" > "$out/revision"
prefix=$(lean --print-prefix)
PATH="$prefix/bin:$PATH"
export PATH
lean --version > "$out/lean-version"

cache_exit=0
MATHLIB_CACHE_GET_URL=https://cache.mathlib.org/mathlib4 lake exe mathlib/cache get \
    > "$out/mathlib-cache.log" 2>&1 || cache_exit=$?
printf '%s\n' "$cache_exit" > "$out/mathlib-cache.exit"
if [ "$cache_exit" -ne 0 ]; then
    exit "$cache_exit"
fi

comparator_exit=0
LAKE_ARTIFACT_CACHE=false lake comparator --json \
    > "$out/comparator-report.json" 2> "$out/comparator.stderr" || comparator_exit=$?
printf '%s\n' "$comparator_exit" > "$out/comparator.exit"
exit "$comparator_exit"
