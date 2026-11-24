# Four upstream dependencies in the 03:06 UTC shard report

All 35 modules in the [operator's report](https://github.com/rohanarun/alpoge-rh-replay/blob/5e9aa6777a581de62b321234921fc536439c0b50/PR120-BUGS.md) are dependencies of `Main`. Twenty-nine have no other reported module among their transitive imports. Four of those 29 have other reported modules downstream. `targets.txt` lists these four. The pair of revisions below each requires the same 8,585 project sources for them. One source blob differs, in `DivisorProofs.Bundle0725`.

At the reported revision `1c5f0accc9a1e44d4166867f5452c8bc68440979`, stock Lake passed all four targets in 35,419 jobs. A second Lean invocation wrote each target to a fresh output directory and returned zero with no errors. `fresh.json` records the source and compiled hashes. At `7926ca49231f6bea8cd45a7c7408e9fd0b512426` all four modules built and each passed the stock Lean kernel replay. The report still records Linux shard failures. These local results use the pinned Lean 4.36.0 release on arm64 macOS.

In a checkout of the reported revision, download the pinned Mathlib cache. Set `checks` to the absolute path of this directory. The temporary outputs keep the stock objects available to check their dependents.

```sh
lake --version
lake exe cache get
xargs lake build < "$checks/targets.txt"
fresh=$(mktemp -d)
while IFS= read -r module; do
    name=$(printf '%s' "$module" | tr . /)
    mkdir -p "$fresh/$(dirname "$name")"
    lake env lean --json --root=src -DautoImplicit=false -DrelaxedAutoImplicit=false \
        -DmaxSynthPendingDepth=3 -DmaxHeartbeats=4000000 \
        -o "$fresh/$name.olean" -i "$fresh/$name.ilean" "src/$name.lean" || exit 1
done < "$checks/targets.txt"
```

Repeat the Lake build in a checkout of the second revision. The kernel check verifies that Lean opens the expected project object and calls `replayFromImports` on it. The receipt binds the four successful replays to the source manifest and the Lake dependency hashes. These commands cover four modules. `Main` and the five protected statements require their own checks on the final commit.

```sh
PR120_REPLAY_LIST="$checks/targets.txt" lake env lean "$checks/ReplayOriginalKernel.lean"
```
