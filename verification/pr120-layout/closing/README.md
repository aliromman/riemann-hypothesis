# PR #120 at its first closure

Deicyde closed #120 as superseded by #324. The last PR head was `fbb0941754dee95d15639f3d4d5596a3f508648b`. Its 47,885 tracked Lean files under `src/` compare with 149,397 on the common 4.36 parent. At closure, main `cb4dc6e23a6187db392c96664295415c55b6b01e` had 60,630 such files on Lean 4.37.0-rc1. A Git merge reported 62,585 conflicted paths, including 62,580 sources. [Maintainer decision](https://github.com/leanprover-community/riemann-hypothesis/pull/120#issuecomment-7129174329) · [Tracked counts](layout-pr120-at-close.json) · [Git conflict results](conflicts-pr120-at-close.json)

The M4 worker reached its terminal failure on `2d20aa9035becfe380b9fe619e3d3fc968cf3400`. The full error file has 67 diagnostics in 16 distinct files. The separate first-error file and the operator’s inventory identify the same 16 first lines. Twenty-four of the 27 failures on the earlier run now compiled. Three persisted and 13 new failed modules became reachable. [Terminal report](https://github.com/rohanarun/alpoge-rh-replay/issues/35028#issuecomment-7129630352) · [Immutable raw diagnostics](https://gist.github.com/maugomez77/f7c49320daf28dbce4ccb8c144899b18/5e431652188c0c9b498e6b0284b830da7da8cde5)

Twelve of the 16 files received source changes before the closing head. The four identical blobs accounted for 15 errors on the M4 pin. They correspond to the doubling integral, `BlockDecomposition.Bundle0463`, `IntegrableOnCartanDoubleCosetShellIntegrand` and `SetIntegralLeftCosetShellIntegrandEqZero`. Their dependencies could have changed. The operator stopped after the pinned run, so the closing revision has no measured failure count or Comparator result. The map lists the two Git blob IDs, diagnostic location, line correspondence, source commits and error count for every file. [Per-file comparison](m4-closing-source-comparison.json)

## Repeat the source comparison

Run these commands in this directory with Python 3.9 or later. Set `repo` to a clone that contains the two commits and their history. The script checks both diagnostic files against their SHA-256 digests. It also checks the first error in each file against the operator's comment.

```sh
gh api gists/f7c49320daf28dbce4ccb8c144899b18/5e431652188c0c9b498e6b0284b830da7da8cde5 > "$scratch/gist.json"
gh api repos/rohanarun/alpoge-rh-replay/issues/comments/7129630352 --jq .body > "$scratch/operator.md"
python3 replay_terminal.py --repo "$repo" --gist-json "$scratch/gist.json" \
  --operator-report "$scratch/operator.md" > "$scratch/comparison.json"
cmp m4-closing-source-comparison.json "$scratch/comparison.json"
```

Rohan reopened #120, then closed it again while the 4.36 builds continued. Use the author's shard board for current failures. [Author's update](https://github.com/leanprover-community/riemann-hypothesis/pull/120#issuecomment-7137899644) · [Shard board](https://github.com/rohanarun/alpoge-rh-replay/blob/main/PR120-BUGS.md)
