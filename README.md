# Private Mathlib imports in the RH formalization

This directory records verification for commit `21baf112ac31f7376204339a3dd01f56d9f6a867`, with parent `a28ad7ec8b9f5ff4ec448fe210d3ac57aacfffe1`. The source change removes 1,026,876 original private import lines and adds 170 precise imports in 39,352 files. The upstream branch contains only Lean source changes.

## Reproduce the source count

Use a clone of the community repository with both revisions available. Set `EVIDENCE` to the directory that contains this README. Run these commands from the source repository. Python needs only its standard library.

```sh
git diff --numstat a28ad7ec8b9f5ff4ec448fe210d3ac57aacfffe1 21baf112ac31f7376204339a3dd01f56d9f6a867 | awk '{ added += $1; removed += $2 } END { print NR, added, removed }'
python3 "$EVIDENCE/audit_source.py" a28ad7ec8b9f5ff4ec448fe210d3ac57aacfffe1 21baf112ac31f7376204339a3dd01f56d9f6a867 \
  --targets "$EVIDENCE/targets.txt" --extra "$EVIDENCE/extra-imports.json" --unclump
```

The source audit reads the Git blobs, compares the declaration bodies byte for byte, and checks every deleted and added private import. It uses the repository's unclumper to compare the original member sources of changed clumps. `source-counts.json` holds the physical line, nonblank line and byte counts under `src/`. `other-lean-sources.json` lists the tracked Lean files outside that directory.

`project-dependents.json` counts the modules that directly and transitively depend on an edited file. It includes the branch counts for the three project imports of `Main`. It uses all 376,417 project import edges, checked against the compiled parent. For this change, 3,052 unmodified files import an edited module directly and 11,103 depend on one through at least one import. Those counts describe the potential rebuild scope.

## Inspect a compiler result

`modules.tsv.gz` has one record per edited source. Each record identifies the original and candidate source digests, the number of private imports removed, any added import, the number of local declarations, the parent archive, the public and IR output digests, and the verification run or local trial. The SHA-256 of the compressed table is `d51b9dcc4a5d4d2aad93c5502beff785480978d429f193fdafafccd9076bbc8e`.

`workflow-reports.json` records the source tree, workflow commit, per-module report digest and GitHub artifact digest for each completed native group. The original compiler reports are stored under `native-reports/` by the SHA-256 of the uncompressed JSONL data. They remain available after the temporary Actions artifacts expire. The native runner used the community cache, the pinned Lean executable, the Mathlib cache and Lean's own serializer. The private declaration table comparisons include local theorem proofs and auxiliary declarations. `five-theorems.json` records the status of the root check for this Git tree.

The first native sweep began before the merge of community PR #295. The reuse certificate compares the actual Git blobs, import flags and SHA-256 contents of the complete effective project import cones against both official archive manifests. Its list and witnesses are part of the newer workflow. [First native run](https://github.com/aliromman/riemann-hypothesis/actions/runs/45323243703) · [Current-base native run](https://github.com/aliromman/riemann-hypothesis/actions/runs/45327949270) · [Verification source](https://github.com/aliromman/riemann-hypothesis/tree/55b05d120de3421727dc1c0f67a6dbbc55ab5811/ci/import-screen) · [Parent cache receipt](https://rh-cache.taucetiproject.org/ci/revisions/a28ad7ec8b9f5ff4ec448fe210d3ac57aacfffe1.json)

To run the full independent check from source, use the upstream Linux instructions for `lake comparator`. [Community procedure](https://github.com/leanprover-community/riemann-hypothesis/blob/a28ad7ec8b9f5ff4ec448fe210d3ac57aacfffe1/README.md#checking-the-proof-yourself)
