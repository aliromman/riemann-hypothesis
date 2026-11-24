# Community batch 6 and PR #977

The community merged batch #1198 as `1da818b50f1e18808db2792b9dc735bda8cb84d8`. The proposed commit is `e7127ce8136d8ed36e610884d8578de1cffadd19`. The project uses Lean 4.37.0-rc1 and Mathlib `31ce06eaadf4`. The official receipt authenticates 59,908 project modules. [Community batch](https://github.com/leanprover-community/riemann-hypothesis/pull/1198) · [Community cache receipt](https://rh-cache.taucetiproject.org/ci/revisions/1da818b50f1e18808db2792b9dc735bda8cb84d8.json) · [Parent input comparison](official-receipt-comparison.json)

The patch removes 251,428 Lean scope commands and 131,362 comment lines from 11,551 proof clumps. It preserves the archive and order of all 68,255 original members. It joins 24,512 compatible public and noncomputable sections. Charging all 415 net new Python lines gives 251,013 fewer code lines. [Command categories](scope-command-counts.json) · [Reproduced source pairs](scope-source-rows.jsonl.gz) [Source audit](source-audit.json)

| Under `src/` | Community main | Proposed |
| --- | ---: | ---: |
| Nonblank Lean lines | 14,430,089 | 14,047,299 |
| Physical Lean lines | 16,153,947 | 15,760,590 |
| Lean source bytes | 1,065,406,229 | 1,044,654,939 |
| Lean source modules | 59,909 | 59,909 |

The new community batch changes 871 retained sources and deletes 24 others touched by the prior proposal. This revision uses each surviving community proof and preserves every deletion. The other 10,680 source pairs match the previous parent and proposal. [Integrated sources](upstream-integration.json) · [Changed source pairs](changed-source-pairs.json) · [Source preview before the community merge](coordination/prior-source-preview.json)

The graph has 368,104 project import edges. Among untouched modules, 9,885 import a changed module directly and 30,411 depend on one transitively. Both proposals together change 41,417 Lean files. All 9,155 shared files have exactly the import proposal’s header and the scope proposal’s body in the combined tree. It contains 13,031,422 nonblank Lean lines, a reduction of 1,398,667. [Dependency counts](dependencies.json) · [Combined tree](composition.json) · [Per-file comparison](composition-source.jsonl.gz)

A full default-target Lake rebuild and the full sandboxed five-theorem Comparator solution export remain community-run checks. The largest ordinary stock workload and the five-proof kernel replay use different sets of inputs.

The final reader and the preceding reader restore identical member bytes and order across 12,364 recoverable archives and 73,087 members on this tree. The community reader already fails to extract one other, unedited archive, `DefectTorsionSecondCohomologyKernel`, where local declarations appear between its first marker and its header. The same file and error are recorded on this revision. The final diagnostic control includes ordinary files and code before an archive. [Whole-tree comparison](archive-reads.json) · [Real stock errors](diagnostics/result.json)

In `QEqColPer` the new upstream proof removes three former member refinements. The final source keeps the one genuine section fusion. Restoring one blank line gives the standard rendering of the remaining body. All 840 retained refinements save at least one additional command. [Exact source and original member comparison](selection/standard-QEqColPer.json) · [Current per-owner refinements](selection/current-refinements.json)

## Compiled outputs and theorem checks

The final records cover all 11,551 changed source modules and all five declarations in `Main`. The raw ZIP files retain the original GitHub authentication digests. The upstream comparison records all paths changed since this mathematical parent and checks the two Git merge previews. [Compiled outputs](native) · [Five theorem proofs](five-theorems) · [Latest main comparison](latest-main.json)

The two proposals also share a measured compiler workload. Its input record identifies the exact joint tree and the community modules used. [Combined-source comparison](composition-native) · [Stock Lake and sandboxed source replays](bounded-checks.md) · [Cross-PR merge checks](coordination)
