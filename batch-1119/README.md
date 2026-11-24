# Source integration after community batch 5

PR #977 has candidate commit `989ea9c41e8400a6fe894fe365298c219f8c7e1d` and source tree `a598d19cccf798deb6e2bea9700cbac2ff050e11`. Its mathematical parent is community commit `1cd97d8aa4a16681b109389ab18eefa4b2ba36d8`. Its official compiler cache lists 60,146 project modules and uses Lean 4.37.0-rc1 with Mathlib `31ce06eaadf4`. [Community batch](https://github.com/leanprover-community/riemann-hypothesis/pull/1119) · [Official community receipt](https://rh-cache.taucetiproject.org/ci/revisions/1cd97d8aa4a16681b109389ab18eefa4b2ba36d8.json)

The patch removes 251,766 Lean commands and 131,585 standalone comments from 11,575 clumps. Charging all 400 net new Python lines against the command savings leaves 251,366 code lines removed. The new layout retains 68,375 original members, in their original order, with their complete import headers.

| Under `src/` | Community parent | Proposed |
| --- | ---: | ---: |
| Nonblank Lean lines | 14,799,476 | 14,416,125 |
| Physical Lean lines | 16,531,025 | 16,137,102 |
| Lean source bytes | 1,084,079,300 | 1,063,301,737 |
| Lean source files | 60,147 | 60,147 |

The existing reader recovers each member on the parent. The new reader reconstructs the same member import records and body text apart from 24,534 specified section fusions. The normal renderer reproduces each proposed clump. [Module-by-module source audit](scope-source-rows.jsonl.gz) [Source audit](source-audit.json) · [Full tree counts](source-trees.json)

Upstream changed 139 retained module sources and deleted 4 more. The merge applies the transformation to the new upstream proofs and preserves the deletions. The other 11,436 source pairs match the preceding proposal at the byte level. Compiler artifacts and their dependency inputs require a separate comparison before a previous result can be reused. [Changed source pairs](new-source-pairs.json) · [Merge record](upstream-integration.json) · [Pre-merge source reconstruction](coordination/batch5-peer-sources.json)

The project graph contains 369,383 project imports. Among untouched modules, 9,940 directly import an edited module and 30,548 depend on an edited module transitively. Both proposals together affect 41,518 distinct Lean files. In every one of the 9,177 overlapping files, the merged bytes consist of the import branch's header and the scope branch's body. That merged tree contains 13,397,697 nonblank Lean lines under `src/`, a reduction of 1,401,779. [Downstream dependencies](dependencies.json) · [Combined source trees](composition.json) · [Per-file composition](composition-source.jsonl.gz)

A full default-target build and the community's full independent five-theorem Comparator export require a separate run.

## Compiled outputs and theorem checks

The final records cover all 11,575 changed source modules and all five declarations in `Main`. The raw ZIP files retain the original GitHub authentication digests. The latest main comparison lists every subsequent upstream path and checks whether it changes a tested source or tool. [Compiled outputs](native) · [Five theorem proofs](five-theorems) · [Latest main comparison](latest-main.json)

We also built two selected workloads with both proposals together. The five full statements have separate evidence for each branch. [Combined-source checks](composition-native) · [From native run inputs to the current PRs](python-only-revision.json)

A later diagnostic revision at `be239239d08c` fixes literal markers outside clumps and includes a new whole-tree reader comparison. Its Lean source tree is identical to this record. [Revision and independent replay](archive-boundary)
