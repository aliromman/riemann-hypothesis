# Source integration after community batch 5

PR #879 has candidate commit `a2a92740de233b5ca34edee530cb1efe7cd63b73` and source tree `6578db3dffd4f7afe7c61f2a6dfd013d3e23c341`. Its mathematical parent is community commit `1cd97d8aa4a16681b109389ab18eefa4b2ba36d8`. Its official compiler cache lists 60,146 project modules and uses Lean 4.37.0-rc1 with Mathlib `31ce06eaadf4`. [Community batch](https://github.com/leanprover-community/riemann-hypothesis/pull/1119) · [Official community receipt](https://rh-cache.taucetiproject.org/ci/revisions/1cd97d8aa4a16681b109389ab18eefa4b2ba36d8.json)

The patch deletes 1,018,810 private Mathlib import lines and adds 382 narrow replacements. Every byte after the import preamble stays the same in 39,120 files. The existing clump extractor restores the identical 58,945 archived members in 9,278 affected clumps.

| Under `src/` | Community parent | Proposed |
| --- | ---: | ---: |
| Nonblank Lean lines | 14,799,476 | 13,781,048 |
| Physical Lean lines | 16,531,025 | 15,512,597 |
| Lean source bytes | 1,084,079,300 | 1,033,931,951 |
| Lean source files | 60,147 | 60,147 |

The source pass checks each import against the original catalog and the allowed narrow replacements. It also decodes every changed clump with the community extractor. [Source audit](source-audit.json) · [Full tree counts](source-trees.json)

Upstream changed 586 retained module sources and deleted 17 more. The merge applies the transformation to the new upstream proofs and preserves the deletions. The other 38,534 source pairs match the preceding proposal at the byte level. Compiler artifacts and their dependency inputs require a separate comparison before a previous result can be reused. [Changed source pairs](new-source-pairs.json) · [Merge record](upstream-integration.json) · [Pre-merge source reconstruction](coordination/batch5-peer-sources.json)

The project graph contains 369,383 project imports. Among untouched modules, 2,656 directly import an edited module and 10,515 depend on an edited module transitively. Both proposals together affect 41,518 distinct Lean files. In every one of the 9,177 overlapping files, the merged bytes consist of the import branch's header and the scope branch's body. That merged tree contains 13,397,697 nonblank Lean lines under `src/`, a reduction of 1,401,779. [Downstream dependencies](dependencies.json) · [Combined source trees](composition.json) · [Per-file composition](composition-source.jsonl.gz)

A full default-target build and the community's full independent five-theorem Comparator export require a separate run.

## Compiled outputs and theorem checks

The final records cover all 39,120 changed source modules and all five declarations in `Main`. The raw ZIP files retain the original GitHub authentication digests. The latest main comparison lists every subsequent upstream path and checks whether it changes a tested source or tool. [Compiled outputs](native) · [Five theorem proofs](five-theorems) · [Latest main comparison](latest-main.json)

We also built two selected workloads with both proposals together. The five full statements have separate evidence for each branch. [Combined-source checks](composition-native) · [From native run inputs to the current PRs](python-only-revision.json)

The following #977 diagnostic revision changes two Python files. Its entire joint Lean source tree is identical to the measured composition. [Published revisions and source manifests](current-peer-tool-revision.json)
