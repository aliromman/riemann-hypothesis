# Source comparison for PR #977

Community commit `82c577caf1b8a66c76212d78a399234f55813d28` and proposed commit `13345ac952b571c8f08a856fcedab838bfef0af8` use Lean 4.37.0-rc1 and Mathlib `31ce06eaadf4a200c0e1407c5f10953cf606b8f8`. The proposal has source tree `1963e10e232f5316fbf9fb44f1651d59bc6cf9e4`. Upstream batch #1410 changed the mathematical sources. [Batch merge](https://github.com/leanprover-community/riemann-hypothesis/pull/1410) · [Upstream integration by file](upstream-integration.jsonl.gz)

The clump tool factors out repeated namespace opens and file-level sections, and preserves the ordered member archive. Among 68,094 recovered members, 43,655 match the upstream bytes. The other 24,439 have an outer section fusion. The only accompanying deletions inside those members are 7,021 final outer ends and 3,024 empty lines. Every declaration and tactic line matches the upstream source. The Lean change removes 252,183 scope command lines and 130,929 standalone comment lines. The Python tool and its tests add 448 physical lines net. Charging all 448 leaves 251,735 fewer code lines. [Counts and per-file data](scope-source-counts.json) · [Independent comparison of every member](scope-member-differences.json) · [Python line counts](python-change.json)

| Under `src/` | Community | Proposed |
| --- | ---: | ---: |
| Nonblank Lean lines | 14,240,044 | 13,856,932 |
| Physical Lean lines | 15,952,569 | 15,558,411 |
| Lean source bytes | 1,055,553,676 | 1,034,688,453 |
| Lean files | 59,823 | 59,823 |

The two proposals have no file additions, removals or renames under `src/`. Across all 9,137 files in both diffs, the Git merge has the complete import header from #879 and the complete scope body from #977. The combined source has 12,842,696 nonblank Lean lines, a reduction of 1,397,348. [Git trees](source-trees.json) · [Per-file merge comparison](composition-source.jsonl.gz)

The edited modules own 529,864 declaration occurrences and 524,976 distinct Lean names in the official parent. Of the other modules, 9,866 directly import an edited module and 30,369 depend on one at any depth. The compiled header comparison covers 59,822 modules and 367,514 project edges. [Declarations by module](declarations) · [Downstream counts](dependencies.json) · [Compiled import graph](compiled-import-graph.json)

The Git objects for the challenge, the two immediate proof providers, Main, Statements, the Comparator configuration, the five target names and the package pins match the parent. Of the edited modules, 4,304 have identical old and new source pairs, identical whole official owner archives and identical effective compiler inputs across the two batches. The other 7,230 require new checks. This record covers source and dependencies. Complete candidate verification requires the full Lake build and the community Comparator. Whole-project compilation time has not been measured. [Frozen inputs](protected-inputs.json) · [Selection](native-selection.json) · [Official cache identity](official-parent.json)

The independent transfer check reopens the official dependency archives, verifies the earlier native rows and requires the effective inputs to agree. A negative control uses a real owner for which the imported bytes changed. [Verified transfers](verified-transfers/verified.json) The two PR readers additionally recovered the same 72,877 entries in the same order from all 12,338 readable archives in the proposed tree. One unedited legacy archive already fails to decode at the community parent. [Archive compatibility and the exception](archive-reads.json)

## Current compiler checks

Stock Lake built a workload with 237 project modules and 27 downstream roots from this revision. The independent comparison covers 7,498 declarations, including private proof values, and 823 warnings. The recorded compiler file sizes use the actual candidate files and the community's complete original archive table. These are workload measurements. [Counts, generated C and five compiler file sizes](ordinary-workload/measurements.json) · [Per-module comparison](ordinary-workload/rows.jsonl.gz)

The five endpoint checks compile ClaimStrip, MainConclusion and Main on Apple silicon. They use the expected public dependency images for the entire project. Lean accepts the five original proof expressions and rejects a deliberately invalid replacement. Current original and candidate native compilations must still confirm all projected dependency bytes. The archive retains the fifteen root compiler files plus the frozen challenge and axiom checks. [Root archive and explicit input scope](projected-input-five-theorems/verified-projected-only.json) · [Actual native evidence at the time of the root run](projected-input-five-theorems/latest-native-evidence.json) · [Inputs checked against community archives](projected-input-five-theorems/fresh-compiler-input-witnesses.json)

The separate per-module checkpoint counts 4,324 of 11,534 edited modules at its capture time. The remaining work includes the complete comparison, the default Lake build and the standard Linux Comparator. [Checkpoint and scope](native-checkpoint/summary.json)

The reviewer commands for these original Darwin archives check the fifteen actual compiler files and their two providers. Each archive also contains its own partial input census. [Commands and archive hashes](projected-input-five-theorems/REVIEW-projected-Main.md) · [Reviewer command receipt](projected-input-five-theorems/reviewer-current-projected.json) · [Corresponding ordinary Lake workload](ordinary-workload/projection-comparison.json)
