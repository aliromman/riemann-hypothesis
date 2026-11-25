# Source comparison for PR #879

Community commit `82c577caf1b8a66c76212d78a399234f55813d28` and proposed commit `299eff8a308272be2b9167be917156f1929359a2` use Lean 4.37.0-rc1 and Mathlib `31ce06eaadf4a200c0e1407c5f10953cf606b8f8`. The proposal has source tree `98322f9e7758e1587b78ac21c1281d7f2431286c`. Upstream batch #1410 changed the mathematical sources. [Batch merge](https://github.com/leanprover-community/riemann-hypothesis/pull/1410) · [Upstream integration by file](upstream-integration.jsonl.gz)

The source audit checks every import removal and addition. All bytes after the import header match the community source in all 38,956 edited modules. The community extractor recovers the same 58,652 archived members from 9,238 clumps. The counts cover 1,014,616 removed private Mathlib imports and 380 narrower imports. The net reduction is 1,014,236 Lean code lines. [Counts by import](header-audit.json) · [Narrower providers by file](narrower-providers.json)

| Under `src/` | Community | Proposed |
| --- | ---: | ---: |
| Nonblank Lean lines | 14,240,044 | 13,225,808 |
| Physical Lean lines | 15,952,569 | 14,938,333 |
| Lean source bytes | 1,055,553,676 | 1,005,614,457 |
| Lean files | 59,823 | 59,823 |

The two proposals have no file additions, removals or renames under `src/`. Across all 9,137 files in both diffs, the Git merge has the complete import header from #879 and the complete scope body from #977. The combined source has 12,842,696 nonblank Lean lines, a reduction of 1,397,348. [Git trees](source-trees.json) · [Per-file merge comparison](composition-source.jsonl.gz)

The edited modules own 872,729 declaration occurrences and 856,835 distinct Lean names in the official parent. Of the other modules, 2,579 directly import an edited module and 10,331 depend on one at any depth. The compiled header comparison covers 59,822 modules and 367,514 project edges. [Declarations by module](declarations) · [Downstream counts](dependencies.json) · [Compiled import graph](compiled-import-graph.json)

The Git objects for the challenge, the two immediate proof providers, Main, Statements, the Comparator configuration, the five target names and the package pins match the parent. Of the edited modules, 17,651 have identical old and new source pairs, identical whole official owner archives and identical effective compiler inputs across the two batches. The other 21,305 require new checks. This record covers source and dependencies. Complete candidate verification requires the full Lake build and the community Comparator. Whole-project compilation time has not been measured. [Frozen inputs](protected-inputs.json) · [Selection](native-selection.json) · [Official cache identity](official-parent.json)

The independent transfer check reopens the official dependency archives, verifies the earlier native rows and requires the effective inputs to agree. A negative control uses a real owner for which the imported bytes changed. [Verified transfers](verified-transfers/verified.json)

## Current compiler checks

Stock Lake built a workload with 74 project modules and 7 downstream roots from this revision. The independent comparison covers 3,452 declarations, including private proof values, and 178 warnings. The recorded compiler file sizes use the actual candidate files and the community's complete original archive table. These are workload measurements. [Counts, generated C and five compiler file sizes](ordinary-workload/measurements.json) · [Per-module comparison](ordinary-workload/rows.jsonl.gz)

The five endpoint checks compile ClaimStrip, MainConclusion and Main on Apple silicon. They use the expected public dependency images for the entire project. Lean accepts the five original proof expressions and rejects a deliberately invalid replacement. Current original and candidate native compilations must still confirm all projected dependency bytes. The archive retains the fifteen root compiler files plus the frozen challenge and axiom checks. [Root archive and explicit input scope](projected-input-five-theorems/verified-projected-only.json) · [Actual native evidence at the time of the root run](projected-input-five-theorems/latest-native-evidence.json) · [Inputs checked against community archives](projected-input-five-theorems/fresh-compiler-input-witnesses.json)

The separate per-module checkpoint counts 17,700 of 38,956 edited modules at its capture time. The remaining work includes the complete comparison, the default Lake build and the standard Linux Comparator. [Checkpoint and scope](native-checkpoint/summary.json)
