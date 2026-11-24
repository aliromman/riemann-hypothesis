# Native compiler comparisons

PR #977 edits 11,548 modules at `963ebea3bb3d7c2c5738946fca45317b8084f972`. Its community parent is `307cef33f046955ee79dba47e0d828d06496d75f`. The pinned compiler is Lean 4.37.0-rc1 at `0b77e12952ad`. Mathlib is pinned at `31ce06eaadf4`. The parent cache receipt binds the original compiler outputs. [Source pairs](../binding.json) · [Community receipt](https://rh-cache.taucetiproject.org/ci/revisions/307cef33f046955ee79dba47e0d828d06496d75f.json)

The native jobs re-elaborated 9,751 changed modules against the current community archives. The aggregate uses the Git source bytes of the published proposal. The module records retain the commits on which the workers actually ran. A further 1,797 source pairs have earlier native comparisons. Reuse requires identical original and proposed source bytes, the identical whole owning archive and identical effective compiler inputs. Together the two groups cover all 11,548 changed modules. The checks compare 532,127 declaration occurrences, representing 527,219 distinct Lean names, including types and private proof values. They check the public import flags and the warning multisets. Each module was checked against its official parent dependencies. The integrated root check loads the selected public module outputs together. The [ordinary Lake build](../ordinary-lake) follows the project dependency graph and rebuilds affected importers as needed. The source inventory lists the declaration names within each owner. [Native comparison by module](native-modules.jsonl.gz) · [Selection and exclusions](summary.json) · [Declaration inventory](../declarations) · [Compiler input comparison](../project-inputs)

All three ordinary compiler outputs have the same bytes in each edited module. Across these modules the public images occupy 3,223,586,728 bytes, the IR signatures 2,863,904 and the IR bodies 193,002,592. Raw editor and private files can include source positions. The compiler comparison also checks the declarations and their private proof values. [Sizes by module](compiled-sizes.tsv.gz)

| Native output | Files with different bytes |
| --- | ---: |
| Public module (`.olean`) | 0 |
| IR signature (`.ir.sig`) | 0 |
| IR body (`.ir`) | 0 |
| Editor metadata (`.olean.server`) | 11,547 |
| Private module (`.olean.private`) | 8,303 |

The archive index records the ID, byte size, workflow run and SHA-256 that GitHub assigned to each original ZIP. The independent release check joined the module rows with the published Git source pairs, current official owners and the separate declaration census. The five final theorems have their own test against the integrated project inputs. [Original producer ZIPs](producer-archives/github-archives.json) · [Release cross-check](independent-release-check.json) · [Five final theorems](../five-theorems)

The native records cover 133,843 warning occurrences after source positions are removed. Per-module multiset digests are available for 11,548 rows.
