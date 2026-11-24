# Native compiler comparisons

PR #879 edits 39,120 modules at `a2a92740de233b5ca34edee530cb1efe7cd63b73`. Its community parent is `1cd97d8aa4a16681b109389ab18eefa4b2ba36d8`. The pinned compiler is Lean 4.37.0-rc1 at `0b77e12952ad`. Mathlib is pinned at `31ce06eaadf4`. The parent cache receipt binds the original compiler outputs. [Source pairs](../binding.json) · [Community receipt](https://rh-cache.taucetiproject.org/ci/revisions/1cd97d8aa4a16681b109389ab18eefa4b2ba36d8.json)

The native jobs re-elaborated 24,138 changed modules against the current community archives. The aggregate uses the Git source bytes of the published proposal. The module records retain the commits on which the workers actually ran. A further 14,982 source pairs have earlier native comparisons. Reuse requires identical original and proposed source bytes, the identical whole owning archive and identical effective compiler inputs. Together the two groups cover all 39,120 changed modules. The checks compare 879,697 declaration occurrences, representing 863,652 distinct Lean names, including types and private proof values. They check the public import flags and the warning multisets. Each module was checked against its official parent dependencies. The integrated root check loads the selected public module outputs together. A full Lake build would also re-elaborate affected importers as required by its dependency graph. The source inventory lists the declaration names within each owner. [Native comparison by module](native-modules.jsonl.gz) · [Selection and exclusions](summary.json) · [Declaration inventory](../declarations) · [Compiler input comparison](../project-inputs)

The public module, IR signature and IR body occupy **7,148,005,880 → 6,767,363,432 bytes** across the changed modules. Both the public module and the IR body shrink in every owner. The IR signatures have the same bytes. For each source pair, a second reader serialized the expected import arrays and checked the observed compiler digests. The byte count covers these three outputs. [Sizes by module](compiled-sizes.tsv.gz) · [Output digests](compiled-images.jsonl.gz) · [Distribution](size-distribution.json)

| Native output | Files with different bytes |
| --- | ---: |
| Public module (`.olean`) | 39,120 |
| IR signature (`.ir.sig`) | 0 |
| IR body (`.ir`) | 39,120 |
| Editor metadata (`.olean.server`) | 39,120 |
| Private module (`.olean.private`) | 39,110 |

The archive index records the ID, byte size, workflow run and SHA-256 that GitHub assigned to each original ZIP. The independent release check joined the module rows with the published Git source pairs, current official owners and the separate declaration census. The five final theorems have their own test against the integrated project inputs. [Original producer ZIPs](producer-archives/github-archives.json) · [Release cross-check](independent-release-check.json) · [Five final theorems](../five-theorems)

The native records cover 173,860 warning occurrences after source positions are removed. Per-module multiset digests are available for 30,052 rows. The earlier comparator retained equality results and counts for 9,068 transferred rows. Those rows have no additional warning digest.
