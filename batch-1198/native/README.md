# Native compiler comparisons

PR #977 edits 11,551 modules at `e7127ce8136d8ed36e610884d8578de1cffadd19`. Its community parent is `1da818b50f1e18808db2792b9dc735bda8cb84d8`. The pinned compiler is Lean 4.37.0-rc1 at `0b77e12952ad`. Mathlib is pinned at `31ce06eaadf4`. The parent cache receipt binds the original compiler outputs. [Source pairs](../binding.json) · [Community receipt](https://rh-cache.taucetiproject.org/ci/revisions/1da818b50f1e18808db2792b9dc735bda8cb84d8.json)

The native jobs re-elaborated 8,254 changed modules against the current community archives. The aggregate uses the Git source bytes of the published proposal. The module records retain the commits on which the workers actually ran. A further 3,297 source pairs have earlier native comparisons. Reuse requires identical original and proposed source bytes, the identical whole owning archive and identical effective compiler inputs. Together the two groups cover all 11,551 changed modules. The checks compare 532,429 declaration occurrences, representing 527,519 distinct Lean names, including types and private proof values. They check the public import flags and the warning multisets. Each module was checked against its official parent dependencies. The integrated root check loads the selected public module outputs together. A full Lake build would also re-elaborate affected importers as required by its dependency graph. The source inventory lists the declaration names within each owner. [Native comparison by module](native-modules.jsonl.gz) · [Selection and exclusions](summary.json) · [Declaration inventory](../declarations) · [Compiler input comparison](../project-inputs)

All three ordinary compiler outputs have the same bytes in each edited module. Across these modules the public images occupy 3,226,999,648 bytes, the IR signatures 2,864,648 and the IR bodies 195,909,048. Raw editor and private files can include source positions. The compiler comparison also checks the declarations and their private proof values. [Sizes by module](compiled-sizes.tsv.gz)

| Native output | Files with different bytes |
| --- | ---: |
| Public module (`.olean`) | 0 |
| IR signature (`.ir.sig`) | 0 |
| IR body (`.ir`) | 0 |
| Editor metadata (`.olean.server`) | 11,550 |
| Private module (`.olean.private`) | 8,304 |

The archive index records the ID, byte size, workflow run and SHA-256 that GitHub assigned to each original ZIP. The independent release check joined the module rows with the published Git source pairs, current official owners and the separate declaration census. The five final theorems have their own test against the integrated project inputs. [Original producer ZIPs](producer-archives/github-archives.json) · [Release cross-check](independent-release-check.json) · [Five final theorems](../five-theorems)

The native records cover 133,945 warning occurrences after source positions are removed. Per-module multiset digests are available for 11,551 rows.
