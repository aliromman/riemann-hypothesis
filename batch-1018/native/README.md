# Native compiler comparisons

PR #879 edits 39,137 modules at `9e72b7b093ae4dabd1bb89f14fc9e8885c5aad5c`. Its community parent is `c6d67c05b648be9f1993aa84bd32c29ea9d2fb72`. The pinned compiler is Lean 4.37.0-rc1 at `0b77e12952ad`. Mathlib is pinned at `31ce06eaadf4`. The parent cache receipt binds the original compiler outputs. [Source pairs](../binding.json) · [Community receipt](https://rh-cache.taucetiproject.org/ci/revisions/c6d67c05b648be9f1993aa84bd32c29ea9d2fb72.json)

The current native jobs re-elaborated 23,261 changed modules. Another 15,876 source pairs have earlier native comparisons. Reuse requires identical original and proposed source bytes, the identical whole owning archive and identical effective compiler inputs. Together the two groups cover all 39,137 changed modules. The checks compare 882,067 declaration occurrences, representing 865,957 distinct Lean names, including types and private proof values. They check the public import flags and the warning multisets. Each module was checked against its official parent dependencies. The integrated root check loads the selected public module outputs together. A full Lake build would also re-elaborate affected importers as required by its dependency graph. The source inventory lists the declaration names within each owner. [Native comparison by module](native-modules.jsonl.gz) · [Selection and exclusions](summary.json) · [Declaration inventory](../declarations) · [Compiler input comparison](../project-inputs)

The public module, IR signature and IR body occupy **7,169,385,048 → 6,788,572,416 bytes** across the changed modules. Both the public module and the IR body shrink in every owner. The IR signatures have the same bytes. For each source pair, a second reader serialized the expected import arrays and checked the observed compiler digests. The byte count covers these three outputs. [Sizes by module](compiled-sizes.tsv.gz) · [Output digests](compiled-images.jsonl.gz) · [Distribution](size-distribution.json)

| Native output | Files with different bytes |
| --- | ---: |
| Public module (`.olean`) | 39,137 |
| IR signature (`.ir.sig`) | 0 |
| IR body (`.ir`) | 39,137 |
| Editor metadata (`.olean.server`) | 39,137 |
| Private module (`.olean.private`) | 39,127 |

The archive index records the ID, byte size, workflow run and SHA-256 that GitHub assigned to each original ZIP. The independent release check joined the module rows with the published Git source pairs, current official owners and the separate declaration census. The five final theorems have their own test against the integrated project inputs. [Original producer ZIPs](producer-archives/github-archives.json) · [Release cross-check](independent-release-check.json) · [Five final theorems](../five-theorems)
