# Native compiler comparisons

PR #977 edits 11,579 modules at `f3e19bf8371ab5dd383b81e008ec14c4b0331811`. Its community parent is `bb9476b875a219608a9068f8f18d8c56b4e7f1ca`. The pinned compiler is Lean 4.37.0-rc1 at `0b77e12952ad`. Mathlib is pinned at `31ce06eaadf4`. The parent cache receipt binds the original compiler outputs. [Source pairs](../binding.json) · [Community receipt](https://rh-cache.taucetiproject.org/ci/revisions/bb9476b875a219608a9068f8f18d8c56b4e7f1ca.json)

The current native jobs re-elaborated 7,799 changed modules. Another 3,780 source pairs have earlier native comparisons. Reuse requires identical original and proposed source bytes, the identical whole owning archive and identical effective compiler inputs. Together the two groups cover all 11,579 changed modules. The checks compare 534,030 declaration occurrences, representing 529,093 distinct Lean names, including types and private proof values. They check the public import flags and the warning multisets. Each module was checked against its official parent dependencies. The integrated root check loads the selected public module outputs together. A full Lake build would also re-elaborate affected importers as required by its dependency graph. The source inventory lists the declaration names within each owner. [Native comparison by module](native-modules.jsonl.gz) · [Selection and exclusions](summary.json) · [Declaration inventory](../declarations) · [Compiler input comparison](../project-inputs)

All three ordinary compiler outputs have the same bytes in each edited module. Across these modules the public images occupy 3,240,658,104 bytes, the IR signatures 2,871,592 and the IR bodies 201,700,272. Raw editor and private files can include source positions. The compiler comparison also checks the declarations and their private proof values. [Sizes by module](compiled-sizes.tsv.gz)

| Native output | Files with different bytes |
| --- | ---: |
| Public module (`.olean`) | 0 |
| IR signature (`.ir.sig`) | 0 |
| IR body (`.ir`) | 0 |
| Editor metadata (`.olean.server`) | 11,578 |
| Private module (`.olean.private`) | 8,325 |

The archive index records the ID, byte size, workflow run and SHA-256 that GitHub assigned to each original ZIP. The independent release check joined the module rows with the published Git source pairs, current official owners and the separate declaration census. The five final theorems have their own test against the integrated project inputs. [Original producer ZIPs](producer-archives/github-archives.json) · [Release cross-check](independent-release-check.json) · [Five final theorems](../five-theorems)
