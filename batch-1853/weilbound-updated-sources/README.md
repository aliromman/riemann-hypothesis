# WeilBound changes since the first review

Lean compiled the revised source of all 80 files that changed since the first review. Each run used Apple silicon and authenticated compiler inputs from batch #1853. The proposed files in PR #879 and the standalone WeilBound commit are byte-identical. The original compiler outputs came from the community cache. The checks covered 3,795 declaration occurrences and 642 warning occurrences. Every declaration, proof term, public import and warning multiset matched its community original. The candidate public and IR files also matched the expected compiler output. [All files, source blobs and results](results.json)

The six files named in the [Windows review](https://github.com/leanprover-community/riemann-hypothesis/pull/879#issuecomment-7151726569) passed with the following declaration counts.

| Source file | Declaration occurrences |
| --- | ---: |
| `NuPull.lean` | 80 |
| `PhiAIter.lean` | 170 |
| `FirstChernCompatibleL.lean` | 50 |
| `CxDataModel.lean` | 232 |
| `PlaceFacts.lean` | 23 |
| `WlocTop.lean` | 55 |

These are per-source comparisons. The full branch build and the community Linux Comparator remain separate checks. [First group](review-first/report.json) · [Second group](review-full/report.json)
