# PR #879 on community batch 12

The candidate is `fc7da07ee956d37af90da7e0bf4bae68dc5795a9`, based on community commit `fcb6eac7534875d32d68030967e2deae6d686151`. It uses Lean 4.37.0-rc1 and Mathlib `31ce06eaadf4a200c0e1407c5f10953cf606b8f8`. The integration keeps the new proof sources from batch #1853. [Upstream batch](https://github.com/leanprover-community/riemann-hypothesis/pull/1853) · [Integration by file](upstream-integration.jsonl.gz)

Removing 1,013,356 private Mathlib imports and adding 379 narrower imports saves 1,012,977 Lean code lines in 38,910 files. Every byte after the imports matches the new community source. Its extractor recovers the same 58,556 members from all 9,231 clumps in this diff. [Imports removed and retained](header-audit.json) · [Narrower providers](narrower-providers.json)

| Under `src/` | Community | Candidate |
| --- | ---: | ---: |
| Nonblank Lean lines | 13,954,393 | 12,941,416 |
| Physical Lean lines | 15,656,672 | 14,643,695 |
| Lean source bytes | 1,040,474,062 | 990,596,665 |
| Lean files | 59,764 | 59,764 |

The two PRs edit 41,301 distinct Lean files. A byte comparison of the Git merge confirms that each of the 9,130 shared files has the import block from #879 and the clump body from #977. The combined tree has 12,558,897 nonblank Lean lines, 1,395,496 fewer than community main. [Source totals](source-trees.json) · [Git merge comparison](composition.json)

The project source graph contains 59,763 compiled module targets and 367,146 project import edges. Outside the edited files, 2,554 modules import an edited file directly and 10,310 depend on one at any depth. Both candidates keep the complete source and pins of the five theorem statements, their two immediate providers and Main from this community revision.  The two frozen statement exports also match the community CI hashes. The full source census, default build and full solution Comparator are separate checks. Whole-project compile time is unmeasured. [Dependencies](dependencies.json) · [Protected inputs](protected-inputs.json) · [Frozen statement exports](frozen-statements.json)

## Ordinary compiler results

Stock Lake completed 2 groups with 170 distinct project modules on this revision. An independent read of each candidate and community compiler output compared 6,368 declaration occurrences, including private proof values, and 428 normalized warnings. Each group also passed a second Lake invocation with compilation disabled. The workload includes 67 edited modules. Some outputs came from valid compiler caches. [Per-module results](ordinary-progress/rows.jsonl.gz) · [Lake invocations](ordinary-progress/lake-invocations.json)

Generated C in this workload went from 5,492,787 to 4,475,058 bytes. Direct Mathlib initializer calls went from 8,460 to 4,644. The signed change in private compiler file size was +14,656 bytes. These figures cover the listed modules. Whole-project time remains unmeasured. [Measurements for all five compiler facets](ordinary-progress/summary.json)

The edited modules own 866,681 declaration occurrences in the community build. The index gives their Lean names and kinds by module. [Declaration ownership](declaration-owners/manifest.json) [Directory review commits](directory-review.md)

## Direct source compilation

Lean compiled the revised `BlockSymApply` source against authenticated compiler inputs for this revision. All 2 declarations, their proof terms and the compiler warnings matched the community version. [Source comparison](current-initial-native.json)

The current WeilBound commit edits 2,858 files. The complete upstream source of `PureTypeLatticesOrthogonal.lean` is present on both sides of the diff. Of the remaining paths, 2,778 retain both source blobs from the reviewer's earlier commit and 80 have updated sources. [Reviewer audit](https://github.com/leanprover-community/riemann-hypothesis/pull/879#issuecomment-7150958950) · [Source changes since the review](weilbound-review-transition.json) · [Directory commits](directory-review.md)
