# PR #879 on community batch 10

The candidate is `c8612c024cfc12b0aa89ca2553f33ca5af8aa9ee`, based on community commit `4a5b4a2d2a5177a2b6cb876425f0cb4cb6b85061`. It uses Lean 4.37.0-rc1 and Mathlib `31ce06eaadf4a200c0e1407c5f10953cf606b8f8`. The integration keeps the new proof sources from batch #1739. [Upstream batch](https://github.com/leanprover-community/riemann-hypothesis/pull/1739) · [Integration by file](upstream-integration.jsonl.gz)

Removing 1,014,406 private Mathlib imports and adding 380 narrower imports saves 1,014,026 Lean code lines in 38,948 files. Every byte after the imports matches the new community source. Its extractor recovers the same 58,604 members from all 9,237 clumps in this diff. [Imports removed and retained](header-audit.json) · [Narrower providers](narrower-providers.json)

| Under `src/` | Community | Candidate |
| --- | ---: | ---: |
| Nonblank Lean lines | 14,004,007 | 12,989,981 |
| Physical Lean lines | 15,711,430 | 14,697,404 |
| Lean source bytes | 1,043,725,816 | 993,796,986 |
| Lean files | 59,807 | 59,807 |

The two PRs edit 41,342 distinct Lean files. A byte comparison of the Git merge confirms that each of the 9,136 shared files has the import block from #879 and the clump body from #977. The combined tree has 12,607,145 nonblank Lean lines, 1,396,862 fewer than community main. [Source totals](source-trees.json) · [Git merge comparison](composition.json)

The project source graph contains 59,806 compiled module targets and 367,370 project import edges. Outside the edited files, 2,571 modules import an edited file directly and 10,325 depend on one at any depth. Both candidates keep the complete source and pins of the five theorem statements, their two immediate providers and Main from this community revision. Four newly changed source pairs have an independent compiler result covering 77 declarations and their proof values. The two frozen statement exports also match the community CI hashes. The full source census, default build and full solution Comparator are separate checks. Whole-project compile time is unmeasured. [Dependencies](dependencies.json) · [Protected inputs](protected-inputs.json) · [Four initial compiler results](current-initial-native.json) · [Frozen statement exports](frozen-statements.json)
