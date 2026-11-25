# PR #879 on community batch 11

The candidate is `f390b4d81f818a3174ffc7fc0154c0d7369c08f2`, based on community commit `c40250a50104b7e02e7d74f658d00fa7b1f4827c`. It uses Lean 4.37.0-rc1 and Mathlib `31ce06eaadf4a200c0e1407c5f10953cf606b8f8`. The integration keeps the new proof sources from batch #1801. [Upstream batch](https://github.com/leanprover-community/riemann-hypothesis/pull/1801) · [Integration by file](upstream-integration.jsonl.gz)

Removing 1,014,268 private Mathlib imports and adding 380 narrower imports saves 1,013,888 Lean code lines in 38,943 files. Every byte after the imports matches the new community source. Its extractor recovers the same 58,601 members from all 9,237 clumps in this diff. [Imports removed and retained](header-audit.json) · [Narrower providers](narrower-providers.json)

| Under `src/` | Community | Candidate |
| --- | ---: | ---: |
| Nonblank Lean lines | 13,984,697 | 12,970,809 |
| Physical Lean lines | 15,690,442 | 14,676,554 |
| Lean source bytes | 1,042,380,208 | 992,458,164 |
| Lean files | 59,790 | 59,790 |

The two PRs edit 41,334 distinct Lean files. A byte comparison of the Git merge confirms that each of the 9,136 shared files has the import block from #879 and the clump body from #977. The combined tree has 12,588,049 nonblank Lean lines, 1,396,648 fewer than community main. [Source totals](source-trees.json) · [Git merge comparison](composition.json)

The project source graph contains 59,789 compiled module targets and 367,287 project import edges. Outside the edited files, 2,559 modules import an edited file directly and 10,314 depend on one at any depth. Both candidates keep the complete source and pins of the five theorem statements, their two immediate providers and Main from this community revision.  The two frozen statement exports also match the community CI hashes. The full source census, default build and full solution Comparator are separate checks. Whole-project compile time is unmeasured. [Dependencies](dependencies.json) · [Protected inputs](protected-inputs.json) · [Frozen statement exports](frozen-statements.json)
