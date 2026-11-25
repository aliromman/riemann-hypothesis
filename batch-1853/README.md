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
