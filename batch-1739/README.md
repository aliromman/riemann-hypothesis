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

## Ordinary compiler results

Stock Lake completed 8 groups with 746 distinct project modules on this revision. An independent read of each candidate and community compiler output compared 20,360 declaration occurrences, including private proof values, and 1,918 normalized warnings. Each group also passed a second Lake invocation with compilation disabled. The workload includes 490 edited modules. Some outputs came from valid compiler caches. [Per-module results](ordinary-progress/rows.jsonl.gz) · [Lake invocations](ordinary-progress/lake-invocations.json)

Generated C in this workload went from 22,537,613 to 15,111,293 bytes. Direct Mathlib initializer calls went from 52,324 to 24,474. The signed change in private compiler file size was +91,264 bytes. These figures cover the listed modules. Whole-project time remains unmeasured. [Measurements for all five compiler facets](ordinary-progress/summary.json)

The edited modules own 870,830 declaration occurrences in the community build. The index gives their Lean names and kinds by module. [Declaration ownership](declaration-owners/manifest.json) [Directory review commits](directory-review.md)

## Five final claims

The updated ClaimStrip and MainConclusion providers and Main were compiled from the published revision. Their fifteen compiler files match the community originals. Lean accepted the five final proof terms and rejected a replacement proof of `True`. All five axiom sets contain only `propext`, `Quot.sound` and `Classical.choice`. The two independent frozen statement exports also reproduce the community CI hashes. [Proof terms and negative control](projected-input-five-theorems/roots/replay.log) · [Axioms](projected-input-five-theorems/roots/axioms.log) · [Frozen statement exports](frozen-statements.json)

This endpoint check used expected compiled public inputs for 58,932 project modules. Actual ordinary Lake output matched the expected public and IR files for the 746 modules in the recorded workload. A complete build must still establish the remaining inputs at this revision. The standard Linux Comparator with its independent checker remains outstanding. [Input coverage](projected-input-five-theorems/latest-native-evidence.json) · [Reproduce the endpoint comparison](projected-input-five-theorems/REVIEW-projected-Main.md) · [Root compiler files and logs](projected-input-five-theorems/projected-inputs-darwin-five-roots-c8612c024cfc12b0aa89ca2553f33ca5af8aa9ee.zip)

The source and compiler-input comparison covers 8,343 of 38,948 edited modules at this checkpoint. It includes 8,043 earlier checks with matching source and compiler inputs, 293 isolated compilations and 7 additional ordinary build results. The checkpoint records 0 nonpassing observations. Other modules still need a comparison. [Exact counts and scope](module-comparison/readback.json) · [Results by module](module-comparison/native-modules.jsonl.gz)
