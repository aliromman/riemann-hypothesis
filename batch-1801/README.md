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

## Ordinary compiler results

Stock Lake completed 9 groups with 842 distinct project modules on this revision. An independent read of each candidate and community compiler output compared 21,266 declaration occurrences, including private proof values, and 2,176 normalized warnings. Each group also passed a second Lake invocation with compilation disabled. The workload includes 567 edited modules. Some outputs came from valid compiler caches. [Per-module results](ordinary-progress/rows.jsonl.gz) · [Lake invocations](ordinary-progress/lake-invocations.json)

Generated C in this workload went from 25,016,191 to 16,423,428 bytes. Direct Mathlib initializer calls went from 60,128 to 27,906. The signed change in private compiler file size was +104,312 bytes. These figures cover the listed modules. Whole-project time remains unmeasured. [Measurements for all five compiler facets](ordinary-progress/summary.json)

The edited modules own 869,463 declaration occurrences in the community build. The index gives their Lean names and kinds by module. [Declaration ownership](declaration-owners/manifest.json) [Directory review commits](directory-review.md)

## Five final claims

The updated ClaimStrip and MainConclusion providers and Main were compiled from the published revision. Their fifteen compiler files match the community originals. Lean accepted the five final proof terms and rejected a replacement proof of `True`. All five axiom sets contain only `propext`, `Quot.sound` and `Classical.choice`. The two independent frozen statement exports also reproduce the community CI hashes. [Proof terms and negative control](projected-input-five-theorems/roots/replay.log) · [Axioms](projected-input-five-theorems/roots/axioms.log) · [Frozen statement exports](frozen-statements.json)

This endpoint check used expected compiled public inputs for 58,917 project modules. Actual ordinary Lake output matched the expected public and IR files for the 266 modules available when the archive was sealed. A complete build must still establish the remaining inputs at this revision. The standard Linux Comparator with its independent checker remains outstanding. [Input coverage](projected-input-five-theorems/latest-native-evidence.json) · [Reproduce the endpoint comparison](projected-input-five-theorems/REVIEW-projected-Main.md) · [Root compiler files and logs](projected-input-five-theorems/projected-inputs-darwin-five-roots-f390b4d81f818a3174ffc7fc0154c0d7369c08f2.zip)

The archive records source-compilation evidence for 8,503 of 38,943 edited modules. The transfer audit checks both the Git source and the effective compiled inputs for each earlier result. A second kernel invocation opened Main from the sealed archive, authenticated the 58,917 loaded project images and reproduced the accepted and rejected proofs. [Source transfer audit](module-comparison/verified.json) · [Per-source results](module-comparison/reused-native-source-rows.jsonl.gz) · [Independent archive replay](projected-input-five-theorems/independent-archive-replay.json)
