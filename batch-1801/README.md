# PR #977 on community batch 11

The candidate is `c0d14da69d2c6b5f0335680d7c3b6541acc95c29`, based on community commit `c40250a50104b7e02e7d74f658d00fa7b1f4827c`. It uses Lean 4.37.0-rc1 and Mathlib `31ce06eaadf4a200c0e1407c5f10953cf606b8f8`. The integration keeps the new proof sources from batch #1801. [Upstream batch](https://github.com/leanprover-community/riemann-hypothesis/pull/1801) · [Integration by file](upstream-integration.jsonl.gz)

The clump tool removes 251,970 Lean scope commands and 130,790 standalone comment lines. Counting all 448 net Python lines added to the tool and tests leaves 251,522 fewer code lines. Of 68,024 recovered members, 43,609 match upstream byte for byte and 24,415 combine the outer public and noncomputable sections. Every declaration and tactic line matches the community version. The compatibility check reads all 59,790 Lean source files and compares the rendered output for all 12,325 extractable archives. One unedited legacy file fails in the community reader. [Scope commands and physical line counts](scope-source-counts.json) · [Member comparisons](scope-member-differences.json) · [Archive compatibility](archive-reads.json)

| Under `src/` | Community | Candidate |
| --- | ---: | ---: |
| Nonblank Lean lines | 13,984,697 | 13,601,937 |
| Physical Lean lines | 15,690,442 | 15,296,640 |
| Lean source bytes | 1,042,380,208 | 1,021,531,693 |
| Lean files | 59,790 | 59,790 |

The two PRs edit 41,334 distinct Lean files. A byte comparison of the Git merge confirms that each of the 9,136 shared files has the import block from #879 and the clump body from #977. The combined tree has 12,588,049 nonblank Lean lines, 1,396,648 fewer than community main. [Source totals](source-trees.json) · [Git merge comparison](composition.json)

The project source graph contains 59,789 compiled module targets and 367,287 project import edges. Outside the edited files, 9,850 modules import an edited file directly and 30,352 depend on one at any depth. Both candidates keep the complete source and pins of the five theorem statements, their two immediate providers and Main from this community revision.  The two frozen statement exports also match the community CI hashes. The full source census, default build and full solution Comparator are separate checks. Whole-project compile time is unmeasured. [Dependencies](dependencies.json) · [Protected inputs](protected-inputs.json) · [Frozen statement exports](frozen-statements.json)

## Ordinary compiler results

Stock Lake completed 4 groups with 525 distinct project modules on this revision. An independent read of each candidate and community compiler output compared 19,355 declaration occurrences, including private proof values, and 1,545 normalized warnings. Each group also passed a second Lake invocation with compilation disabled. The workload includes 36 edited modules. Some outputs came from valid compiler caches. [Per-module results](ordinary-progress/rows.jsonl.gz) · [Lake invocations](ordinary-progress/lake-invocations.json)

Generated C in this workload went from 14,022,220 to 14,022,220 bytes. Direct Mathlib initializer calls went from 23,776 to 23,776. The signed change in private compiler file size was +0 bytes. These figures cover the listed modules. Whole-project time remains unmeasured. [Measurements for all five compiler facets](ordinary-progress/summary.json)

The edited modules own 527,619 declaration occurrences in the community build. The index gives their Lean names and kinds by module. [Declaration ownership](declaration-owners/manifest.json)

## Five final claims

The updated ClaimStrip and MainConclusion providers and Main were compiled from the published revision. Their fifteen compiler files match the community originals. Lean accepted the five final proof terms and rejected a replacement proof of `True`. All five axiom sets contain only `propext`, `Quot.sound` and `Classical.choice`. The two independent frozen statement exports also reproduce the community CI hashes. [Proof terms and negative control](projected-input-five-theorems/roots/replay.log) · [Axioms](projected-input-five-theorems/roots/axioms.log) · [Frozen statement exports](frozen-statements.json)

This endpoint check used expected compiled public inputs for 58,917 project modules. Actual ordinary Lake output matched the expected public and IR files for the 525 modules available when the archive was sealed. A complete build must still establish the remaining inputs at this revision. The standard Linux Comparator with its independent checker remains outstanding. [Input coverage](projected-input-five-theorems/latest-native-evidence.json) · [Reproduce the endpoint comparison](projected-input-five-theorems/REVIEW-projected-Main.md) · [Root compiler files and logs](projected-input-five-theorems/projected-inputs-darwin-five-roots-c0d14da69d2c6b5f0335680d7c3b6541acc95c29.zip)

The archive records source-compilation evidence for 1,734 of 11,527 edited modules. The transfer audit checks both the Git source and the effective compiled inputs for each earlier result. A second kernel invocation opened Main from the sealed archive, authenticated the 58,917 loaded project images and reproduced the accepted and rejected proofs. [Source transfer audit](module-comparison/verified.json) · [Per-source results](module-comparison/reused-native-source-rows.jsonl.gz) · [Independent archive replay](projected-input-five-theorems/independent-archive-replay.json)
