# PR #977 on community batch 10

The candidate is `9b5b3c860537e95becc28e23c767b6a7c4053aa6`, based on community commit `4a5b4a2d2a5177a2b6cb876425f0cb4cb6b85061`. It uses Lean 4.37.0-rc1 and Mathlib `31ce06eaadf4a200c0e1407c5f10953cf606b8f8`. The integration keeps the new proof sources from batch #1739. [Upstream batch](https://github.com/leanprover-community/riemann-hypothesis/pull/1739) · [Integration by file](upstream-integration.jsonl.gz)

The clump tool removes 252,020 Lean scope commands and 130,816 standalone comment lines. Counting all 448 net Python lines added to the tool and tests leaves 251,572 fewer code lines. Of 68,037 recovered members, 43,613 match upstream byte for byte and 24,424 combine the outer public and noncomputable sections. Every declaration and tactic line matches the community version. The compatibility check reads all 59,807 Lean source files and compares the rendered output for all 12,331 extractable archives. One unedited legacy file fails in the community reader. [Scope commands and physical line counts](scope-source-counts.json) · [Member comparisons](scope-member-differences.json) · [Archive compatibility](archive-reads.json)

| Under `src/` | Community | Candidate |
| --- | ---: | ---: |
| Nonblank Lean lines | 14,004,007 | 13,621,171 |
| Physical Lean lines | 15,711,430 | 15,317,554 |
| Lean source bytes | 1,043,725,816 | 1,022,874,073 |
| Lean files | 59,807 | 59,807 |

The two PRs edit 41,342 distinct Lean files. A byte comparison of the Git merge confirms that each of the 9,136 shared files has the import block from #879 and the clump body from #977. The combined tree has 12,607,145 nonblank Lean lines, 1,396,862 fewer than community main. [Source totals](source-trees.json) · [Git merge comparison](composition.json)

The project source graph contains 59,806 compiled module targets and 367,370 project import edges. Outside the edited files, 9,856 modules import an edited file directly and 30,359 depend on one at any depth. Both candidates keep the complete source and pins of the five theorem statements, their two immediate providers and Main from this community revision. Four newly changed source pairs have an independent compiler result covering 73 declarations and their proof values. The two frozen statement exports also match the community CI hashes. The full source census, default build and full solution Comparator are separate checks. Whole-project compile time is unmeasured. [Dependencies](dependencies.json) · [Protected inputs](protected-inputs.json) · [Four initial compiler results](current-initial-native.json) · [Frozen statement exports](frozen-statements.json)

## Ordinary compiler results

Stock Lake completed 1 groups with 237 distinct project modules on this revision. An independent read of each candidate and community compiler output compared 7,495 declaration occurrences, including private proof values, and 823 normalized warnings. Each group also passed a second Lake invocation with compilation disabled. The workload includes 29 edited modules. Some outputs came from valid compiler caches. [Per-module results](ordinary-progress/rows.jsonl.gz) · [Lake invocations](ordinary-progress/lake-invocations.json)

Generated C in this workload went from 4,151,064 to 4,151,064 bytes. Direct Mathlib initializer calls went from 5,222 to 5,222. The signed change in private compiler file size was +0 bytes. These figures cover the listed modules. Whole-project time remains unmeasured. [Measurements for all five compiler facets](ordinary-progress/summary.json)

The edited modules own 528,521 declaration occurrences in the community build. The index gives their Lean names and kinds by module. [Declaration ownership](declaration-owners/manifest.json)

## Five final claims

The updated ClaimStrip and MainConclusion providers and Main were compiled from the published revision. Their fifteen compiler files match the community originals. Lean accepted the five final proof terms and rejected a replacement proof of `True`. All five axiom sets contain only `propext`, `Quot.sound` and `Classical.choice`. The two independent frozen statement exports also reproduce the community CI hashes. [Proof terms and negative control](projected-input-five-theorems/roots/replay.log) · [Axioms](projected-input-five-theorems/roots/axioms.log) · [Frozen statement exports](frozen-statements.json)

This endpoint check used expected compiled public inputs for 58,932 project modules. Actual ordinary Lake output matched the expected public and IR files for the 237 modules in the recorded workload. A complete build must still establish the remaining inputs at this revision. The standard Linux Comparator with its independent checker remains outstanding. [Input coverage](projected-input-five-theorems/latest-native-evidence.json) · [Reproduce the endpoint comparison](projected-input-five-theorems/REVIEW-projected-Main.md) · [Root compiler files and logs](projected-input-five-theorems/projected-inputs-darwin-five-roots-9b5b3c860537e95becc28e23c767b6a7c4053aa6.zip)

The source and compiler-input comparison covers 1,662 of 11,530 edited modules at this checkpoint. It includes 1,548 earlier checks with matching source and compiler inputs, 103 isolated compilations and 11 additional ordinary build results. The checkpoint records 0 nonpassing observations. Other modules still need a comparison. [Exact counts and scope](module-comparison/readback.json) · [Results by module](module-comparison/native-modules.jsonl.gz)
