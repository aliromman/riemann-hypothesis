# Reversible proof clumps on the current community parent

The parent is `cb4dc6e23a6187db392c96664295415c55b6b01e`. The proposed commit is `afa44208210943a202ad969173b6317d06c37420`. The 11,579 changed Lean files contain 68,401 original members. Both readers recover each member in order with its original import header and mathematical declarations. In 24,547 member bodies the outer public section and a compatible file-wide noncomputable section become one. The verification permits that specific scope edit and compares all other member bytes. The normal clump renderer reproduces every final clump body.

The source loses 97,961 closing commands, 67,684 namespace opens, 61,633 sections and 24,547 noncomputable sections. The total is 251,825 fewer Lean commands. Removing 131,637 standalone comment lines brings the nonblank decrease to 383,462. The new renderer and its regression tests add a net 359 physical Python lines. Charging every one of those lines against the Lean command decrease still gives 251,466 fewer lines. The repository keeps all 60,630 Lean files under `src`. The source totals come from the two complete Git trees. The project keeps all 374,593 import edges. Of the untouched modules, 10,096 import an edited module directly and 30,961 do so transitively.

Set `evidence` to a checkout of this evidence branch. Run these commands in a checkout of the community repository that contains the two source commits.

```sh
python3 "$evidence/audit_source.py" cb4dc6e23a6187db392c96664295415c55b6b01e afa44208210943a202ad969173b6317d06c37420 \
  --repo . --output source-rows.jsonl.gz > source-summary.json
cmp source-summary.json "$evidence/verified/source-summary.json"
cmp source-rows.jsonl.gz "$evidence/verified/source-rows.jsonl.gz"
```

## Compiler comparisons

Of the 11,579 selected modules, 9,447 have fresh native comparisons with the current official parent. Another 2,132 reuse the same original and proposed source bytes, owning module and effective compiler inputs from an earlier comparison. All 534,023 module-local declaration records agree on names, types and values. They include 487,250 theorem occurrences. Full public module files and both IR files match for all 11,579 modules, which gives 34,737 raw SHA-256 pairs. Every normalized warning multiset agrees. The private and server files contain additional compiler data, including positions. Their raw bytes differ for 8,381 and 11,578 modules respectively. See the recorded digests and actual declarations in the per-module tables. [Native jobs](https://github.com/aliromman/riemann-hypothesis/actions/runs/45366025067)

Sixty-seven retained upstream files avoid conflicts with other active proposals. One additional clump passed the comparison of all 75 declarations and emitted the same warnings, but its raw IR differed. The pinned compiler moved the arguments of a join block in `Formalism.MainNotions.G.SymmetricFormBlocks.fL`. Applying just that permutation to the original IR reproduces the proposed bytes. The published branch keeps the entire upstream file. The earlier selection also held back examples in which source offsets changed private proof terms. [IR inspection and replay](excluded-compiler-change/diagnosis.json)

The stock Linux sample contains 27 roots and 239 project modules, including the sources of two independently exported theorems. A four-module target rebuilt from an empty project build directory had median wall time 11.723 → 11.699 seconds. One of the five measured pairs was slower. Across 12 individual changed files, the sums of median CPU times were 53.133 → 52.998 seconds. Three files had a higher CPU median. The sample establishes little change in Lean compilation time. The full default-target Lake build and the full five-theorem independent Comparator export remain outstanding. [Stock Lake, independent exports and current input checks](https://github.com/aliromman/riemann-hypothesis/tree/fb366e03e85d06f6151b946212783af4df6de409/ci/stock-batch-896/results/45366826111/)

## Tool and integration checks

The project test runner discovered 277 tests, with one skip. Its separate build-queue runner suite discovered nine tests, with four platform skips. The two CLI logs use paths relative to the temporary test repository. Two real command-line examples cover a dotted quoted name and a name containing a space followed by a Lean comment. Each test runs the planner, applies the plan, compiles the merged module and its downstream user, and recovers the two input files. The full planner comparison covers 60,630 modules. After publication, 841 clumps gained another 4,490 command lines of savings, including 4,098 opens. [Planner and source record](scope-refinements.json)

The Python timing result is filtered from the original full-corpus experiment to the exact 11,579 retained source pairs. It uses five alternating measured pairs and excludes the warm-up. Summing per-file CPU medians gives 1.759 → 1.707 seconds to extract the members and 3.589 → 5.540 seconds to render the clumps. The additional rendering work costs 1.951 CPU seconds over this selection. The full input and output are checked outside the timer. [Original paired observations](https://github.com/aliromman/riemann-hypothesis/blob/9402ee4f659b05304b4769f8a6b24a02fba47ebd/review-73958/tool-observations.jsonl.gz)

Both proposed Git trees merge cleanly. All 9,179 common files equal the private import header from #879 followed by this branch's clump body. The combined 18-root compiler sample covers 51 modules, 2,211 declarations and 153 public/IR digest pairs. Scope-only and import-only verification apply independently to the two PRs. [Combined source records](composition-source.jsonl.gz)

The recorded Git merges cover the focused contributors whose files were reserved, the new integration batches and the wide proof-name cleanup. PR #988 is a separate decision for the maintainers. Its one-way format strips the original import records from every changed clump and removes extraction. The final source and that proposal have 11,579 file conflicts plus one tool conflict. The footer holds 170,403,384 bytes on these paths, including line endings. Filtering out those records leaves every active command in this branch intact. [Compared archive layouts](archive-proposal.json) · [One-way format proposal](https://github.com/leanprover-community/riemann-hypothesis/pull/988)
