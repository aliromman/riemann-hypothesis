# PR #977 on community batch 12

The candidate is `88ac64dbb08e96f5bae2181b1c65cd84474fe5b5`, based on community commit `fcb6eac7534875d32d68030967e2deae6d686151`. It uses Lean 4.37.0-rc1 and Mathlib `31ce06eaadf4a200c0e1407c5f10953cf606b8f8`. The integration keeps the new proof sources from batch #1853. [Upstream batch](https://github.com/leanprover-community/riemann-hypothesis/pull/1853) · [Integration by file](upstream-integration.jsonl.gz)

The clump tool removes 251,813 Lean scope commands and 130,706 standalone comment lines. Counting all 448 net Python lines added to the tool and tests leaves 251,365 fewer code lines. Of 67,979 recovered members, 43,577 match upstream byte for byte and 24,402 combine the outer public and noncomputable sections. Every declaration and tactic line matches the community version. The compatibility check reads all 59,764 Lean source files and compares the rendered output for all 12,319 extractable archives. One unedited legacy file fails in the community reader. [Scope commands and physical line counts](scope-source-counts.json) · [Member comparisons](scope-member-differences.json) · [Archive compatibility](archive-reads.json)

| Under `src/` | Community | Candidate |
| --- | ---: | ---: |
| Nonblank Lean lines | 13,954,393 | 13,571,874 |
| Physical Lean lines | 15,656,672 | 15,263,124 |
| Lean source bytes | 1,040,474,062 | 1,019,634,539 |
| Lean files | 59,764 | 59,764 |

The two PRs edit 41,301 distinct Lean files. A byte comparison of the Git merge confirms that each of the 9,130 shared files has the import block from #879 and the clump body from #977. The combined tree has 12,558,897 nonblank Lean lines, 1,395,496 fewer than community main. [Source totals](source-trees.json) · [Git merge comparison](composition.json)

The project source graph contains 59,763 compiled module targets and 367,146 project import edges. Outside the edited files, 9,842 modules import an edited file directly and 30,338 depend on one at any depth. Both candidates keep the complete source and pins of the five theorem statements, their two immediate providers and Main from this community revision.  The two frozen statement exports also match the community CI hashes. The full source census, default build and full solution Comparator are separate checks. Whole-project compile time is unmeasured. [Dependencies](dependencies.json) · [Protected inputs](protected-inputs.json) · [Frozen statement exports](frozen-statements.json)

## Ordinary compiler results

Stock Lake completed 2 groups with 333 distinct project modules on this revision. An independent read of each candidate and community compiler output compared 10,627 declaration occurrences, including private proof values, and 1,068 normalized warnings. Each group also passed a second Lake invocation with compilation disabled. The workload includes 31 edited modules. Some outputs came from valid compiler caches. [Per-module results](ordinary-progress/rows.jsonl.gz) · [Lake invocations](ordinary-progress/lake-invocations.json)

Generated C in this workload went from 7,108,993 to 7,108,993 bytes. Direct Mathlib initializer calls went from 10,376 to 10,376. The signed change in private compiler file size was +0 bytes. These figures cover the listed modules. Whole-project time remains unmeasured. [Measurements for all five compiler facets](ordinary-progress/summary.json)

The edited modules own 526,512 declaration occurrences in the community build. The index gives their Lean names and kinds by module. [Declaration ownership](declaration-owners/manifest.json)

## Direct source compilation

Lean compiled the revised `LeNuIffPowMemPrinc` source against authenticated compiler inputs for this revision. All 28 declarations, their proof terms and the compiler warnings matched the community version. [Source comparison](current-initial-native.json)
