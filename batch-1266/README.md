# Batch 7 source and proof inputs for PR #977

Community [batch #1266](https://github.com/leanprover-community/riemann-hypothesis/pull/1266) merged as `307cef33f046955ee79dba47e0d828d06496d75f`. This record covers `963ebea3bb3d7c2c5738946fca45317b8084f972`. The project pins Lean 4.37.0-rc1 and Mathlib `31ce06eaadf4`. The successful community receipt identifies the source tree and compiler archives for all 59,883 build targets. [Community receipt](https://rh-cache.taucetiproject.org/ci/revisions/307cef33f046955ee79dba47e0d828d06496d75f.json) · [Original and proposed proof inputs](protected-inputs.json)

The optimized renderer removes 251,315 Lean scope commands from 11,548 proof clumps. The edited archives contain 68,221 original members. It joins 24,504 compatible public and noncomputable sections. Another 131,296 standalone comment lines disappear. Charging all 448 net Python lines, including the new tests, leaves 250,867 fewer lines of code. [Command categories](scope-command-counts.json) · [Per-clump source comparison](scope-source-rows.jsonl.gz) [Source totals](source-audit.json)

| Under `src/` | Official main | Proposed |
| --- | ---: | ---: |
| Nonblank Lean lines | 14,296,783 | 13,914,172 |
| Physical Lean lines | 16,019,664 | 15,626,490 |
| Lean source bytes | 1,059,050,861 | 1,038,308,572 |
| Lean files | 59,884 | 59,884 |

Batch 7 changed 484 retained files in this proposal and deleted 3 that appeared in the previous PR revision. The new proposal keeps every deletion. All other selected source pairs agree with the prior integration. A preview made before the community merge reproduced the surviving source bytes. [Integrated source pairs](integrated-source-pairs.json) · [Earlier batch preview](coordination/batch7-before-merge.json)

The project graph has 367,957 imports. Among untouched files, 9,881 import an edited module directly and 30,400 depend on one transitively. [Dependency counts](dependencies.json)

Together the two proposals change 41,403 Lean sources. On each of the 9,152 shared paths the joint tree combines the import proposal's header and the scope proposal's body. The combined tree has 12,898,659 nonblank Lean lines, 1,398,124 fewer than community main. [Combined tree](composition.json) · [Complete shared-path comparison](composition-source.jsonl.gz)

The full default-target Lake build and the full sandboxed five-theorem solution export require community infrastructure. Whole-project compilation time is unmeasured.

The plan command reads the full project and retains just imports, declaration names, sizes and exclusion flags. The apply command reads only the members in its saved plan. The real stock tool used for the previous whole-checkout measurements has the same two Python source blobs as this proposal. The current source census rechecked every planner input. [Planner source binding](planner/source-binding.json) · [Current inputs and output digests](planner/input-equality.json)

## Archive recovery

The two tools recovered identical bytes in the same order for 73,049 members across all 12,359 extractable archives. All 11,548 edited archives have that property. One other legacy archive already fails extraction on the unchanged community source. It contains local instances between the first member marker and the stored header. Those instances take effect outside the member section. The evidence records the file, the source hash and the original error. [Archive comparison](archive-reads.json) · [Per-file records](archive-reads.jsonl.gz)

## Reviewer measurements

The fork records the ordinary Lake workloads, their timing limits and the source proof checked in the default sandbox. The combined PR tree has a separate compilation panel. [Ordinary build and sandbox measurements](bounded-checks.md) · [Both patches together](composition-native) · [Conflicts with current open PRs](coordination) · [List of affected declarations](declarations)
