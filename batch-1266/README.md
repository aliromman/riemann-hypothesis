# Batch 7 source and proof inputs for PR #879

Community [batch #1266](https://github.com/leanprover-community/riemann-hypothesis/pull/1266) merged as `307cef33f046955ee79dba47e0d828d06496d75f`. This record covers `e0a0acde813bd368786947b98704ee6814656a15`. The project pins Lean 4.37.0-rc1 and Mathlib `31ce06eaadf4`. The successful community receipt identifies the source tree and compiler archives for all 59,883 build targets. [Community receipt](https://rh-cache.taucetiproject.org/ci/revisions/307cef33f046955ee79dba47e0d828d06496d75f.json) · [Original and proposed proof inputs](protected-inputs.json)

The import edit removes 1,015,894 private Mathlib imports and adds 381 narrower replacements across 39,007 existing Development modules. Each file has exactly the same bytes after the import block. The existing community extractor recovers the same 58,795 original members across all 9,253 edited clumps. [Source totals](source-audit.json)

| Under `src/` | Official main | Proposed |
| --- | ---: | ---: |
| Nonblank Lean lines | 14,296,783 | 13,281,270 |
| Physical Lean lines | 16,019,664 | 15,004,151 |
| Lean source bytes | 1,059,050,861 | 1,009,049,225 |
| Lean files | 59,884 | 59,884 |

Batch 7 changed 114 retained files in this proposal and deleted 14 that appeared in the previous PR revision. The new proposal keeps every deletion. All other selected source pairs agree with the prior integration. A preview made before the community merge reproduced the surviving source bytes. [Integrated source pairs](integrated-source-pairs.json) · [Earlier batch preview](coordination/batch7-before-merge.json)

The project graph has 367,957 imports. Among untouched files, 2,565 import an edited module directly and 10,394 depend on one transitively. [Dependency counts](dependencies.json)

Together the two proposals change 41,403 Lean sources. On each of the 9,152 shared paths the joint tree combines the import proposal's header and the scope proposal's body. The combined tree has 12,898,659 nonblank Lean lines, 1,398,124 fewer than community main. [Combined tree](composition.json) · [Complete shared-path comparison](composition-source.jsonl.gz)

The full default-target Lake build and the full sandboxed five-theorem solution export require community infrastructure. Whole-project compilation time is unmeasured.

## Reviewer measurements

The fork records the ordinary Lake workloads, their timing limits and the source proof checked in the default sandbox. The combined PR tree has a separate compilation panel. [Ordinary build and sandbox measurements](bounded-checks.md) · [Both patches together](composition-native) · [Conflicts with current open PRs](coordination) · [List of affected declarations](declarations)
