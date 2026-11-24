# Community batch 6 and PR #879

The community merged batch #1198 as `1da818b50f1e18808db2792b9dc735bda8cb84d8`. The proposed commit is `ac3ff4bec1bf43a091eb6721e12eaf40a592cb9d`. The project uses Lean 4.37.0-rc1 and Mathlib `31ce06eaadf4`. The official receipt authenticates 59,908 project modules. [Community batch](https://github.com/leanprover-community/riemann-hypothesis/pull/1198) · [Community cache receipt](https://rh-cache.taucetiproject.org/ci/revisions/1da818b50f1e18808db2792b9dc735bda8cb84d8.json) · [Parent input comparison](official-receipt-comparison.json)

The patch removes 1,016,259 private Mathlib imports and adds 382 narrower imports. It keeps every byte after the import block in 39,021 existing Development files. The community extraction tool recovers the same 58,829 original members from all 9,256 edited clumps. [Source audit](source-audit.json)

| Under `src/` | Community main | Proposed |
| --- | ---: | ---: |
| Nonblank Lean lines | 14,430,089 | 13,414,212 |
| Physical Lean lines | 16,153,947 | 15,138,070 |
| Lean source bytes | 1,065,406,229 | 1,015,386,766 |
| Lean source modules | 59,909 | 59,909 |

The new community batch changes 110 retained sources and deletes 99 others touched by the prior proposal. This revision uses each surviving community proof and preserves every deletion. The other 38,911 source pairs match the previous parent and proposal. [Integrated sources](upstream-integration.json) · [Changed source pairs](changed-source-pairs.json) · [Source preview before the community merge](coordination/prior-source-preview.json)

The graph has 368,104 project import edges. Among untouched modules, 2,574 import a changed module directly and 10,403 depend on one transitively. Both proposals together change 41,417 Lean files. All 9,155 shared files have exactly the import proposal’s header and the scope proposal’s body in the combined tree. It contains 13,031,422 nonblank Lean lines, a reduction of 1,398,667. [Dependency counts](dependencies.json) · [Combined tree](composition.json) · [Per-file comparison](composition-source.jsonl.gz)

A full default-target Lake rebuild and the full sandboxed five-theorem Comparator solution export remain community-run checks. The largest ordinary stock workload and the five-proof kernel replay use different sets of inputs.

## Compiled outputs and theorem checks

The final records cover all 39,021 changed source modules and all five declarations in `Main`. The raw ZIP files retain the original GitHub authentication digests. The upstream comparison records all paths changed since this mathematical parent and checks the two Git merge previews. [Compiled outputs](native) · [Five theorem proofs](five-theorems) · [Latest main comparison](latest-main.json)

The two proposals also share a measured compiler workload. Its input record identifies the exact joint tree and the community modules used. [Combined-source comparison](composition-native) · [Stock Lake and sandboxed source replays](bounded-checks.md) · [Cross-PR merge checks](coordination)
