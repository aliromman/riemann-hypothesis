# Stock Lake, kernel and timing records for PR #879

GitHub checked merge `1555bcadd7a6f2570988bdeb23b5bd37cb44f924` of author head `87b887f70183a19b577c6b084a8865f04ecb69e4` and community parent `bb9476b875a219608a9068f8f18d8c56b4e7f1ca`. The candidate source tree is `95fe38ceaf8f51ec5628d748d55bd7127e1e6447`. The successful parent cache manifest is `79edef3a77b0086faf52d4f0df0a9b26b58e45826de20a57def3d5559d6ebe89`. [Original Linux run](https://github.com/aliromman/riemann-hypothesis/actions/runs/45386629388)

The stock Lake build covered 72 roots and 143 project modules. 94 modules had source changes, and 101 modules compiled from source. Across both sides the check compared 9,710 module-owned declarations, including 7,694 in changed modules. Lean replayed 3 selected roots. All compared names, types, theorem proofs, definition values, public exports and kernel declarations matched. The compiler-warning multisets matched after removal of source positions.

The import check compared the full public serialized module image after clearing the direct imports field. It compared the exported imports separately. The raw public file differed in 94 modules, the raw server file in 98, and the raw private file in 98. The source manifest records the old and new full-file SHA-256 and the numbers of imported modules added and removed for each of the 94 edited files in this scope.

For every edited source, the job loaded the verified parent `.olean`, `.ir.sig` and `.ir` into the pinned Lean serializer. It replaced only the ordered direct import list, keeping entries, constants and flags. All 282 resulting whole files matched the SHA-256 of the actual stock Linux output. The raw `.ir` digest differed in 94 modules. It carried the source import list. Each of the 94 IR signatures had an empty import table. The job read the actual old and new import items and flags in each IR part and recorded their counts. Among edited modules, raw `.olean` was 42,850,584 → 42,360,464 bytes, `.ir.sig` was 23,312 → 23,312 bytes, and `.ir` was 2,541,096 → 2,041,688 bytes. The ZIP contains every original, expected and actual SHA-256. [Earlier batch #896 raw IR diagnostic](https://github.com/aliromman/riemann-hypothesis/actions/runs/45368083272)

In the same edited modules, raw `.olean.server` was 958,248 → 959,352 bytes and `.olean.private` was 73,765,632 → 73,785,800 bytes. The declaration comparison read all three `.olean` parts and compared every private constant, proof and value. It checked the full sorted kernel declaration serialization as well. The stock theorem verifier also read both actual proof bodies.

## Bounded proof exports

The predeclared theorem targets belong to actual changed sources. Both revisions produced identical exported proof traces for each theorem. The stock Comparator checked statements with the repository’s permitted axioms `propext`, `Quot.sound` and `Classical.choice`. Lean default, Lean paranoid and nanoda accepted both targets. An alternate proof passed. The two negative controls rejected a changed statement and an added named axiom. This scope does not include a five-claim export.

- `GlobalTheory.CatCoh.commAlgFunctorCoboundaryZero_mem_cocyclesOne` used 4,888,069 bytes on each side. SHA-256 `00615d0ad579cd5a3309866b1d7e5861bfa4d6b206bf92d861a0d9b542eee332`.
- `GlobalTheory.TopForm.isBaseChange_exteriorPower` used 52,581,161 bytes on each side. SHA-256 `2dcae760dcc362b23a2aec4c37f91947c52936d0274a4d81e8d65c82812ae24e`.

## Inputs after community batch #1018

All 72 predeclared roots remained in the current project. Relative to the previous batch, 2 parent sources and 2 candidate sources in the complete panel changed. 0 parent direct import lists, 2 verified parent archives and 2 Lake input hashes changed. The job rebuilt and compared this entire panel on the current merge. [Per-root changes](previous-inputs.json)

The project inputs for both selected theorem closures and the complete fresh Lake workload match the preceding batch. The results and times below all come from the new Ubuntu job. The previous job ran on its own machine. [Earlier stock run](https://github.com/aliromman/riemann-hypothesis/actions/runs/45370408013)

Every individual timing closure retained the same parent and candidate source blobs, ordered imports, Lake input hashes and verified parent archives as the earlier batch.

## Matched single-module compiler trials

All 4 predeclared sources ran on the same Ubuntu job. Each used a warm-up pair, then five alternating matched trials with one Lean thread and a fresh output directory for each compile. Both sides used the same pinned imported artifacts. CPU is child user plus system time. Elapsed includes compilation and creation of `.olean`, `.ilean` and C output. Hydration and declaration comparison were outside the timers.

| Source | Private imports removed | Parent CPU, s | Candidate CPU, s | CPU change | Parent elapsed, s | Candidate elapsed, s | Elapsed change | Slower CPU pairs | Slower elapsed pairs |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne` | 27 | 0.671 | 0.585 | -12.83% | 0.674 | 0.591 | -12.27% | 0/5 | 0/5 |
| `Development.AbelianVarietyTheory.Definitions.Divisors.LogAbsVpOfNormalised` | 27 | 2.353 | 2.286 | -2.86% | 2.353 | 2.285 | -2.88% | 0/5 | 0/5 |
| `Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff` | 29 | 0.810 | 0.778 | -3.98% | 0.816 | 0.778 | -4.61% | 0/5 | 0/5 |
| `Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero` | 27 | 1.954 | 1.867 | -4.48% | 1.954 | 1.862 | -4.72% | 0/5 | 0/5 |

CPU sums of per-source medians were 5.789 → 5.515 seconds (-4.72%). 0 sources had a higher candidate median. The candidate was slower in 0/20 pairs. The parent and candidate ranges overlapped in 1/4 sources. Round sums differed by -5.77% to -4.07%.

Elapsed sums of per-source medians were 5.797 → 5.516 seconds (-4.83%). 0 sources had a higher candidate median. The candidate was slower in 0/20 pairs. The parent and candidate ranges overlapped in 1/4 sources. Round sums differed by -5.88% to -4.03%.

Lean also reported its import counts in the warm-up compilation of each source. Each entry lists the parent and candidate magnitudes.

| Source | Imported modules | Imported bytes | Imported constants |
|---|---:|---:|---:|
| `Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne` | 14,348 → 12,753 | 2,456,914,096 → 2,261,496,544 | 395,932 → 347,177 |
| `Development.AbelianVarietyTheory.Definitions.Divisors.LogAbsVpOfNormalised` | 14,317 → 13,248 | 2,445,134,536 → 2,388,037,024 | 392,976 → 380,638 |
| `Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff` | 14,359 → 13,078 | 2,457,168,560 → 2,352,578,312 | 395,833 → 371,591 |
| `Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero` | 14,511 → 13,003 | 2,526,598,480 → 2,365,006,096 | 409,250 → 367,130 |

## Fresh stock Lake workload

The two genuine theorem roots and all 3 project dependencies and roots formed a complete project workload. Every run started with an empty project build directory and the same pinned package cache. All 3 modules compiled in each of twelve runs. Five measured pairs followed one warm-up pair. The timer covers Lake scheduling and compilation. The raw records list the actual compiled modules.

CPU medians were 17.667 → 16.596 seconds (-6.06%). The parent range was 17.287–17.840 seconds and the candidate range was 16.377–16.883 seconds. The candidate was slower in 0/5 pairs.

Elapsed medians were 9.859 → 9.071 seconds (-7.99%). The parent range was 9.631–9.882 seconds and the candidate range was 9.004–9.252 seconds. The candidate was slower in 0/5 pairs.

The timings apply to these measured sources and jobs. No whole-project compile time was measured.

The [default-target capacity record](default-build-capacity.json) includes the current receipt and map queries, a prior-parent stock extraction sample, observed standard runner space, and the community runner requirements. The current source graph has 39,137 edited modules and 49,932 edited or potentially downstream modules out of 60,492. Cache hits and Lake scheduling determine which of them an actual build executes. The exact author, merge and source-input keys had no public successful build receipt at the observation time.

To measure the space needed for a complete ordinary project restore, stock `leantar` unpacked 512 archives from the verified current parent. The extracted files totaled 1,101,123,255 bytes. The stratified estimate is 68.09 GiB across the 60,492 modules, with an estimated sampling error of 2.23 GiB. Package dependencies, sources and build temporaries require additional space. The standard public job has 4 vCPUs, 16 GB RAM and a six-hour limit. The community full-build runner calls for 250 GiB free SSD and ideally 128 GiB memory. A maintainer can request the unchanged nine default targets with `gh workflow run build-pr.yml --repo leanprover-community/riemann-hypothesis --ref main -f mode=build -f pr_number=879`. [Sample and machine data](default-build-capacity.json) [Community workflow](https://github.com/leanprover-community/riemann-hypothesis/blob/bb9476b875a219608a9068f8f18d8c56b4e7f1ca/.github/workflows/build-pr.yml) [Standard Linux runners](https://docs.github.com/en/actions/reference/runners/github-hosted-runners) [Job limits](https://docs.github.com/en/actions/reference/limits)

The original Actions ZIP has SHA-256 `eb9c366b125967a5d8c12f33b5046d030776128df515a370ea8b89f0609ed748`. [Exact workflow and source manifest](https://github.com/aliromman/riemann-hypothesis/tree/0c22dbad798ce02074603246b990626cd1a69ae5/ci/stock-batch-1018)

The [input comparison for author revision `87b887f70183`](bindings/87b887f70183a19b577c6b084a8865f04ecb69e4-on-5f2c8594adf1f48032d37583118512cd7bbf3afa.json) checks the actual community merge `1555bcadd7a6`. GitHub based that merge on `bb9476b875a2`. A clean Git merge with current community main `5f2c8594adf1` produced tree `78a702af430a`. The complete old and new candidate Lean trees are identical. All 143 parent archives were downloaded and extracted again using the current community receipt. All 715 raw public, server, private and compiler IR digests matched the original stock records. The sources, package pins, proof settings and project dependency graph used by this workload matched. The compilation and timing records above come from the original Linux job. A community maintainer can request a default-target build with `gh workflow run build-pr.yml --repo leanprover-community/riemann-hypothesis --ref main -f mode=build -f pr_number=879`.

The [input comparison for author revision `87b887f70183`](bindings/87b887f70183a19b577c6b084a8865f04ecb69e4-on-13b3a924e6439935cf5c7c6abb778f0dc7944956.json) checks the actual community merge `1555bcadd7a6`. GitHub based that merge on `bb9476b875a2`. A clean Git merge with current community main `13b3a924e643` produced tree `4a49b96251d9`. The complete old and new candidate Lean trees are identical. All 143 parent archives were downloaded and extracted again using the current community receipt. All 715 raw public, server, private and compiler IR digests matched the original stock records. The sources, package pins, proof settings and project dependency graph used by this workload matched. The compilation and timing records above come from the original Linux job. A community maintainer can request a default-target build with `gh workflow run build-pr.yml --repo leanprover-community/riemann-hypothesis --ref main -f mode=build -f pr_number=879`.

The documentation-only community updates `06e06ac08731` (AGENTS.md), `13b3a924e643` (README.md) each have a successful official receipt for the same source tree, map and module manifest.

The [input comparison for author revision `9e72b7b093ae`](bindings/9e72b7b093ae4dabd1bb89f14fc9e8885c5aad5c-on-c6d67c05b648be9f1993aa84bd32c29ea9d2fb72.json) checks the actual community merge `787653bd2d41`. GitHub based that merge on current community main `c6d67c05b648`. The complete old and new candidate Lean trees are identical. All 143 parent archives were downloaded and extracted again using the current community receipt. All 715 raw public, server, private and compiler IR digests matched the original stock records. The sources, package pins, proof settings and project dependency graph used by this workload matched. The compilation and timing records above come from the original Linux job. A community maintainer can request a default-target build with `gh workflow run build-pr.yml --repo leanprover-community/riemann-hypothesis --ref main -f mode=build -f pr_number=879`.

The documentation-only community updates `06e06ac08731` (AGENTS.md), `13b3a924e643` (README.md) each have a successful official receipt for the same source tree, map and module manifest.

The published author and GitHub merge both have complete Git tree `294f86161a5ac7327656e77b8185964becaf47fb`, identical to the previously checked effective merge. The upstream label check passed. The upstream frozen-file check confirmed all six paths on this exact head. The manual ordinary build was skipped. [Label PR](https://github.com/leanprover-community/riemann-hypothesis/actions/runs/45393892762/job/138444447255) [Frozen challenge files](https://github.com/leanprover-community/riemann-hypothesis/actions/runs/45393892788/job/138444447276)

Across all 143 compared modules, `.olean.server` grew by 1,216 bytes and `.olean.private` by 20,168 bytes. The four measured compiler warm-ups loaded 1,069–1,595 fewer modules, 57,097,512–195,417,552 fewer imported bytes, and 12,338–48,755 fewer constants. In the synthetic negative controls the statement checker rejected the changed proposition and the axiom checker rejected the added named axiom. Both rejections happened before kernel replay. The three kernels separately accepted the positive alternate proof and each of the two actual project exports.
