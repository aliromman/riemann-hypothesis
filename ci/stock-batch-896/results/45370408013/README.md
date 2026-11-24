# Stock Lake, kernel and timing records for PR #879

GitHub checked merge `1eea9dc9cf3635757f61b9c2cf8d85205f2426a7` of author head `c4b66990077a462b2e2d35777fe0f55644463e87` and community parent `bde3cce9fc2feaf9a39c7f37711cb26c7c44fd1b`. The candidate source tree is `c7126960bde14461813ed3125e947e47544c04c1`. The successful parent cache manifest is `a6cfc0b330c9b2d25551163316b4ae66dbd1b9006439c8f42621c177ec684463`. [Original Linux run](https://github.com/aliromman/riemann-hypothesis/actions/runs/45370408013)

The stock Lake build covered 72 roots and 143 project modules. 94 modules had source changes, and 101 modules compiled from source. Across both sides the check compared 9,710 module-owned declarations, including 7,694 in changed modules. Lean replayed 3 selected roots. All compared names, types, theorem proofs, definition values, public exports and kernel declarations matched. The compiler-warning multisets matched after removal of source positions.

The import check compared the full public serialized module image after clearing the direct imports field. It compared the exported imports separately. The raw public file differed in 94 modules, the raw server file in 98, and the raw private file in 98. The source manifest records the old and new full-file SHA-256 and the numbers of imported modules added and removed for each of the 94 edited files in this scope.

For every edited source, the job loaded the signed parent `.olean`, `.ir.sig` and `.ir` into the pinned Lean serializer. It replaced only the ordered direct import list, keeping entries, constants and flags. All 282 resulting whole files matched the SHA-256 of the actual stock Linux output. The raw `.ir` digest differed in 94 modules. It carried the source import list. Each of the 94 IR signatures had an empty import table. The job read the actual old and new import items and flags in each IR part and recorded their counts. Among edited modules, raw `.olean` was 42,850,584 → 42,360,464 bytes, `.ir.sig` was 23,312 → 23,312 bytes, and `.ir` was 2,541,096 → 2,041,688 bytes. The ZIP contains every original, expected and actual SHA-256. [Initial run with a raw `.ir` assertion](https://github.com/aliromman/riemann-hypothesis/actions/runs/45368083272)

In the same edited modules, raw `.olean.server` was 959,384 → 960,488 bytes and `.olean.private` was 73,765,632 → 73,785,800 bytes. The declaration comparison read all three `.olean` parts and compared every private constant, proof and value. It checked the full sorted kernel declaration serialization as well. The preceding diagnosis supplied structural-only output metadata to the import theorem reporter. The final job used the original import theorem-source verifier and checked both actual proof bodies. [Intermediate diagnostic](https://github.com/aliromman/riemann-hypothesis/actions/runs/45369661753)

## Bounded proof exports

The predeclared theorem targets belong to actual changed sources. Both revisions produced identical exported proof traces for each theorem. The stock Comparator checked statements with the repository’s permitted axioms `propext`, `Quot.sound` and `Classical.choice`. Lean default, Lean paranoid and nanoda accepted both targets. An alternate proof passed. The two negative controls rejected a changed statement and an added named axiom. This scope does not include a five-claim export.

- `GlobalTheory.CatCoh.commAlgFunctorCoboundaryZero_mem_cocyclesOne` used 4,888,069 bytes on each side. SHA-256 `00615d0ad579cd5a3309866b1d7e5861bfa4d6b206bf92d861a0d9b542eee332`.
- `GlobalTheory.TopForm.isBaseChange_exteriorPower` used 52,581,161 bytes on each side. SHA-256 `2dcae760dcc362b23a2aec4c37f91947c52936d0274a4d81e8d65c82812ae24e`.

## Panel changes for the merged batch

- `Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty` → `Development.AbelianVarietyTheory.Definitions.Divisors.PreUMono`. Parent deleted old untimed root; same source directory, an actual changed module, fewest additional ancestors and fixed SHA-256 tie break.

## Matched single-module compiler trials

All 4 predeclared sources ran on the same Ubuntu job. Each used a warm-up pair, then five alternating matched trials with one Lean thread and a fresh output directory for each compile. Both sides used the same pinned imported artifacts. CPU is child user plus system time. Elapsed includes compilation and creation of `.olean`, `.ilean` and C output. Hydration and declaration comparison were outside the timers.

| Source | Private imports removed | Parent CPU, s | Candidate CPU, s | CPU change | Parent elapsed, s | Candidate elapsed, s | Elapsed change | Slower CPU pairs | Slower elapsed pairs |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne` | 27 | 0.717 | 0.629 | -12.31% | 0.718 | 0.635 | -11.49% | 0/5 | 0/5 |
| `Development.AbelianVarietyTheory.Definitions.Divisors.LogAbsVpOfNormalised` | 27 | 2.532 | 2.502 | -1.17% | 2.529 | 2.494 | -1.39% | 0/5 | 0/5 |
| `Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff` | 29 | 0.829 | 0.787 | -5.13% | 0.835 | 0.790 | -5.42% | 0/5 | 0/5 |
| `Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero` | 27 | 2.010 | 1.902 | -5.35% | 2.009 | 1.903 | -5.27% | 0/5 | 0/5 |

CPU sums of per-source medians were 6.088 → 5.820 seconds (-4.40%). 0 sources had a higher candidate median. The candidate was slower in 0/20 pairs. The parent and candidate ranges overlapped in 1/4 sources. Round sums differed by -5.94% to -3.52%.

Elapsed sums of per-source medians were 6.092 → 5.823 seconds (-4.41%). 0 sources had a higher candidate median. The candidate was slower in 0/20 pairs. The parent and candidate ranges overlapped in 1/4 sources. Round sums differed by -6.18% to -3.55%.

Lean also reported its import counts in the warm-up compilation of each source. Each entry lists the parent and candidate magnitudes.

| Source | Imported modules | Imported bytes | Imported constants |
|---|---:|---:|---:|
| `Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne` | 14,348 → 12,753 | 2,456,914,096 → 2,261,496,544 | 395,932 → 347,177 |
| `Development.AbelianVarietyTheory.Definitions.Divisors.LogAbsVpOfNormalised` | 14,317 → 13,248 | 2,445,134,536 → 2,388,037,024 | 392,976 → 380,638 |
| `Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff` | 14,359 → 13,078 | 2,457,168,560 → 2,352,578,312 | 395,833 → 371,591 |
| `Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero` | 14,511 → 13,003 | 2,526,598,480 → 2,365,006,096 | 409,250 → 367,130 |

## Fresh stock Lake workload

The two genuine theorem roots and all 3 project dependencies and roots formed a complete project workload. Every run started with an empty project build directory and the same pinned package cache. All 3 modules compiled in each of twelve runs. Five measured pairs followed one warm-up pair. The timer covers Lake scheduling and compilation. The raw records list the actual compiled modules.

CPU medians were 17.629 → 16.812 seconds (-4.63%). The parent range was 17.427–17.857 seconds and the candidate range was 16.691–17.104 seconds. The candidate was slower in 0/5 pairs.

Elapsed medians were 9.840 → 9.209 seconds (-6.40%). The parent range was 9.631–9.959 seconds and the candidate range was 9.108–9.325 seconds. The candidate was slower in 0/5 pairs.

The timings apply to these measured sources and jobs. No whole-project compile time was measured.

The [default-target capacity record](default-build-capacity.json) includes the current receipt and map queries, a prior-parent stock extraction sample, observed standard runner space, and the community runner requirements. The current source graph has 39,159 edited modules and 50,060 edited or potentially downstream modules out of 60,629. Cache hits and Lake scheduling determine which of them an actual build executes. The exact author, merge and source-input keys had no public successful build receipt at the observation time.

The original Actions ZIP has SHA-256 `548e87859cf6fb8c4f1f0c9d55c4f793e85885c43163f0093704aec0318767ee`. [Exact workflow and source manifest](https://github.com/aliromman/riemann-hypothesis/tree/21f207e668f0058941d86e36a7b656170356c2a7/ci/stock-batch-896)

The [input comparison for author revision `c4b66990077a`](bindings/c4b66990077a462b2e2d35777fe0f55644463e87-on-73958da58a8a4d1f61b789745c5444baf6247cae.json) checks the actual community merge `1eea9dc9cf36`. GitHub based that merge on `bde3cce9fc2f`. A clean Git merge with current community main `73958da58a8a` produced tree `39cc5e449e22`. The complete old and new candidate Lean trees are identical. All 143 parent archives were downloaded and validated again using the current community parent receipt. The sources, package pins, proof settings and project dependency graph used by this workload matched. The compilation and timing records above come from the original Linux job.

The [input comparison for author revision `c4b66990077a`](bindings/c4b66990077a462b2e2d35777fe0f55644463e87-on-2d0c622a3464ba41ad98fca9086bab54fb74e303.json) checks the actual community merge `1eea9dc9cf36`. GitHub based that merge on `bde3cce9fc2f`. A clean Git merge with current community main `2d0c622a3464` produced tree `8a914c780f04`. The complete old and new candidate Lean trees are identical. All 143 parent archives were downloaded and extracted again using the current community receipt. All 715 raw public, server, private and compiler IR digests matched the original stock records. The sources, package pins, proof settings and project dependency graph used by this workload matched. The compilation and timing records above come from the original Linux job. A community maintainer can request a default-target build with `gh workflow run build-pr.yml --repo leanprover-community/riemann-hypothesis --ref main -f mode=build -f pr_number=879`.

The [input comparison for author revision `b880abd47823`](bindings/b880abd478236b392db065624391b785ad648b36-on-cb4dc6e23a6187db392c96664295415c55b6b01e.json) checks the actual community merge `6a6f366043ed`. GitHub based that merge on current community main `cb4dc6e23a61`. All 1 changed Lean files since the run fall outside this entire source and dependency cone. All 143 parent archives were downloaded and extracted again using the current community receipt. All 715 raw public, server, private and compiler IR digests matched the original stock records. The sources, package pins, proof settings and project dependency graph used by this workload matched. The compilation and timing records above come from the original Linux job. A community maintainer can request a default-target build with `gh workflow run build-pr.yml --repo leanprover-community/riemann-hypothesis --ref main -f mode=build -f pr_number=879`.

The [input comparison for author revision `c2c7fc890448`](bindings/c2c7fc890448cf0c8eab464f115e5e370129697a-on-cb4dc6e23a6187db392c96664295415c55b6b01e.json) checks the actual community merge `bca242683454`. GitHub based that merge on current community main `cb4dc6e23a61`. All 22 changed Lean files since the run fall outside this entire source and dependency cone. All 143 parent archives were downloaded and extracted again using the current community receipt. All 715 raw public, server, private and compiler IR digests matched the original stock records. The sources, package pins, proof settings and project dependency graph used by this workload matched. The compilation and timing records above come from the original Linux job. A community maintainer can request a default-target build with `gh workflow run build-pr.yml --repo leanprover-community/riemann-hypothesis --ref main -f mode=build -f pr_number=879`.
