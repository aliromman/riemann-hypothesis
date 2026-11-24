# Stock Lake, kernel and timing records for PR #879

GitHub checked merge `4894d50f6e36f772410351d3d44e45bcba8ada7c` of author head `a2a92740de233b5ca34edee530cb1efe7cd63b73` and community parent `6866a9c6260d77b88a7b5477433e3044b6844f9b`. The candidate source tree is `6578db3dffd4f7afe7c61f2a6dfd013d3e23c341`. The successful parent cache manifest is `0be4f7d2dc2245d221501a8821f7a265982a3ea58cdd0bc799abb98681470f23`. [Original Linux run](https://github.com/aliromman/riemann-hypothesis/actions/runs/45407202903)

The stock Lake build covered 72 roots and 143 project modules. 94 modules had source changes, and 101 modules compiled from source. Across both sides the check compared 9,710 module-owned declarations, including 7,694 in changed modules. Lean replayed 3 selected roots. All compared names, types, theorem proofs, definition values, public exports and kernel declarations matched. The compiler-warning multisets matched after removal of source positions.

The import check compared the full public serialized module image after clearing the direct imports field. It compared the exported imports separately. The raw public file differed in 94 modules, the raw server file in 98, and the raw private file in 98. The source manifest records the old and new full-file SHA-256 and the numbers of imported modules added and removed for each of the 94 edited files in this scope.

For every edited source, the job loaded the verified parent `.olean`, `.ir.sig` and `.ir` into the pinned Lean serializer. It replaced only the ordered direct import list, keeping entries, constants and flags. All 282 resulting whole files matched the SHA-256 of the actual stock Linux output. The raw `.ir` digest differed in 94 modules. It carried the source import list. Each of the 94 IR signatures had an empty import table. The job read the actual old and new import items and flags in each IR part and recorded their counts. Among edited modules, raw `.olean` was 42,850,456 → 42,360,336 bytes, `.ir.sig` was 23,312 → 23,312 bytes, and `.ir` was 2,541,096 → 2,041,688 bytes. The ZIP contains every original, expected and actual SHA-256. [Earlier batch #896 raw IR diagnostic](https://github.com/aliromman/riemann-hypothesis/actions/runs/45368083272)

In the same edited modules, raw `.olean.server` was 958,248 → 959,352 bytes and `.olean.private` was 73,760,696 → 73,780,864 bytes. The declaration comparison read all three `.olean` parts and compared every private constant, proof and value. It checked the full sorted kernel declaration serialization as well. The stock theorem verifier also read both actual proof bodies.

Across all 143 checked modules, the raw server files changed by +1,216 bytes and the raw private files by +20,168 bytes.

## Bounded proof exports

Both predeclared targets belong to edited sources. Each revision produced the same proof trace for each theorem. The job ran stock `lake comparator` on those two exports with `--inadvisably-no-sandbox` on a disposable Ubuntu runner. It used the repository’s permitted axioms `propext`, `Quot.sound` and `Classical.choice`. Lean default, Lean paranoid and nanoda accepted both theorems. The full sandboxed five-claim check remains outstanding.

All three kernels also accepted a control in which `rfl` replaced the proof of `n + 0 = n`. In the two negative controls, statement comparison rejected `n * 1 = n` in place of `n + 0 = n`, and the axiom check rejected the added axiom `ComparisonControl.extra`. Both rejections occurred before kernel replay.

- `GlobalTheory.CatCoh.commAlgFunctorCoboundaryZero_mem_cocyclesOne` used 4,888,069 bytes on each side. SHA-256 `00615d0ad579cd5a3309866b1d7e5861bfa4d6b206bf92d861a0d9b542eee332`.
- `GlobalTheory.TopForm.isBaseChange_exteriorPower` used 52,581,161 bytes on each side. SHA-256 `2dcae760dcc362b23a2aec4c37f91947c52936d0274a4d81e8d65c82812ae24e`.

The upstream module cache donor `1cd97d8aa4a16681b109389ab18eefa4b2ba36d8` and the actual GitHub merge parent have the same complete Lean source tree `00c2fd41c7b96184317b81cef9e3ffdc730e99c6`, package pins and frozen verification inputs.

## Inputs after community batch #1119

All 72 predeclared roots remained in the current project. Relative to the previous batch, 4 parent sources and 4 candidate sources in the complete panel changed. The number of changed direct import lists on the parent side was 0. The number of changed archive digests was 4, and 4 Lake input hashes changed. The job ran the stock build and comparison for this complete panel on the current merge. [Per-root changes](previous-inputs.json)

The project inputs for both selected theorem closures and the complete fresh Lake workload match the preceding batch. The results and times below all come from the new Ubuntu job. The previous job ran on its own machine. [Earlier stock run](https://github.com/aliromman/riemann-hypothesis/actions/runs/45386629388)

The earlier runner reported image `20261116.133.1` and `Linux-7.0.0-1014-aws-x86_64-with-glibc2.39`. The current runner reported image `20261116.376.1` and `Linux-7.0.0-1017-azure-x86_64-with-glibc2.39`.

On that previous runner, the sum of single-module medians changed by -4.83% elapsed and -4.72% CPU. The previous fresh Lake workload changed by -7.99% elapsed and -6.06% CPU. Each percentage compares paired compilations on one runner.

Every individual timing closure retained the same parent and candidate source blobs, ordered imports, Lake input hashes and verified parent archives as the earlier batch.

## Matched single-module compiler trials

All 4 predeclared sources ran on the same Ubuntu job. Each used a warm-up pair, then five alternating matched trials with one Lean thread and a fresh output directory for each compile. Both sides used the same pinned imported artifacts. CPU is child user plus system time. Elapsed includes compilation and creation of `.olean`, `.ilean` and C output. Hydration and declaration comparison were outside the timers.

| Source | Private imports removed | Parent CPU, s | Candidate CPU, s | CPU change | Parent elapsed, s | Candidate elapsed, s | Elapsed change | Slower CPU pairs | Slower elapsed pairs |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne` | 27 | 0.731 | 0.633 | -13.49% | 0.732 | 0.637 | -12.98% | 0/5 | 0/5 |
| `Development.AbelianVarietyTheory.Definitions.Divisors.LogAbsVpOfNormalised` | 27 | 2.233 | 2.163 | -3.13% | 2.230 | 2.157 | -3.30% | 1/5 | 1/5 |
| `Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff` | 29 | 0.836 | 0.780 | -6.70% | 0.839 | 0.781 | -6.95% | 1/5 | 1/5 |
| `Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero` | 27 | 1.896 | 1.820 | -4.03% | 1.891 | 1.815 | -4.00% | 1/5 | 2/5 |

CPU sums of per-source medians were 5.697 → 5.396 seconds (-5.28%). 0 sources had a higher candidate median. The candidate was slower in 3/20 pairs. The parent and candidate ranges overlapped in 3/4 sources. Round sums differed by -7.41% to -3.25%.

For cpu time, the median within-pair change was -5.63% in the 10 trials that compiled the parent first, and -7.65% in the 10 trials that compiled the candidate first.

Elapsed sums of per-source medians were 5.692 → 5.390 seconds (-5.32%). 0 sources had a higher candidate median. The candidate was slower in 4/20 pairs. The parent and candidate ranges overlapped in 3/4 sources. Round sums differed by -7.47% to -3.17%.

For elapsed time, the median within-pair change was -5.60% in the 10 trials that compiled the parent first, and -7.78% in the 10 trials that compiled the candidate first.

Lean also reported its import counts in the warm-up compilation of each source. Each entry lists the parent and candidate magnitudes.

| Source | Imported modules | Imported bytes | Imported constants |
|---|---:|---:|---:|
| `Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne` | 14,348 → 12,753 | 2,456,914,096 → 2,261,496,544 | 395,932 → 347,177 |
| `Development.AbelianVarietyTheory.Definitions.Divisors.LogAbsVpOfNormalised` | 14,317 → 13,248 | 2,445,134,536 → 2,388,037,024 | 392,976 → 380,638 |
| `Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff` | 14,359 → 13,078 | 2,457,168,560 → 2,352,578,312 | 395,833 → 371,591 |
| `Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero` | 14,511 → 13,003 | 2,526,598,480 → 2,365,006,096 | 409,250 → 367,130 |

Across the four warm-ups Lean reported 1,069–1,595 fewer modules (7.47–11.12%), 57,097,512–195,417,552 fewer bytes (2.34–7.95%), 12,338–48,755 fewer constants (3.14–12.31%). The byte counter measures imported data. The job did not measure peak resident memory.

## Fresh stock Lake workload

The two theorem roots and their project dependencies formed a complete workload of 3 modules, including the roots. Every run started with an empty project build directory and the same pinned package cache. All 3 modules compiled in each of twelve runs. Five measured pairs followed one warm-up pair. The timer covers Lake scheduling and compilation. The raw records list the actual compiled modules.

CPU medians were 17.751 → 16.059 seconds (-9.53%). The parent range was 17.117–18.013 seconds and the candidate range was 15.511–17.047 seconds. The candidate was slower in 0/5 pairs.

Elapsed medians were 10.247 → 9.161 seconds (-10.60%). The parent range was 9.948–10.377 seconds and the candidate range was 8.794–9.656 seconds. The candidate was slower in 0/5 pairs.

The community also published a successful receipt directly for GitHub’s first merge parent. It has the same project artifact map and module manifest as the donor used in this run. Its SHA-256 is `87462e5c2a8c7a472eef4960662b4982e282ee4b6bacbda1680392c087da8291`. [Community receipt](https://rh-cache.taucetiproject.org/ci/revisions/6866a9c6260d77b88a7b5477433e3044b6844f9b.json)

These timings cover the measured sources and jobs. Whole-project build time requires a separate measurement.

The [default-target capacity record](default-build-capacity.json) includes the current receipt and map queries, a prior-parent stock extraction sample, observed standard runner space, and the community runner requirements. The current source graph has 39,120 edited modules and 49,635 edited or potentially downstream modules out of 60,146. Cache hits and Lake scheduling determine which of them an actual build executes. The exact author, merge and source-input keys had no public successful build receipt at the observation time.

To measure the space needed for a complete ordinary project restore, stock `leantar` unpacked 512 archives from the verified current parent. The extracted files totaled 1,091,738,253 bytes. The stratified estimate is 66.80 GiB across the 60,146 modules, with an estimated sampling error of 2.15 GiB. Package dependencies, sources and build temporaries require additional space. The standard public job has 4 vCPUs, 16 GB RAM and a six-hour limit. The community full-build runner calls for 250 GiB free SSD and ideally 128 GiB memory. A maintainer can request the unchanged nine default targets with `gh workflow run build-pr.yml --repo leanprover-community/riemann-hypothesis --ref main -f mode=build -f pr_number=879`. [Sample and machine data](default-build-capacity.json) [Community workflow](https://github.com/leanprover-community/riemann-hypothesis/blob/6866a9c6260d77b88a7b5477433e3044b6844f9b/.github/workflows/build-pr.yml) [Standard Linux runners](https://docs.github.com/en/actions/reference/runners/github-hosted-runners) [Job limits](https://docs.github.com/en/actions/reference/limits)

The original Actions ZIP has SHA-256 `e841a7cf838570544bc5849a22f95eaf99c853e5b18f81270060a2dab856720a`. [Exact workflow and source manifest](https://github.com/aliromman/riemann-hypothesis/tree/5f08aaa9c6088d9fa827af5defdb7c7c36b87644/ci/stock-batch-1119)
