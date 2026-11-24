# Stock Lake, kernel and timing records for PR #879

GitHub checked merge `4db316c45c8e1d40f99c60396f58951e7ae2a22f` of author head `ac3ff4bec1bf43a091eb6721e12eaf40a592cb9d` and community parent `1da818b50f1e18808db2792b9dc735bda8cb84d8`. The candidate source tree is `7225a26844ccbc8d12877c062c1fe5330ec78ad1`. The successful parent cache manifest is `edc38df9198228480080821adb772f6c4109fdba7404a04be28bc49a250cb487`. [Original Linux run](https://github.com/aliromman/riemann-hypothesis/actions/runs/45431197871)

The stock Lake build covered 72 roots and 140 project modules. 95 modules had source changes, and 99 modules compiled from source. Across both sides the check compared 9,540 module-owned declarations, including 7,555 in changed modules. Lean replayed 3 selected roots. All compared names, types, theorem proofs, definition values, public exports and kernel declarations matched. The compiler-warning multisets matched after removal of source positions.

The import check compared the full public serialized module image after clearing the direct imports field. It compared the exported imports separately. The raw public file differed in 95 modules, the raw server file in 99, and the raw private file in 99. The source manifest records the old and new full-file SHA-256 and the numbers of imported modules added and removed for each of the 95 edited files in this scope.

For every edited source, the job loaded the verified parent `.olean`, `.ir.sig` and `.ir` into the pinned Lean serializer. It replaced only the ordered direct import list, keeping entries, constants and flags. All 285 resulting whole files matched the SHA-256 of the actual stock Linux output. The raw `.ir` digest differed in 95 modules. It carried the source import list. Each of the 95 IR signatures had an empty import table. The job read the actual old and new import items and flags in each IR part and recorded their counts. Among edited modules, raw `.olean` was 42,526,208 → 42,032,384 bytes, `.ir.sig` was 23,560 → 23,560 bytes, and `.ir` was 2,486,408 → 1,982,960 bytes. The ZIP contains every original, expected and actual SHA-256. [Earlier batch #896 raw IR diagnostic](https://github.com/aliromman/riemann-hypothesis/actions/runs/45368083272)

In the same edited modules, raw `.olean.server` was 951,832 → 952,848 bytes and `.olean.private` was 73,100,464 → 73,121,264 bytes. The declaration comparison read all three `.olean` parts and compared every private constant, proof and value. It checked the full sorted kernel declaration serialization as well. The stock theorem verifier also read both actual proof bodies.

Across all 140 checked modules, the raw server files changed by +1,128 bytes and the raw private files by +20,800 bytes.

## Bounded proof exports

Both predeclared targets belong to edited sources. Each revision produced the same proof trace for each theorem. The job ran stock `lake comparator` on those two exports with `--inadvisably-no-sandbox` on a disposable Ubuntu runner. It used the repository’s permitted axioms `propext`, `Quot.sound` and `Classical.choice`. Lean default, Lean paranoid and nanoda accepted both theorems. The full sandboxed five-claim check remains outstanding.

All three kernels also accepted a control in which `rfl` replaced the proof of `n + 0 = n`. In the two negative controls, statement comparison rejected `n * 1 = n` in place of `n + 0 = n`, and the axiom check rejected the added axiom `ComparisonControl.extra`. Both rejections occurred before kernel replay.

- `GlobalTheory.CatCoh.commAlgFunctorCoboundaryZero_mem_cocyclesOne` used 4,888,069 bytes on each side. SHA-256 `00615d0ad579cd5a3309866b1d7e5861bfa4d6b206bf92d861a0d9b542eee332`.
- `GlobalTheory.TopForm.isBaseChange_exteriorPower` used 52,581,161 bytes on each side. SHA-256 `2dcae760dcc362b23a2aec4c37f91947c52936d0274a4d81e8d65c82812ae24e`.

## Inputs after community batch #1198

The previous panel had 3 untimed roots that upstream deleted. The current panel retains its 69 surviving roots and includes 3 changed replacements. Each replacement comes from the same immediate namespace. The selection minimizes the difference in project closure size and direct import count, then breaks ties by module name. [Replacement selection](https://github.com/aliromman/riemann-hypothesis/blob/f3aae0655526a12e1fa18a8e8c3a4ac29efc3f78/ci/stock-batch-1198/root-replacement-design.json)

Among project modules common to both panels, 4 parent sources, 4 candidate sources, 1 ordered parent import lists, 7 archive digests and 14 Lake input hashes changed. The complete new panel includes 10 project modules outside the prior cone. The prior panel had 13 project modules outside the new cone. [Per-root changes](previous-inputs.json)

The edited cocycle module received four upstream instance changes after its named theorem. This changed a fresh-workload input. A separate pinned exporter loaded the new signed parent archive and found the actual theorem proof at expression index 83,803. Its full 4,888,069-byte proof export still matches the preceding batch. The current Ubuntu job also exported the new parent and candidate. [Independent signed-parent export](https://github.com/aliromman/riemann-hypothesis/blob/f3aae0655526a12e1fa18a8e8c3a4ac29efc3f78/ci/stock-batch-1198/rechecked-parent-export.json)

All current results and times below come from this Ubuntu job. The previous job ran on its own machine. [Earlier stock run](https://github.com/aliromman/riemann-hypothesis/actions/runs/45407202903)

The earlier runner reported image `20261116.376.1` and `Linux-7.0.0-1017-azure-x86_64-with-glibc2.39`. The current runner reported image `20261116.133.1` and `Linux-7.0.0-1014-aws-x86_64-with-glibc2.39`.

On that previous runner, the sum of single-module medians changed by -5.32% elapsed and -5.28% CPU. The previous fresh Lake workload changed by -10.60% elapsed and -9.53% CPU. Each percentage compares paired compilations on one runner.

Every individual timing closure retained the same parent and candidate source blobs, ordered imports, Lake input hashes and verified parent archives as the earlier batch.

## Matched single-module compiler trials

All 4 predeclared sources ran on the same Ubuntu job. Each used a warm-up pair, then five alternating matched trials with one Lean thread and a fresh output directory for each compile. Both sides used the same pinned imported artifacts. CPU is child user plus system time. Elapsed includes compilation and creation of `.olean`, `.ilean` and C output. Hydration and declaration comparison were outside the timers.

| Source | Private imports removed | Parent CPU, s | Candidate CPU, s | CPU change | Parent elapsed, s | Candidate elapsed, s | Elapsed change | Slower CPU pairs | Slower elapsed pairs |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne` | 27 | 0.649 | 0.573 | -11.62% | 0.655 | 0.581 | -11.34% | 0/5 | 0/5 |
| `Development.AbelianVarietyTheory.Definitions.Divisors.LogAbsVpOfNormalised` | 27 | 2.251 | 2.205 | -2.03% | 2.250 | 2.205 | -1.99% | 0/5 | 0/5 |
| `Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff` | 29 | 0.757 | 0.720 | -4.95% | 0.762 | 0.724 | -4.98% | 0/5 | 0/5 |
| `Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero` | 27 | 1.801 | 1.723 | -4.34% | 1.802 | 1.719 | -4.59% | 0/5 | 0/5 |

CPU sums of per-source medians were 5.457 → 5.221 seconds (-4.34%). 0 sources had a higher candidate median. The candidate was slower in 0/20 pairs. The parent and candidate ranges overlapped in 1/4 sources. Round sums differed by -7.28% to -2.83%.

For cpu time, the median within-pair change was -3.01% in the 10 trials that compiled the parent first, and -4.47% in the 10 trials that compiled the candidate first.

Elapsed sums of per-source medians were 5.470 → 5.230 seconds (-4.39%). 0 sources had a higher candidate median. The candidate was slower in 0/20 pairs. The parent and candidate ranges overlapped in 1/4 sources. Round sums differed by -7.49% to -3.35%.

For elapsed time, the median within-pair change was -3.20% in the 10 trials that compiled the parent first, and -4.91% in the 10 trials that compiled the candidate first.

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

CPU medians were 15.058 → 14.271 seconds (-5.22%). The parent range was 14.996–15.105 seconds and the candidate range was 14.239–14.343 seconds. The candidate was slower in 0/5 pairs.

Elapsed medians were 8.350 → 7.708 seconds (-7.69%). The parent range was 8.332–8.413 seconds and the candidate range was 7.687–7.737 seconds. The candidate was slower in 0/5 pairs.

The community also published a successful receipt directly for GitHub’s first merge parent. It has the same project artifact map and module manifest as the donor used in this run. Its SHA-256 is `a6a11f580ac1cd82a43c7dedb0d255ad775c6af2a235035a384bb407d26a824f`. [Community receipt](https://rh-cache.taucetiproject.org/ci/revisions/1da818b50f1e18808db2792b9dc735bda8cb84d8.json)

These timings cover the measured sources and jobs. Whole-project build time requires a separate measurement.

The [default-target capacity record](default-build-capacity.json) includes the current receipt and map queries, a prior-parent stock extraction sample, observed standard runner space, and the community runner requirements. The current source graph has 39,021 edited modules and 49,424 edited or potentially downstream modules out of 59,908. Cache hits and Lake scheduling determine which of them an actual build executes. The exact author, merge and source-input keys had no public successful build receipt at the observation time.

To measure the space needed for a complete ordinary project restore, the stratified sample used 512 archives from the verified current parent. Stock `leantar` inspected 320 on this parent. For 192 previous observations, both the entire signed archive and Lake input key were identical. The sample files totaled 1,083,881,126 bytes. The stratified estimate is 65.63 GiB across the 59,908 modules, with an estimated sampling error of 2.14 GiB. Package dependencies, sources and build temporaries require additional space. The standard public job has 4 vCPUs, 16 GB RAM and a six-hour limit. The community full-build runner calls for 250 GiB free SSD and ideally 128 GiB memory. A maintainer can request the unchanged nine default targets with `gh workflow run build-pr.yml --repo leanprover-community/riemann-hypothesis --ref main -f mode=build -f pr_number=879`. [Sample and machine data](default-build-capacity.json) [Community workflow](https://github.com/leanprover-community/riemann-hypothesis/blob/1da818b50f1e18808db2792b9dc735bda8cb84d8/.github/workflows/build-pr.yml) [Standard Linux runners](https://docs.github.com/en/actions/reference/runners/github-hosted-runners) [Job limits](https://docs.github.com/en/actions/reference/limits)

The original Actions ZIP has SHA-256 `4a80042defaa7d6ddbfc60c9c1b1381ec7457a61fa0fe63451e590f8c1d3d0cb`. [Exact workflow and source manifest](https://github.com/aliromman/riemann-hypothesis/tree/f3aae0655526a12e1fa18a8e8c3a4ac29efc3f78/ci/stock-batch-1198)

The [input comparison for author revision `ac3ff4bec1bf`](bindings/ac3ff4bec1bf43a091eb6721e12eaf40a592cb9d-on-1da818b50f1e18808db2792b9dc735bda8cb84d8.json) checks the actual community merge `4db316c45c8e`. GitHub based that merge on current community main `1da818b50f1e`. The complete old and new candidate Lean trees are identical. All 140 parent archives were downloaded and extracted again using the current community receipt. All 700 raw public, server, private and compiler IR digests matched the original stock records. The sources, package pins, proof settings and project dependency graph used by this workload matched. The compilation and timing records above come from the original Linux job. A community maintainer can request a default-target build with `gh workflow run build-pr.yml --repo leanprover-community/riemann-hypothesis --ref main -f mode=build -f pr_number=879`.

## Source sandbox and current head `ac3ff4bec1bf`

The default Linux Bubblewrap Comparator compiled both named theorem sources from empty project outputs on this pull request. All three kernels accepted both results. All 9 raw public module, IR signature and full IR files for its 3 project sources matched the separate ordinary build. The alternate proof was accepted. The changed statement and extra axiom were rejected before kernel replay. Every source input to those sandboxed compilations also matches current GitHub preview `4db316c45c8e1d40f99c60396f58951e7ae2a22f`. [Original sandbox results](https://github.com/aliromman/riemann-hypothesis/tree/4366fc4a54fe18b21b3dcda79770f37c682ad2ba/ci/source-sandbox/results/45431323026/)

All nine public author, merge and input-fingerprint cache routes returned 404 for this head. The public parent had a successful direct receipt. [Current project and cache binding](current-verification.json)
