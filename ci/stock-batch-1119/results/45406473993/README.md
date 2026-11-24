# Stock Lake, kernel and timing records for PR #977

GitHub checked merge `040c785b5b35bf2a35f826aa2273ca2627a95d9c` of author head `2b481024a8665bd5b24ca40d28fe90cb4fb86ce0` and community parent `6866a9c6260d77b88a7b5477433e3044b6844f9b`. The candidate source tree is `a598d19cccf798deb6e2bea9700cbac2ff050e11`. The successful parent cache manifest is `0be4f7d2dc2245d221501a8821f7a265982a3ea58cdd0bc799abb98681470f23`. [Original Linux run](https://github.com/aliromman/riemann-hypothesis/actions/runs/45406473993)

The stock Lake build covered 27 roots and 239 project modules. 29 modules had source changes, and 36 modules compiled from source. Across both sides the check compared 7,655 module-owned declarations, including 1,852 in changed modules. Lean replayed 6 selected roots. All compared names, types, theorem proofs, definition values, public exports and kernel declarations matched. The compiler-warning multisets matched after removal of source positions.

The structural check also required the raw public module and both compiler IR parts to match. The server and private module bytes differed in 33 and 25 modules.

## Bounded proof exports

Both predeclared targets belong to edited sources. Each revision produced the same proof trace for each theorem. The job ran stock `lake comparator` on those two exports with `--inadvisably-no-sandbox` on a disposable Ubuntu runner. It used the repository’s permitted axioms `propext`, `Quot.sound` and `Classical.choice`. Lean default, Lean paranoid and nanoda accepted both theorems. The full sandboxed five-claim check remains outstanding.

All three kernels also accepted a control in which `rfl` replaced the proof of `n + 0 = n`. In the two negative controls, statement comparison rejected `n * 1 = n` in place of `n + 0 = n`, and the axiom check rejected the added axiom `ComparisonControl.extra`. Both rejections occurred before kernel replay.

- `GlobalTheory.CompanionTheory.SW.Averaging.bijective_pair` used 3,149,696 bytes on each side. SHA-256 `31bf90c0ba09af45d2a9f9f99cc93265e87b6cd3824bb11016d34544ef565bf3`.
- `Formalism.LatticeBaseChangeAlt.four_term_sum_bound_of_parameters` used 50,380,642 bytes on each side. SHA-256 `9bf232ca29179dce903c72e3121754f9e639887a77f3072e88ef1ce68638c35b`.

The upstream module cache donor `1cd97d8aa4a16681b109389ab18eefa4b2ba36d8` and the actual GitHub merge parent have the same complete Lean source tree `00c2fd41c7b96184317b81cef9e3ffdc730e99c6`, package pins and frozen verification inputs.

## Inputs after community batch #1119

All 27 predeclared roots remained in the current project. Relative to the previous batch, 6 parent sources and 6 candidate sources in the complete panel changed. The number of changed direct import lists on the parent side was 1. The number of changed archive digests was 7, and 9 Lake input hashes changed. The job ran the stock build and comparison for this complete panel on the current merge. [Per-root changes](previous-inputs.json)

The project inputs for both selected theorem closures and the complete fresh Lake workload match the preceding batch. The results and times below all come from the new Ubuntu job. The previous job ran on its own machine. [Earlier stock run](https://github.com/aliromman/riemann-hypothesis/actions/runs/45386999286)

The earlier runner reported image `20261116.376.1` and `Linux-7.0.0-1017-azure-x86_64-with-glibc2.39`. The current runner reported image `20261116.133.1` and `Linux-7.0.0-1014-aws-x86_64-with-glibc2.39`.

On that previous runner, the sum of single-module medians changed by -0.51% elapsed and -0.54% CPU. The previous fresh Lake workload changed by +0.11% elapsed and -0.29% CPU. Each percentage compares paired compilations on one runner.

The individual timing closures that changed in the new batch were `CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.AdmissibleOfIwasawa`, `PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.FinalTF`.

## Matched single-module compiler trials

All 12 predeclared sources ran on the same Ubuntu job. Each used a warm-up pair, then five alternating matched trials with one Lean thread and a fresh output directory for each compile. Both sides used the same pinned imported artifacts. CPU is child user plus system time. Elapsed includes compilation and creation of `.olean`, `.ilean` and C output. Hydration and declaration comparison were outside the timers.

| Source | Clump members | Parent CPU, s | Candidate CPU, s | CPU change | Parent elapsed, s | Candidate elapsed, s | Elapsed change | Slower CPU pairs | Slower elapsed pairs |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.AdmissibleOfIwasawa` | 2 | 0.668 | 0.670 | +0.17% | 0.675 | 0.676 | +0.16% | 2/5 | 2/5 |
| `CompanionTheory.AutomorphicTheory.BesselWaveGrids.NqMovedExample` | 7 | 5.190 | 5.135 | -1.06% | 5.183 | 5.127 | -1.08% | 2/5 | 2/5 |
| `Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularPairLiftToPrimePowerField` | 2 | 0.882 | 0.877 | -0.63% | 0.887 | 0.882 | -0.51% | 1/5 | 1/5 |
| `Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelRowsColumnsSquareIntegrable` | 27 | 7.650 | 7.595 | -0.71% | 7.609 | 7.551 | -0.76% | 1/5 | 1/5 |
| `Formalism.IncomingBounds.FlowDegreeBounds.ProdRangeEqFactorialMulProdIco` | 2 | 1.281 | 1.276 | -0.35% | 1.285 | 1.283 | -0.14% | 2/5 | 2/5 |
| `Formalism.GradedWeylDivisibility.FinalC` | 19 | 5.323 | 5.286 | -0.69% | 5.296 | 5.255 | -0.78% | 0/5 | 0/5 |
| `GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteModuloGeneralEquation` | 2 | 5.754 | 5.766 | +0.21% | 5.756 | 5.768 | +0.21% | 3/5 | 3/5 |
| `GroundTheory.HeightsAndTheta.Heights.HeightKernels.AssemblySympl` | 24 | 6.331 | 6.242 | -1.40% | 6.328 | 6.224 | -1.65% | 0/5 | 0/5 |
| `PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.AutomorphyFactorKernelAlgebraProof` | 3 | 2.756 | 2.732 | -0.87% | 2.755 | 2.728 | -0.96% | 1/5 | 1/5 |
| `PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.FinalTF` | 19 | 9.582 | 9.533 | -0.51% | 9.535 | 9.472 | -0.66% | 0/5 | 0/5 |
| `ReciprocityTheory.DualLattices.QExpansionMonoWCoeffZero` | 2 | 1.761 | 1.747 | -0.81% | 1.755 | 1.738 | -0.95% | 2/5 | 2/5 |
| `ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality` | 17 | 8.337 | 8.298 | -0.48% | 8.296 | 8.252 | -0.53% | 2/5 | 2/5 |

CPU sums of per-source medians were 55.514 → 55.156 seconds (-0.65%). 2 sources had a higher candidate median. The candidate was slower in 16/60 pairs. The parent and candidate ranges overlapped in 11/12 sources. Round sums differed by -0.92% to -0.12%.

For cpu time, the median within-pair change was -0.73% in the 30 trials that compiled the parent first, and -0.60% in the 30 trials that compiled the candidate first.

Elapsed sums of per-source medians were 55.360 → 54.957 seconds (-0.73%). 2 sources had a higher candidate median. The candidate was slower in 16/60 pairs. The parent and candidate ranges overlapped in 11/12 sources. Round sums differed by -1.02% to -0.11%.

For elapsed time, the median within-pair change was -0.71% in the 30 trials that compiled the parent first, and -0.54% in the 30 trials that compiled the candidate first.

Lean reported the same module, byte and constant import counts on each side for all 12 warm-up pairs.

## Fresh stock Lake workload

The two theorem roots and their project dependencies formed a complete workload of 4 modules, including the roots. Every run started with an empty project build directory and the same pinned package cache. All 4 modules compiled in each of twelve runs. Five measured pairs followed one warm-up pair. The timer covers Lake scheduling and compilation. The raw records list the actual compiled modules.

CPU medians were 13.412 → 13.380 seconds (-0.24%). The parent range was 13.294–13.497 seconds and the candidate range was 13.264–13.395 seconds. The candidate was slower in 2/5 pairs.

Elapsed medians were 12.060 → 12.027 seconds (-0.27%). The parent range was 11.942–12.113 seconds and the candidate range was 11.952–12.057 seconds. The candidate was slower in 2/5 pairs.

The community also published a successful receipt directly for GitHub’s first merge parent. It has the same project artifact map and module manifest as the donor used in this run. Its SHA-256 is `87462e5c2a8c7a472eef4960662b4982e282ee4b6bacbda1680392c087da8291`. [Community receipt](https://rh-cache.taucetiproject.org/ci/revisions/6866a9c6260d77b88a7b5477433e3044b6844f9b.json)

These timings cover the measured sources and jobs. Whole-project build time requires a separate measurement.

The [default-target capacity record](default-build-capacity.json) includes the current receipt and map queries, a prior-parent stock extraction sample, observed standard runner space, and the community runner requirements. The current source graph has 11,575 edited modules and 42,123 edited or potentially downstream modules out of 60,146. Cache hits and Lake scheduling determine which of them an actual build executes. The exact author, merge and source-input keys had no public successful build receipt at the observation time.

To measure the space needed for a complete ordinary project restore, stock `leantar` unpacked 512 archives from the verified current parent. The extracted files totaled 1,091,738,253 bytes. The stratified estimate is 66.80 GiB across the 60,146 modules, with an estimated sampling error of 2.15 GiB. Package dependencies, sources and build temporaries require additional space. The standard public job has 4 vCPUs, 16 GB RAM and a six-hour limit. The community full-build runner calls for 250 GiB free SSD and ideally 128 GiB memory. A maintainer can request the unchanged nine default targets with `gh workflow run build-pr.yml --repo leanprover-community/riemann-hypothesis --ref main -f mode=build -f pr_number=977`. [Sample and machine data](default-build-capacity.json) [Community workflow](https://github.com/leanprover-community/riemann-hypothesis/blob/6866a9c6260d77b88a7b5477433e3044b6844f9b/.github/workflows/build-pr.yml) [Standard Linux runners](https://docs.github.com/en/actions/reference/runners/github-hosted-runners) [Job limits](https://docs.github.com/en/actions/reference/limits)

The original Actions ZIP has SHA-256 `f9fd9ebf792d5b7229dc3a5672aed92858c2c941db71bd4eb5bc649237606fe6`. [Exact workflow and source manifest](https://github.com/aliromman/riemann-hypothesis/tree/218b9f99c404188661ffe95eb2856f811d2e623b/ci/stock-batch-1119)

The [input comparison for author revision `2b481024a866`](bindings/2b481024a8665bd5b24ca40d28fe90cb4fb86ce0-on-9875ed9904be9d8967f578bd91121d0eafba4ba3.json) checks the actual community merge `040c785b5b35`. GitHub based that merge on `6866a9c6260d`. A clean Git merge with current community main `9875ed9904be` produced tree `3e23f0a33df1`. The complete old and new candidate Lean trees are identical. All 239 parent archives were downloaded and extracted again using the current community receipt. All 1,195 raw public, server, private and compiler IR digests matched the original stock records. The sources, package pins, proof settings and project dependency graph used by this workload matched. The compilation and timing records above come from the original Linux job. A community maintainer can request a default-target build with `gh workflow run build-pr.yml --repo leanprover-community/riemann-hypothesis --ref main -f mode=build -f pr_number=977`.

The [input comparison for author revision `989ea9c41e84`](bindings/989ea9c41e8400a6fe894fe365298c219f8c7e1d-on-5ba3d66a2a5acdcd70e2482d73e05b41d7116186.json) checks the actual community merge `e970187f4b8e`. GitHub based that merge on current community main `5ba3d66a2a5a`. The complete old and new candidate Lean trees are identical. All 239 parent archives were downloaded and extracted again using the current community receipt. All 1,195 raw public, server, private and compiler IR digests matched the original stock records. The sources, package pins, proof settings and project dependency graph used by this workload matched. The compilation and timing records above come from the original Linux job. A community maintainer can request a default-target build with `gh workflow run build-pr.yml --repo leanprover-community/riemann-hypothesis --ref main -f mode=build -f pr_number=977`.

The documentation-only community updates `0ba932f5613e` (AGENTS.md) each have a successful official receipt for the same source tree, map and module manifest.

The separate Ubuntu check ran on final author revision `989ea9c41e84`. All 60 native CI tests and all 12 focused clump tests passed. The complete script suite ran 308 tests with 0 skipped, including the focused suite. The job used Python 3.12.16, PyYAML 6.0.2, cp (GNU coreutils) 9.4 and the repository’s boto3 and botocore 1.44.9 pins. [Ubuntu job](https://github.com/aliromman/riemann-hypothesis/actions/runs/45410674890/job/138503244640) [Original test output](bindings/ubuntu-python-989ea9c41e8400a6fe894fe365298c219f8c7e1d.zip)
