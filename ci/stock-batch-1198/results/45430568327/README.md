# Stock Lake, kernel and timing records for PR #977

GitHub checked merge `19beb187eef5fd39b78be2d7bd81855b2b5a4327` of author head `c0228c0ae22d9cbf3e5466760718fd19111058ac` and community parent `1da818b50f1e18808db2792b9dc735bda8cb84d8`. The candidate source tree is `3944961f74ce15f369676a6052f0a6586707750d`. The successful parent cache manifest is `edc38df9198228480080821adb772f6c4109fdba7404a04be28bc49a250cb487`. [Original Linux run](https://github.com/aliromman/riemann-hypothesis/actions/runs/45430568327)

The stock Lake build covered 27 roots and 239 project modules. 29 modules had source changes, and 36 modules compiled from source. Across both sides the check compared 7,655 module-owned declarations, including 1,852 in changed modules. Lean replayed 6 selected roots. All compared names, types, theorem proofs, definition values, public exports and kernel declarations matched. The compiler-warning multisets matched after removal of source positions.

The structural check also required the raw public module and both compiler IR parts to match. The server and private module bytes differed in 33 and 25 modules.

## Bounded proof exports

Both predeclared targets belong to edited sources. Each revision produced the same proof trace for each theorem. The job ran stock `lake comparator` on those two exports with `--inadvisably-no-sandbox` on a disposable Ubuntu runner. It used the repository’s permitted axioms `propext`, `Quot.sound` and `Classical.choice`. Lean default, Lean paranoid and nanoda accepted both theorems. The full sandboxed five-claim check remains outstanding.

All three kernels also accepted a control in which `rfl` replaced the proof of `n + 0 = n`. In the two negative controls, statement comparison rejected `n * 1 = n` in place of `n + 0 = n`, and the axiom check rejected the added axiom `ComparisonControl.extra`. Both rejections occurred before kernel replay.

- `GlobalTheory.CompanionTheory.SW.Averaging.bijective_pair` used 3,149,696 bytes on each side. SHA-256 `31bf90c0ba09af45d2a9f9f99cc93265e87b6cd3824bb11016d34544ef565bf3`.
- `Formalism.LatticeBaseChangeAlt.four_term_sum_bound_of_parameters` used 50,380,642 bytes on each side. SHA-256 `9bf232ca29179dce903c72e3121754f9e639887a77f3072e88ef1ce68638c35b`.

## Inputs after community batch #1198

All 27 predeclared roots remained in the current project.

Among project modules common to both panels, 30 parent sources, 30 candidate sources, 29 ordered parent import lists, 31 archive digests and 35 Lake input hashes changed. The complete new panel includes 0 project modules outside the prior cone. The prior panel had 0 project modules outside the new cone. [Per-root changes](previous-inputs.json)

The complete theorem inputs and the fresh Lake workload match the preceding batch.

All current results and times below come from this Ubuntu job. The previous job ran on its own machine. [Earlier stock run](https://github.com/aliromman/riemann-hypothesis/actions/runs/45406473993)

The earlier runner reported image `20261116.133.1` and `Linux-7.0.0-1014-aws-x86_64-with-glibc2.39`. The current runner reported image `20261116.133.1` and `Linux-7.0.0-1014-aws-x86_64-with-glibc2.39`.

On that previous runner, the sum of single-module medians changed by -0.73% elapsed and -0.65% CPU. The previous fresh Lake workload changed by -0.27% elapsed and -0.24% CPU. Each percentage compares paired compilations on one runner.

The individual timing closures that changed in the new batch were `CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.AdmissibleOfIwasawa`, `GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteModuloGeneralEquation`, `GroundTheory.HeightsAndTheta.Heights.HeightKernels.AssemblySympl`, `PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.FinalTF`.

## Matched single-module compiler trials

All 12 predeclared sources ran on the same Ubuntu job. Each used a warm-up pair, then five alternating matched trials with one Lean thread and a fresh output directory for each compile. Both sides used the same pinned imported artifacts. CPU is child user plus system time. Elapsed includes compilation and creation of `.olean`, `.ilean` and C output. Hydration and declaration comparison were outside the timers.

| Source | Clump members | Parent CPU, s | Candidate CPU, s | CPU change | Parent elapsed, s | Candidate elapsed, s | Elapsed change | Slower CPU pairs | Slower elapsed pairs |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.AdmissibleOfIwasawa` | 2 | 0.724 | 0.725 | +0.19% | 0.728 | 0.732 | +0.62% | 2/5 | 3/5 |
| `CompanionTheory.AutomorphicTheory.BesselWaveGrids.NqMovedExample` | 7 | 5.670 | 5.686 | +0.29% | 5.654 | 5.685 | +0.54% | 3/5 | 3/5 |
| `Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularPairLiftToPrimePowerField` | 2 | 0.963 | 0.961 | -0.13% | 0.969 | 0.966 | -0.32% | 3/5 | 3/5 |
| `Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelRowsColumnsSquareIntegrable` | 27 | 8.152 | 8.068 | -1.03% | 8.105 | 8.022 | -1.02% | 3/5 | 3/5 |
| `Formalism.IncomingBounds.FlowDegreeBounds.ProdRangeEqFactorialMulProdIco` | 2 | 1.363 | 1.361 | -0.16% | 1.368 | 1.365 | -0.26% | 0/5 | 0/5 |
| `Formalism.GradedWeylDivisibility.FinalC` | 19 | 5.771 | 5.681 | -1.55% | 5.742 | 5.655 | -1.52% | 0/5 | 0/5 |
| `GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteModuloGeneralEquation` | 2 | 5.636 | 5.678 | +0.74% | 5.638 | 5.678 | +0.71% | 2/5 | 2/5 |
| `GroundTheory.HeightsAndTheta.Heights.HeightKernels.AssemblySympl` | 24 | 6.913 | 6.980 | +0.97% | 6.895 | 6.969 | +1.06% | 4/5 | 4/5 |
| `PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.AutomorphyFactorKernelAlgebraProof` | 3 | 3.061 | 3.000 | -1.96% | 3.060 | 3.000 | -1.97% | 1/5 | 1/5 |
| `PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.FinalTF` | 19 | 10.572 | 10.382 | -1.79% | 10.501 | 10.310 | -1.82% | 1/5 | 1/5 |
| `ReciprocityTheory.DualLattices.QExpansionMonoWCoeffZero` | 2 | 1.934 | 1.924 | -0.51% | 1.930 | 1.918 | -0.64% | 2/5 | 2/5 |
| `ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality` | 17 | 9.343 | 9.191 | -1.63% | 9.292 | 9.127 | -1.77% | 0/5 | 0/5 |

CPU sums of per-source medians were 60.100 → 59.639 seconds (-0.77%). 4 sources had a higher candidate median. The candidate was slower in 21/60 pairs. The parent and candidate ranges overlapped in 12/12 sources. Round sums differed by -0.80% to -0.35%.

For cpu time, the median within-pair change was -0.19% in the 30 trials that compiled the parent first, and -0.56% in the 30 trials that compiled the candidate first.

Elapsed sums of per-source medians were 59.883 → 59.426 seconds (-0.76%). 4 sources had a higher candidate median. The candidate was slower in 22/60 pairs. The parent and candidate ranges overlapped in 12/12 sources. Round sums differed by -0.81% to -0.26%.

For elapsed time, the median within-pair change was -0.15% in the 30 trials that compiled the parent first, and -0.65% in the 30 trials that compiled the candidate first.

Lean reported the same module, byte and constant import counts on each side for all 12 warm-up pairs.

## Fresh stock Lake workload

The two theorem roots and their project dependencies formed a complete workload of 4 modules, including the roots. Every run started with an empty project build directory and the same pinned package cache. All 4 modules compiled in each of twelve runs. Five measured pairs followed one warm-up pair. The timer covers Lake scheduling and compilation. The raw records list the actual compiled modules.

CPU medians were 14.014 → 14.000 seconds (-0.10%). The parent range was 13.941–14.050 seconds and the candidate range was 13.873–14.057 seconds. The candidate was slower in 1/5 pairs.

Elapsed medians were 12.540 → 12.552 seconds (+0.10%). The parent range was 12.503–12.582 seconds and the candidate range was 12.458–12.609 seconds. The candidate was slower in 3/5 pairs.

The community also published a successful receipt directly for GitHub’s first merge parent. It has the same project artifact map and module manifest as the donor used in this run. Its SHA-256 is `a6a11f580ac1cd82a43c7dedb0d255ad775c6af2a235035a384bb407d26a824f`. [Community receipt](https://rh-cache.taucetiproject.org/ci/revisions/1da818b50f1e18808db2792b9dc735bda8cb84d8.json)

These timings cover the measured sources and jobs. Whole-project build time requires a separate measurement.

The [default-target capacity record](default-build-capacity.json) includes the current receipt and map queries, a prior-parent stock extraction sample, observed standard runner space, and the community runner requirements. The current source graph has 11,551 edited modules and 41,962 edited or potentially downstream modules out of 59,908. Cache hits and Lake scheduling determine which of them an actual build executes. The exact author, merge and source-input keys had no public successful build receipt at the observation time.

To measure the space needed for a complete ordinary project restore, the stratified sample used 512 archives from the verified current parent. Stock `leantar` inspected 320 on this parent. For 192 previous observations, both the entire signed archive and Lake input key were identical. The sample files totaled 1,083,881,126 bytes. The stratified estimate is 65.63 GiB across the 59,908 modules, with an estimated sampling error of 2.14 GiB. Package dependencies, sources and build temporaries require additional space. The standard public job has 4 vCPUs, 16 GB RAM and a six-hour limit. The community full-build runner calls for 250 GiB free SSD and ideally 128 GiB memory. A maintainer can request the unchanged nine default targets with `gh workflow run build-pr.yml --repo leanprover-community/riemann-hypothesis --ref main -f mode=build -f pr_number=977`. [Sample and machine data](default-build-capacity.json) [Community workflow](https://github.com/leanprover-community/riemann-hypothesis/blob/1da818b50f1e18808db2792b9dc735bda8cb84d8/.github/workflows/build-pr.yml) [Standard Linux runners](https://docs.github.com/en/actions/reference/runners/github-hosted-runners) [Job limits](https://docs.github.com/en/actions/reference/limits)

The original Actions ZIP has SHA-256 `7c4a59966408dd2083824e72770ce1f61953ac38887c927e3a5c9e8fd303a3c6`. [Exact workflow and source manifest](https://github.com/aliromman/riemann-hypothesis/tree/907cdb7d158ed2af3ab7579b5e2271be094eced7/ci/stock-batch-1198)

The [input comparison for author revision `f6177155e8e4`](bindings/f6177155e8e440c0a831d4c15de4c74341de0a93-on-1da818b50f1e18808db2792b9dc735bda8cb84d8.json) checks the actual community merge `177babf54b6c`. GitHub based that merge on current community main `1da818b50f1e`. All 1 changed Lean files since the run fall outside this entire source and dependency cone. All 239 parent archives were downloaded and extracted again using the current community receipt. All 1,195 raw public, server, private and compiler IR digests matched the original stock records. The sources, package pins, proof settings and project dependency graph used by this workload matched. The compilation and timing records above come from the original Linux job. A community maintainer can request a default-target build with `gh workflow run build-pr.yml --repo leanprover-community/riemann-hypothesis --ref main -f mode=build -f pr_number=977`.

## Source sandbox and current head `f6177155e8e4`

The default Linux Bubblewrap Comparator compiled both named theorem sources from empty project outputs on this pull request. All three kernels accepted both results. All 12 raw public module, IR signature and full IR files for its 4 project sources matched the separate ordinary build. The alternate proof was accepted. The changed statement and extra axiom were rejected before kernel replay. Every source input to those sandboxed compilations also matches current GitHub preview `177babf54b6c42736e5040c9fec8f5e2a00864ff`. [Original sandbox results](https://github.com/aliromman/riemann-hypothesis/tree/4366fc4a54fe18b21b3dcda79770f37c682ad2ba/ci/source-sandbox/results/45431323026/)

The Ubuntu Python and compiler-diagnostic run used source `c0228c0ae22d9cbf3e5466760718fd19111058ac`. Later author `f6177155e8e440c0a831d4c15de4c74341de0a93` added one empty line to `QEqColPer.lean`, outside the 239-module project cone, the 12 standalone timings, the four-file fresh build and both theorem cones. All repository scripts, unit test files, compiler pins and diagnostic fixtures are identical. The original job passed 313 repository tests, 13 included clump tests, 60 native tests and four real compiler diagnostics. [Original Ubuntu logs](https://github.com/aliromman/riemann-hypothesis/tree/fae64fb569cba9e83bcf85ea565168726e8f0876/ci/clump-diagnostics/results/45430700016/)

All nine public author, merge and input-fingerprint cache routes returned 404 for this head. The public parent had a successful direct receipt. [Current project and cache binding](current-verification.json)
