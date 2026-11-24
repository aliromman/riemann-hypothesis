# Stock Lake, kernel and timing records for PR #977

GitHub checked merge `25957d64bc7e20ccc2848be576b3a3092f4510d2` of author head `70e09b0994fce225e678b4808941de89c27a763b` and community parent `5f2c8594adf1f48032d37583118512cd7bbf3afa`. The candidate source tree is `445477315d15f0c5eaea8c076b18063ebd7a17a6`. The successful parent cache manifest is `79edef3a77b0086faf52d4f0df0a9b26b58e45826de20a57def3d5559d6ebe89`. [Original Linux run](https://github.com/aliromman/riemann-hypothesis/actions/runs/45386999286)

The stock Lake build covered 27 roots and 239 project modules. 29 modules had source changes, and 36 modules compiled from source. Across both sides the check compared 7,659 module-owned declarations, including 1,852 in changed modules. Lean replayed 6 selected roots. All compared names, types, theorem proofs, definition values, public exports and kernel declarations matched. The compiler-warning multisets matched after removal of source positions.

The structural check also required the raw public module and both compiler IR parts to match. The server and private module bytes differed in 33 and 25 modules.

## Bounded proof exports

The predeclared theorem targets belong to actual changed sources. Both revisions produced identical exported proof traces for each theorem. The stock Comparator checked statements with the repository’s permitted axioms `propext`, `Quot.sound` and `Classical.choice`. Lean default, Lean paranoid and nanoda accepted both targets. An alternate proof passed. The two negative controls rejected a changed statement and an added named axiom. The full five-claim export remains a separate check.

- `GlobalTheory.CompanionTheory.SW.Averaging.bijective_pair` used 3,149,696 bytes on each side. SHA-256 `31bf90c0ba09af45d2a9f9f99cc93265e87b6cd3824bb11016d34544ef565bf3`.
- `Formalism.LatticeBaseChangeAlt.four_term_sum_bound_of_parameters` used 50,380,642 bytes on each side. SHA-256 `9bf232ca29179dce903c72e3121754f9e639887a77f3072e88ef1ce68638c35b`.

The upstream module cache donor `bb9476b875a219608a9068f8f18d8c56b4e7f1ca` and the actual GitHub merge parent have the same complete Lean source tree `fd6cca42e515165d98659a81ff24b5c84b71ece6`, package pins and frozen verification inputs.

## Inputs after community batch #1018

All 27 predeclared roots remained in the current project. Relative to the previous batch, 6 parent sources and 6 candidate sources in the complete panel changed. The number of changed direct import lists on the parent side was 1. The number of changed archive digests was 7, and 7 Lake input hashes changed. The job ran the stock build and comparison for this complete panel on the current merge. [Per-root changes](previous-inputs.json)

The project inputs for both selected theorem closures and the complete fresh Lake workload match the preceding batch. The results and times below all come from the new Ubuntu job. The previous job ran on its own machine. [Earlier stock run](https://github.com/aliromman/riemann-hypothesis/actions/runs/45366826111)

On that previous runner, the sum of single-module medians changed by -0.23% elapsed and -0.25% CPU. The previous fresh Lake workload changed by -0.20% elapsed and -0.65% CPU. Each percentage compares paired compilations on one runner.

The individual timing closures that changed in the new batch were `PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.FinalTF`, `ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality`.

## Matched single-module compiler trials

All 12 predeclared sources ran on the same Ubuntu job. Each used a warm-up pair, then five alternating matched trials with one Lean thread and a fresh output directory for each compile. Both sides used the same pinned imported artifacts. CPU is child user plus system time. Elapsed includes compilation and creation of `.olean`, `.ilean` and C output. Hydration and declaration comparison were outside the timers.

| Source | Clump members | Parent CPU, s | Candidate CPU, s | CPU change | Parent elapsed, s | Candidate elapsed, s | Elapsed change | Slower CPU pairs | Slower elapsed pairs |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.AdmissibleOfIwasawa` | 2 | 0.871 | 0.877 | +0.67% | 0.874 | 0.879 | +0.57% | 4/5 | 4/5 |
| `CompanionTheory.AutomorphicTheory.BesselWaveGrids.NqMovedExample` | 7 | 7.415 | 7.137 | -3.75% | 7.387 | 7.115 | -3.69% | 1/5 | 1/5 |
| `Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularPairLiftToPrimePowerField` | 2 | 1.235 | 1.257 | +1.76% | 1.236 | 1.258 | +1.77% | 2/5 | 2/5 |
| `Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelRowsColumnsSquareIntegrable` | 27 | 11.117 | 11.446 | +2.96% | 11.032 | 11.361 | +2.98% | 3/5 | 3/5 |
| `Formalism.IncomingBounds.FlowDegreeBounds.ProdRangeEqFactorialMulProdIco` | 2 | 1.909 | 1.905 | -0.21% | 1.908 | 1.909 | +0.08% | 3/5 | 3/5 |
| `Formalism.GradedWeylDivisibility.FinalC` | 19 | 7.497 | 7.417 | -1.07% | 7.445 | 7.359 | -1.15% | 0/5 | 0/5 |
| `GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteModuloGeneralEquation` | 2 | 8.479 | 8.383 | -1.14% | 8.473 | 8.376 | -1.14% | 2/5 | 2/5 |
| `GroundTheory.HeightsAndTheta.Heights.HeightKernels.AssemblySympl` | 24 | 9.860 | 9.958 | +1.00% | 9.796 | 9.902 | +1.09% | 2/5 | 2/5 |
| `PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.AutomorphyFactorKernelAlgebraProof` | 3 | 4.049 | 4.062 | +0.32% | 4.042 | 4.056 | +0.35% | 2/5 | 2/5 |
| `PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.FinalTF` | 19 | 14.624 | 14.328 | -2.02% | 14.479 | 14.201 | -1.93% | 2/5 | 2/5 |
| `ReciprocityTheory.DualLattices.QExpansionMonoWCoeffZero` | 2 | 2.432 | 2.415 | -0.68% | 2.408 | 2.393 | -0.62% | 1/5 | 1/5 |
| `ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality` | 17 | 12.238 | 12.101 | -1.12% | 12.151 | 12.005 | -1.21% | 1/5 | 1/5 |

CPU sums of per-source medians were 81.725 → 81.285 seconds (-0.54%). 5 sources had a higher candidate median. The candidate was slower in 23/60 pairs. The parent and candidate ranges overlapped in 12/12 sources. Round sums differed by -1.20% to +0.89%.

Elapsed sums of per-source medians were 81.231 → 80.813 seconds (-0.51%). 6 sources had a higher candidate median. The candidate was slower in 23/60 pairs. The parent and candidate ranges overlapped in 12/12 sources. Round sums differed by -1.18% to +0.92%.

Lean reported the same module, byte and constant import counts on each side for all 12 warm-up pairs.

## Fresh stock Lake workload

The two theorem roots and their project dependencies formed a complete workload of 4 modules, including the roots. Every run started with an empty project build directory and the same pinned package cache. All 4 modules compiled in each of twelve runs. Five measured pairs followed one warm-up pair. The timer covers Lake scheduling and compilation. The raw records list the actual compiled modules.

CPU medians were 20.901 → 20.839 seconds (-0.29%). The parent range was 20.738–20.979 seconds and the candidate range was 20.812–20.916 seconds. The candidate was slower in 3/5 pairs.

Elapsed medians were 18.815 → 18.835 seconds (+0.11%). The parent range was 18.708–18.914 seconds and the candidate range was 18.800–18.901 seconds. The candidate was slower in 3/5 pairs.

These timings cover the measured sources and jobs. Whole-project build time requires a separate measurement.

The [default-target capacity record](default-build-capacity.json) includes the current receipt and map queries, a prior-parent stock extraction sample, observed standard runner space, and the community runner requirements. The current source graph has 11,579 edited modules and 42,415 edited or potentially downstream modules out of 60,492. Cache hits and Lake scheduling determine which of them an actual build executes. The exact author, merge and source-input keys had no public successful build receipt at the observation time.

To measure the space needed for a complete ordinary project restore, stock `leantar` unpacked 512 archives from the verified current parent. The extracted files totaled 1,101,123,255 bytes. The stratified estimate is 68.09 GiB across the 60,492 modules, with an estimated sampling error of 2.23 GiB. Package dependencies, sources and build temporaries require additional space. The standard public job has 4 vCPUs, 16 GB RAM and a six-hour limit. The community full-build runner calls for 250 GiB free SSD and ideally 128 GiB memory. A maintainer can request the unchanged nine default targets with `gh workflow run build-pr.yml --repo leanprover-community/riemann-hypothesis --ref main -f mode=build -f pr_number=977`. [Sample and machine data](default-build-capacity.json) [Community workflow](https://github.com/leanprover-community/riemann-hypothesis/blob/5f2c8594adf1f48032d37583118512cd7bbf3afa/.github/workflows/build-pr.yml) [Standard Linux runners](https://docs.github.com/en/actions/reference/runners/github-hosted-runners) [Job limits](https://docs.github.com/en/actions/reference/limits)

The original Actions ZIP has SHA-256 `7d677ebf0a4715a8f191109229d852a7bad5184817edaa702fc845e08cf4c946`. [Exact workflow and source manifest](https://github.com/aliromman/riemann-hypothesis/tree/1ce87c66afc8e96552387acdd62b787745a8c150/ci/stock-batch-1018)

The [input comparison for author revision `f3e19bf8371a`](bindings/f3e19bf8371ab5dd383b81e008ec14c4b0331811-on-06e06ac0873112b46d8f4f6b7ad7922f649c5273.json) checks the actual community merge `cc98ee93408f`. GitHub based that merge on `5f2c8594adf1`. A clean Git merge with current community main `06e06ac08731` produced tree `29690562eabf`. The complete old and new candidate Lean trees are identical. All 239 parent archives were downloaded and extracted again using the current community receipt. All 1,195 raw public, server, private and compiler IR digests matched the original stock records. The sources, package pins, proof settings and project dependency graph used by this workload matched. The compilation and timing records above come from the original Linux job. A community maintainer can request a default-target build with `gh workflow run build-pr.yml --repo leanprover-community/riemann-hypothesis --ref main -f mode=build -f pr_number=977`.

The separate Ubuntu check ran on the exact final author revision `f3e19bf8371a`. All 60 native CI tests and all 12 clump regression tests passed with Python 3.12.3, PyYAML 6.0.1 and cp (GNU coreutils) 9.4. [Ubuntu job](https://github.com/aliromman/riemann-hypothesis/actions/runs/45391097480) [Original test output](bindings/ubuntu-python-f3e19bf8371ab5dd383b81e008ec14c4b0331811.zip)
