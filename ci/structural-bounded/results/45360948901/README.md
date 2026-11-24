# Final stock Lake check for PR #977

GitHub built merge `483fb485bd20e7a45a09f41ea0eec36a3c1827e5` of PR head `1ae1f79ed3f27986e4493a1c8fb6e21455d7467a` and upstream `86b7a0de35098e42e2f7e695f3c82e086f3deae4`. The complete candidate source tree was `e4578d9cb1c96062bc9a81dbb3cb3aae8156cd6e`. The official parent archive manifest was `18bf99f19a3357168a83dd5bb70bfb1836134646fb27bac2419611778c15bb2a`. [Final Linux job](https://github.com/aliromman/riemann-hypothesis/actions/runs/45360948901)

Stock Lake rebuilt 36 sources in a 204-module dependency cone across six source libraries, with 25 roots, 31 changed clumps and 10 selected direct-consumer cases. Lean compared 7,045 module-owned declarations, including 1,998 in changed clumps. Public images, kernel declarations, proof expressions, both compiler IR facets and warning text after removal of source positions matched. Lean replayed 6 selected roots. Raw server images differed in 33 modules and raw private images in 23.

The stock Comparator compared two sets of exported theorem proofs in its direct trace mode. The permitted axioms were `propext`, `Quot.sound` and `Classical.choice`. Lean default, Lean paranoid and nanoda accepted both proofs. The three controls accepted a different proof of the same statement, rejected a different true statement and rejected an added named axiom. These two targets cover part of the source graph. The combined five-claim export was outside this workload.

- `GlobalTheory.CompanionTheory.SW.Averaging.bijective_pair` produced 3,149,696 identical bytes per revision. SHA-256 `31bf90c0ba09af45d2a9f9f99cc93265e87b6cd3824bb11016d34544ef565bf3`.
- `Formalism.LatticeBaseChangeAlt.four_term_sum_bound_of_parameters` produced 50,380,642 identical bytes per revision. SHA-256 `9bf232ca29179dce903c72e3121754f9e639887a77f3072e88ef1ce68638c35b`.

## Timing the revised source

The original Linux job selected twelve changed clumps before measurement. One of their sources changed in the published follow-up. The final job recomputed the full project import closure of each timed root and compared source blobs against that original checkout. It found exactly one affected timed root. Each single-module trial used one Lean thread, a fresh output directory, identical imported artifacts, one warm-up pair and five measured pairs in alternating order.

The final job compiled `Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelRowsColumnsSquareIntegrable` (27 members).

CPU medians were 7.455 → 7.413 seconds (-0.56%). The parent range was 7.364–7.577 seconds. The candidate range was 7.356–7.588 seconds. The candidate was slower in 2/5 pairs.

Elapsed medians were 7.419 → 7.363 seconds (-0.75%). The parent range was 7.324–7.530 seconds. The candidate range was 7.310–7.538 seconds. The candidate was slower in 2/5 pairs.

## The eleven unchanged timing roots

These sources and all their project dependencies match the first Linux job. Their measurements come from that earlier runner. The table gives parent and candidate medians in seconds. Each change is the percentage of its parent median. [Original run](https://github.com/aliromman/riemann-hypothesis/actions/runs/45354961381)

| Library and module | Parent CPU | Candidate CPU | CPU change | Parent elapsed | Candidate elapsed | Elapsed change |
|---|---:|---:|---:|---:|---:|---:|
| `CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.AdmissibleOfIwasawa` | 0.865 | 0.853 | -1.36% | 0.867 | 0.857 | -1.21% |
| `CompanionTheory.AutomorphicTheory.BesselWaveGrids.NqMovedExample` | 7.349 | 7.216 | -1.81% | 7.314 | 7.182 | -1.81% |
| `Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularPairLiftToPrimePowerField` | 1.186 | 1.182 | -0.27% | 1.188 | 1.183 | -0.48% |
| `Formalism.IncomingBounds.FlowDegreeBounds.ProdRangeEqFactorialMulProdIco` | 1.825 | 1.811 | -0.78% | 1.827 | 1.814 | -0.73% |
| `Formalism.JumpKernelCokernel.LengthTheoremsWithEarlier` | 40.781 | 40.789 | +0.02% | 40.721 | 40.741 | +0.05% |
| `GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteModuloGeneralEquation` | 8.281 | 8.166 | -1.39% | 8.273 | 8.159 | -1.38% |
| `GroundTheory.HeightsAndTheta.Heights.HeightKernels.AssemblySympl` | 8.970 | 8.817 | -1.70% | 8.911 | 8.763 | -1.66% |
| `PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.AutomorphyFactorKernelAlgebraProof` | 3.937 | 3.952 | +0.39% | 3.925 | 3.945 | +0.52% |
| `PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.FinalTF` | 14.434 | 14.262 | -1.19% | 14.282 | 14.132 | -1.05% |
| `ReciprocityTheory.DualLattices.QExpansionMonoWCoeffZero` | 2.441 | 2.446 | +0.19% | 2.416 | 2.425 | +0.40% |
| `ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality` | 12.411 | 12.266 | -1.16% | 12.312 | 12.176 | -1.11% |

CPU sums of eleven per-source medians were 102.479 → 101.761 seconds (-0.70%). The candidate had a higher median on 3/11 sources and was slower in 15/55 matched trials.

Elapsed sums of eleven per-source medians were 102.037 → 101.376 seconds (-0.65%). The candidate had a higher median on 3/11 sources and was slower in 15/55 matched trials.

## Fresh four-module stock Lake runs

The final runner also timed a complete stock Lake project workload for the two theorem roots, including all four project modules. Every trial started with an empty project build directory and the same pinned package cache. Lake compiled all four project modules in each of twelve runs. Five measured pairs followed one warm-up pair. Post-build proof and artifact comparisons took place outside the timer. These are fresh timings on the final runner.

CPU medians were 13.351 → 13.221 seconds (-0.98%). Parent range 13.128–13.570 seconds. Candidate range 13.200–13.360 seconds. The candidate was slower in 2/5 pairs.

Elapsed medians were 12.015 → 11.917 seconds (-0.82%). Parent range 11.818–12.222 seconds. Candidate range 11.904–12.014 seconds. The candidate was slower in 2/5 pairs.

The paired measurements describe these sources and include observed regressions. The two GitHub runners were separate machines. No twelve-module aggregate combines their times. No whole-repository compile time was measured.

The original final-run ZIP has SHA-256 `1468f95581d1a0e8a88f3977388bb93c9255df81a6584cae91db01024f89d7a9`. [Verifier, configuration and predeclared panel](https://github.com/aliromman/riemann-hypothesis/tree/31d6b43c0605c770623667fbf3d1e381290cc53c/ci/structural-bounded)
