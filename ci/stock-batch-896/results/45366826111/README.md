# Stock Lake, kernel and timing records for PR #977

GitHub checked merge `7caed4e13dfdb503dd13b79ccc6ef6e7699fb875` of author head `9db9c372b954b858261870086c953c60d07a2890` and community parent `c9883164b0b3d762cee21f889d03d59a53b3ba3b`. The candidate source tree is `2f3a5bc48d255b9683b700ec22411ab69d4b4efa`. The successful parent cache manifest is `a6cfc0b330c9b2d25551163316b4ae66dbd1b9006439c8f42621c177ec684463`. [Original Linux run](https://github.com/aliromman/riemann-hypothesis/actions/runs/45366826111)

The stock Lake build covered 27 roots and 239 project modules. 29 modules had source changes, and 36 modules compiled from source. Across both sides the check compared 7,655 module-owned declarations, including 1,852 in changed modules. Lean replayed 6 selected roots. All compared names, types, theorem proofs, definition values, public exports and kernel declarations matched. Both raw compiler IR parts and all compiler-warning multisets after removal of source positions matched.

The structural check also required the raw public module bytes to match. The server and private module bytes differed in 33 and 25 modules.

## Bounded proof exports

The predeclared theorem targets belong to actual changed sources. Both revisions produced identical exported proof traces for each theorem. The stock Comparator checked statements with the repository’s permitted axioms `propext`, `Quot.sound` and `Classical.choice`. Lean default, Lean paranoid and nanoda accepted both targets. An alternate proof passed. The two negative controls rejected a changed statement and an added named axiom. This scope does not include a five-claim export.

- `GlobalTheory.CompanionTheory.SW.Averaging.bijective_pair` used 3,149,696 bytes on each side. SHA-256 `31bf90c0ba09af45d2a9f9f99cc93265e87b6cd3824bb11016d34544ef565bf3`.
- `Formalism.LatticeBaseChangeAlt.four_term_sum_bound_of_parameters` used 50,380,642 bytes on each side. SHA-256 `9bf232ca29179dce903c72e3121754f9e639887a77f3072e88ef1ce68638c35b`.

## Panel changes for the merged batch

- `Formalism.JumpKernelCokernel.LengthTheoremsWithEarlier` → `Formalism.GradedWeylDivisibility.FinalC`. Original timing source is now protected; matched its library, member count and source bytes, with original cone and byte limits.
- `ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HHINDA` → `ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValNorm`. Original downstream no longer has its declared changed-source or direct dependency role; preserve library and change state, minimize extra ancestors.

## Matched single-module compiler trials

All 12 predeclared sources ran on the same Ubuntu job. Each used a warm-up pair, then five alternating matched trials with one Lean thread and a fresh output directory for each compile. Both sides used the same pinned imported artifacts. CPU is child user plus system time. Elapsed includes compilation and creation of `.olean`, `.ilean` and C output. Hydration and declaration comparison were outside the timers.

| Source | Clump members | Parent CPU, s | Candidate CPU, s | CPU change | Parent elapsed, s | Candidate elapsed, s | Elapsed change | Slower CPU pairs | Slower elapsed pairs |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.AdmissibleOfIwasawa` | 2 | 0.641 | 0.637 | -0.57% | 0.642 | 0.644 | +0.39% | 3/5 | 4/5 |
| `CompanionTheory.AutomorphicTheory.BesselWaveGrids.NqMovedExample` | 7 | 4.948 | 4.943 | -0.10% | 4.948 | 4.944 | -0.08% | 1/5 | 3/5 |
| `Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularPairLiftToPrimePowerField` | 2 | 0.864 | 0.856 | -0.94% | 0.868 | 0.863 | -0.56% | 1/5 | 2/5 |
| `Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelRowsColumnsSquareIntegrable` | 27 | 7.261 | 7.204 | -0.79% | 7.224 | 7.165 | -0.82% | 1/5 | 1/5 |
| `Formalism.IncomingBounds.FlowDegreeBounds.ProdRangeEqFactorialMulProdIco` | 2 | 1.236 | 1.230 | -0.44% | 1.236 | 1.236 | +0.04% | 2/5 | 3/5 |
| `Formalism.GradedWeylDivisibility.FinalC` | 19 | 5.092 | 5.058 | -0.67% | 5.061 | 5.036 | -0.49% | 1/5 | 1/5 |
| `GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteModuloGeneralEquation` | 2 | 5.496 | 5.546 | +0.91% | 5.496 | 5.542 | +0.84% | 5/5 | 5/5 |
| `GroundTheory.HeightsAndTheta.Heights.HeightKernels.AssemblySympl` | 24 | 6.035 | 5.986 | -0.82% | 6.022 | 5.975 | -0.78% | 1/5 | 1/5 |
| `PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.AutomorphyFactorKernelAlgebraProof` | 3 | 2.633 | 2.618 | -0.56% | 2.628 | 2.618 | -0.37% | 1/5 | 2/5 |
| `PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.FinalTF` | 19 | 9.139 | 9.055 | -0.92% | 9.090 | 8.998 | -1.02% | 0/5 | 0/5 |
| `ReciprocityTheory.DualLattices.QExpansionMonoWCoeffZero` | 2 | 1.756 | 1.766 | +0.56% | 1.751 | 1.761 | +0.57% | 2/5 | 3/5 |
| `ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality` | 17 | 8.032 | 8.099 | +0.84% | 7.993 | 8.056 | +0.79% | 1/5 | 1/5 |

CPU sums of per-source medians were 53.133 → 52.998 seconds (-0.25%). 3 sources had a higher candidate median. The candidate was slower in 19/60 pairs. The parent and candidate ranges overlapped in 11/12 sources. Round sums differed by -1.23% to -0.09%.

Elapsed sums of per-source medians were 52.959 → 52.838 seconds (-0.23%). 5 sources had a higher candidate median. The candidate was slower in 26/60 pairs. The parent and candidate ranges overlapped in 11/12 sources. Round sums differed by -1.22% to -0.08%.

Lean reported the same module, byte and constant import counts on each side for all 12 warm-up pairs.

## Fresh stock Lake workload

The two genuine theorem roots and all 4 project dependencies and roots formed a complete project workload. Every run started with an empty project build directory and the same pinned package cache. All 4 modules compiled in each of twelve runs. Five measured pairs followed one warm-up pair. The timer covers Lake scheduling and compilation. The raw records list the actual compiled modules.

CPU medians were 13.052 → 12.968 seconds (-0.65%). The parent range was 12.982–13.117 seconds and the candidate range was 12.921–13.421 seconds. The candidate was slower in 1/5 pairs.

Elapsed medians were 11.723 → 11.699 seconds (-0.20%). The parent range was 11.695–11.802 seconds and the candidate range was 11.631–12.080 seconds. The candidate was slower in 1/5 pairs.

The timings apply to these measured sources and jobs. No whole-project compile time was measured.

The [default-target capacity record](default-build-capacity.json) includes the current receipt and map queries, a prior-parent stock extraction sample, observed standard runner space, and the community runner requirements. The current source graph has 11,647 edited modules and 42,544 edited or potentially downstream modules out of 60,629. Cache hits and Lake scheduling determine which of them an actual build executes. The exact author, merge and source-input keys had no public successful build receipt at the observation time.

The original Actions ZIP has SHA-256 `033b1fd213ca3efcdc84afae11b12eb4b69805570fea8bb429980112e61698a2`. [Exact workflow and source manifest](https://github.com/aliromman/riemann-hypothesis/tree/ffb4517637cb5f9999a64ee09421290a1af93178/ci/stock-batch-896)

The [input comparison for author revision `34177e76b3d6`](bindings/34177e76b3d63c96565710dd9977ba7155427e13.json) checks the actual community merge `35ca2479f6b0`. The complete old and new candidate Lean trees are identical. All 239 parent archives were downloaded and validated again. The sources, package pins, proof settings and project dependency graph used by this workload matched. The compilation and timing records above come from the original Linux job.

The [input comparison for author revision `34177e76b3d6`](bindings/34177e76b3d63c96565710dd9977ba7155427e13-on-2d0c622a3464ba41ad98fca9086bab54fb74e303.json) checks the actual community merge `35ca2479f6b0`. GitHub based that merge on `73958da58a8a`. A clean Git merge with current community main `2d0c622a3464` produced tree `14c5bbf4604f`. The complete old and new candidate Lean trees are identical. All 239 parent archives were downloaded and extracted again using the current community receipt. All 1,195 raw public, server, private and compiler IR digests matched the original stock records. The sources, package pins, proof settings and project dependency graph used by this workload matched. The compilation and timing records above come from the original Linux job. A community maintainer can request a default-target build with `gh workflow run build-pr.yml --repo leanprover-community/riemann-hypothesis --ref main -f mode=build -f pr_number=977`.

The [input comparison for author revision `afa442082109`](bindings/afa44208210943a202ad969173b6317d06c37420-on-cb4dc6e23a6187db392c96664295415c55b6b01e.json) checks the actual community merge `9ea85f253787`. GitHub based that merge on current community main `cb4dc6e23a61`. All 68 changed Lean files since the run fall outside this entire source and dependency cone. All 239 parent archives were downloaded and extracted again using the current community receipt. All 1,195 raw public, server, private and compiler IR digests matched the original stock records. The sources, package pins, proof settings and project dependency graph used by this workload matched. The compilation and timing records above come from the original Linux job. A community maintainer can request a default-target build with `gh workflow run build-pr.yml --repo leanprover-community/riemann-hypothesis --ref main -f mode=build -f pr_number=977`.
