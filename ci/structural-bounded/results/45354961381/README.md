# Stock Lake measurements and source verification

The measured build and the later source check ran on the public verification fork. The two ZIP files in this directory are byte-for-byte copies of the original GitHub artifacts. The source check read the original ZIP and the community's successful build receipt directly. [Source-binding job](https://github.com/aliromman/riemann-hypothesis/actions/runs/45360087383)

The published candidate was `bde5d32d9681e0e3b30295b53d7bdb45b6cf463a`, with community parent `e23fe94c20626997fceadcc817237335a0602c20`. All 204 measured Lean source blobs and their imported dependencies match the earlier run. 48 source files outside this dependency cone changed after measurement. Both versions of the community dependency reader found the same ordered import lists on both source sets. The official parent archive manifest contains 60,928 modules.

The full timing panel and the four-module stock Lake build showed small, mixed changes. Four of the twelve sources had higher CPU and wall-time medians. Measured ranges overlapped on eleven of the twelve. No whole-project time was measured.

The original stock-Lake ZIP has SHA-256 `f19dba0994ba94fd32119e086a5fba2865a66ce679a70dfb8701e527b3f1c728`. The source-binding ZIP has SHA-256 `58af4a402298237b0c74044c631f8b986f672f3df0b10fdcd3627eff1caf4d09`. The latter contains the same JSON as `source-binding.json`.

The fork ran the stock Lean build on source commit `b9be9b789d211a66c8918d22ef288d9d0a091a36` against community parent `d27f71347abceb76cd37dc8a5fccbe556ec2be90`. The source tree is `ea4eca26ea9220038083bd2c6c6313c0a2cba605`. The parent LTAR manifest is `18bf99f19a3357168a83dd5bb70bfb1836134646fb27bac2419611778c15bb2a`. [Linux run](https://github.com/aliromman/riemann-hypothesis/actions/runs/45354961381)

The six-library slice included 25 roots, 204 modules and 31 changed clumps. Lake rebuilt 36 checked sources. Lean compared 7,045 local declarations, including 1,998 in changed clumps. All proof terms, kernel declarations, public module bytes, IR bytes, IR signatures and compiler-warning multisets passed their checks. Lean replayed 6 roots. The raw server and private facet difference counts were 33 and 23.

The stock Comparator checked 2 exported theorem proofs with the repository’s axiom set. Lean default, Lean paranoid and nanoda accepted both. The three controls accepted an alternate proof, rejected an altered true statement and rejected an additional named axiom.

- `GlobalTheory.CompanionTheory.SW.Averaging.bijective_pair` had a 3,149,696-byte proof export on each revision. SHA-256 `31bf90c0ba09af45d2a9f9f99cc93265e87b6cd3824bb11016d34544ef565bf3`.
- `Formalism.LatticeBaseChangeAlt.four_term_sum_bound_of_parameters` had a 50,380,642-byte proof export on each revision. SHA-256 `9bf232ca29179dce903c72e3121754f9e639887a77f3072e88ef1ce68638c35b`.

## Individual compiler trials

Twelve changed clumps ran five matched trials per revision after a warm-up pair. The sum of per-module CPU medians went from 113.577 to 112.875 seconds (-0.62%). The sum of elapsed medians went from 113.038 to 112.409 seconds (-0.56%). Each compile used identical dependency artifacts and a fresh output directory. This is a stratified panel from six libraries.

| Library and module | Members | Parent CPU, s | Candidate CPU, s | CPU change | Parent elapsed, s | Candidate elapsed, s | Elapsed change | Slower pairs CPU / elapsed |
|---|---:|---:|---:|---:|---:|---:|---:|---|
| `CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.AdmissibleOfIwasawa` | 2 | 0.865 | 0.853 | -1.36% | 0.867 | 0.857 | -1.21% | 0 / 0 |
| `CompanionTheory.AutomorphicTheory.BesselWaveGrids.NqMovedExample` | 7 | 7.349 | 7.216 | -1.81% | 7.314 | 7.182 | -1.81% | 0 / 0 |
| `Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularPairLiftToPrimePowerField` | 2 | 1.186 | 1.182 | -0.27% | 1.188 | 1.183 | -0.48% | 2 / 2 |
| `Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelRowsColumnsSquareIntegrable` | 27 | 11.098 | 11.114 | +0.14% | 11.002 | 11.033 | +0.29% | 3 / 3 |
| `Formalism.IncomingBounds.FlowDegreeBounds.ProdRangeEqFactorialMulProdIco` | 2 | 1.825 | 1.811 | -0.78% | 1.827 | 1.814 | -0.73% | 0 / 0 |
| `Formalism.JumpKernelCokernel.LengthTheoremsWithEarlier` | 24 | 40.781 | 40.789 | +0.02% | 40.721 | 40.741 | +0.05% | 2 / 2 |
| `GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteModuloGeneralEquation` | 2 | 8.281 | 8.166 | -1.39% | 8.273 | 8.159 | -1.38% | 2 / 2 |
| `GroundTheory.HeightsAndTheta.Heights.HeightKernels.AssemblySympl` | 24 | 8.970 | 8.817 | -1.70% | 8.911 | 8.763 | -1.66% | 2 / 2 |
| `PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.AutomorphyFactorKernelAlgebraProof` | 3 | 3.937 | 3.952 | +0.39% | 3.925 | 3.945 | +0.52% | 3 / 3 |
| `PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.FinalTF` | 19 | 14.434 | 14.262 | -1.19% | 14.282 | 14.132 | -1.05% | 2 / 2 |
| `ReciprocityTheory.DualLattices.QExpansionMonoWCoeffZero` | 2 | 2.441 | 2.446 | +0.19% | 2.416 | 2.425 | +0.40% | 2 / 2 |
| `ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality` | 17 | 12.411 | 12.266 | -1.16% | 12.312 | 12.176 | -1.11% | 0 / 0 |

The aggregate CPU difference across five observed rounds ranged from -1.40% to +0.13%. Candidate CPU was higher in 18/60 pairs. The measured ranges overlapped in 11/12 modules.

The aggregate elapsed difference across five observed rounds ranged from -1.35% to +0.17%. Candidate elapsed was higher in 18/60 pairs. The measured ranges overlapped in 11/12 modules.

## Complete stock Lake builds

The two theorem roots and their entire 4-module project cone ran in a fresh Lake project build directory for each trial. All 4 project modules were observed compiling in every run. Official package dependencies were warm. Five timed pairs followed one warm-up pair.

CPU medians were 20.872 → 20.746 seconds (-0.60%). Parent and candidate ranges were 20.648–21.367 and 20.686–21.147 seconds. The candidate was slower in 2/5 pairs.

Elapsed medians were 18.857 → 18.770 seconds (-0.46%). Parent and candidate ranges were 18.674–19.286 and 18.681–19.095 seconds. The candidate was slower in 2/5 pairs.

The immutable GitHub artifact has SHA-256 `f19dba0994ba94fd32119e086a5fba2865a66ce679a70dfb8701e527b3f1c728`. [Verifier and source manifest](https://github.com/aliromman/riemann-hypothesis/tree/d8f3ee0119ccbd71c783f72c8e62907d0ec24ce6/ci/structural-bounded)
