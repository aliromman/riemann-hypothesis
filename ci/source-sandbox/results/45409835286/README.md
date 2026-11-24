# Four theorem sources checked inside Bubblewrap

The stock Lean Comparator built four named theorems inside its default sandbox on Ubuntu 22.04. Lean default, Lean paranoid and nanoda accepted each result. The ordinary namespace probe ran as user 1001 with bubblewrap 0.6.1. [Original Linux jobs](https://github.com/aliromman/riemann-hypothesis/actions/runs/45409835286)

The run fetched the public pull requests and checked every source SHA-256 in their complete project dependency cones. It compiled each trusted parent from source and reproduced the original proof export by size and SHA-256. Each candidate run began with an empty project output and cache directory and the same pinned Mathlib packages. Stock `lake comparator --challenge-from-export` then resolved the workspace, built and exported the candidate, compared the statements, checked the three allowed axioms and replayed all three kernels. The candidate's public module, IR signature and full IR from each compilation matched the corresponding earlier ordinary stock build byte for byte.

| PR | Theorem | Project modules compiled in its sandbox | Parent proof bytes |
|---|---|---:|---:|
| #879 | `GlobalTheory.CatCoh.commAlgFunctorCoboundaryZero_mem_cocyclesOne` | 1 | 4,888,069 |
| #879 | `GlobalTheory.TopForm.isBaseChange_exteriorPower` | 2 | 52,581,161 |
| #977 | `GlobalTheory.CompanionTheory.SW.Averaging.bijective_pair` | 3 | 3,149,696 |
| #977 | `Formalism.LatticeBaseChangeAlt.four_term_sum_bound_of_parameters` | 1 | 50,380,642 |

All three kernels accepted a control that supplied a different proof of the same statement. The statement checker rejected a changed proposition. The axiom checker rejected a proof using the new axiom `SandboxControl.extra`. Each negative control compiled and exported inside Bubblewrap before the expected rejection. Both negative controls stopped before kernel replay.

In the first Ubuntu 24.04 Python job, 60 native CI tests and 12 focused clump tests passed. Nine of 308 full script tests errored in setup. That job used the Ubuntu system Botocore, which lacked `load_client_plugins`. This explains the workflow’s failed overall status. Its independent source Comparator job passed. [Original Python output](python-suites.zip)

The corrected Python job checked final #977 author `989ea9c41e8400a6fe894fe365298c219f8c7e1d` with the repository’s boto3 and botocore 1.44.9 pins. It ran 60 native tests, 12 focused clump tests and 308 full script tests. The full script suite includes the focused tests and skipped 0. The complete Lean source tree, compiler and proof settings on this final author match the original timed and sandboxed revision. The binding rechecked all 1,195 authenticated parent facets in the 239-module cone. [Final Ubuntu job](https://github.com/aliromman/riemann-hypothesis/actions/runs/45410674890/job/138503244640) [Original final Python output](final-python-suites.zip) [Final source binding](final-clump-binding.json)

The project checks cover the four named source theorems. The nine default-target build and full five-claim sandboxed comparison of these pull requests remain separate obligations. [Original Comparator output](sandbox.zip) [Verified provenance and native output hashes](verified.json)
