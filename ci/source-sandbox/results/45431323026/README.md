# Four theorem sources checked inside Bubblewrap

The pinned community Comparator built four named theorems inside its default sandbox on Ubuntu 22.04. Lean default, Lean paranoid and nanoda accepted each result. The ordinary namespace probe ran as user 1001 with bubblewrap 0.6.1. [Original Linux job](https://github.com/aliromman/riemann-hypothesis/actions/runs/45431323026/job/138577096801)

The job fetched the public pull requests. It checked every source SHA-256 in their full project dependency cones. It compiled each trusted parent from source and reproduced the named proof export by size and SHA-256. Each candidate comparison started with empty project outputs and the same pinned Mathlib packages. Stock `lake comparator --challenge-from-export` resolved the workspace, built and exported the solution, compared the statements, checked the three permitted axioms and replayed all three kernels. The public module and both IR files from the sandboxed builds matched the fresh ordinary stock Lake output byte for byte.

| PR | Theorem | Project modules compiled | Parent proof bytes |
|---|---|---:|---:|
| #879 | `GlobalTheory.CatCoh.commAlgFunctorCoboundaryZero_mem_cocyclesOne` | 1 | 4,888,069 |
| #879 | `GlobalTheory.TopForm.isBaseChange_exteriorPower` | 2 | 52,581,161 |
| #977 | `GlobalTheory.CompanionTheory.SW.Averaging.bijective_pair` | 3 | 3,149,696 |
| #977 | `Formalism.LatticeBaseChangeAlt.four_term_sum_bound_of_parameters` | 1 | 50,380,642 |

The three kernels also accepted a different proof of a control statement. The statement checker rejected a changed proposition. The axiom checker rejected a new axiom, `SandboxControl.extra`. Both negative controls built and exported genuine Lean source inside Bubblewrap before the expected rejection. Their kernel steps were skipped.

The separate Ubuntu 24.04 job ran 313 repository script tests, 13 included clump tests, 60 native CI tests and four actual stock Lake diagnostic controls on the same author and source. [Python and compiler logs](https://github.com/aliromman/riemann-hypothesis/tree/fae64fb569cba9e83bcf85ea565168726e8f0876/ci/clump-diagnostics/results/45430700016/)

The sandbox verified these four named theorems on each independently proposed pull request. A complete nine-target Lake build and full five-claim sandboxed comparison are separate checks. [Original Comparator output](sandbox.zip) [Verified source bindings and compiled file hashes](verified.json)
