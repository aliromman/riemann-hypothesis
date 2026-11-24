# Source check for the changed theorem inside Bubblewrap

The pinned community Comparator built the affected named theorem inside its default sandbox on Ubuntu 22.04. Lean default, Lean paranoid and nanoda accepted each result. The ordinary namespace probe ran as user 1001 with bubblewrap 0.6.1. [Original Linux job](https://github.com/aliromman/riemann-hypothesis/actions/runs/45446517890/job/138631661610)

The job fetched the current community parent and the exact public fork revision. It checked the source SHA-256 of all three project modules in this theorem’s dependency cone. It compiled each trusted parent from source and reproduced the named proof export by size and SHA-256. Each candidate comparison started with empty project outputs and the same pinned Mathlib packages. Stock `lake comparator --challenge-from-export` resolved the workspace, built and exported the solution, compared the statements, checked the three permitted axioms and replayed all three kernels. The public module and both IR files from the sandboxed builds matched the fresh ordinary stock Lake output byte for byte.

| PR | Theorem | Project modules compiled | Parent proof bytes |
|---|---|---:|---:|
| #977 | `GlobalTheory.CompanionTheory.SW.Averaging.bijective_pair` | 3 | 3,149,696 |

The three kernels also accepted a different proof of a control statement. The statement checker rejected a changed proposition. The axiom checker rejected a new axiom, `SandboxControl.extra`. Both negative controls built and exported genuine Lean source inside Bubblewrap before the expected rejection. Their kernel steps were skipped.

This sandbox job verified the single source workload with changed batch 1266 inputs. The other three previously verified theorem workloads had identical source and dependency inputs. A complete nine-target Lake build and full five-claim sandboxed comparison are separate checks. [Original Comparator output](sandbox.zip) [Verified source bindings and compiled file hashes](verified.json)
