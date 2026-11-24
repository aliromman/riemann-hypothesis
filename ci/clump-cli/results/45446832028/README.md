# Full-checkout planner and saved-plan measurements

The stock CLI ran on all 59,884 tracked Lean files from Git revision `963ebea3bb3d7c2c5738946fca45317b8084f972` on Ubuntu 24.04. The driver verified every source before and after the run. Each tool ran in a fresh process. The two planners and three apply implementations each had one warm-up and five scored trials. The order alternated within each command. [Original Ubuntu job](https://github.com/aliromman/riemann-hypothesis/actions/runs/45446832028/job/138632800911)

| Command | Git revision | Elapsed median, s | CPU median, s | Peak RSS median, MiB |
|---|---|---:|---:|---:|
| plan | `70f5e2c0737a` (published) | 19.926 | 19.768 | 3570.75 |
| plan | `963ebea3bb3d` (proposed) | 18.697 | 18.698 | 702.03 |
| apply | `307cef33f046` (community) | 17.050 | 16.882 | 3412.24 |
| apply | `70f5e2c0737a` (published) | 0.310 | 0.315 | 69.89 |
| apply | `963ebea3bb3d` (proposed) | 0.307 | 0.312 | 69.89 |

## Matched outcomes

| Command | Baseline | Elapsed change | Slower pairs | CPU change | Slower pairs | Peak RSS change | Higher pairs |
|---|---|---:|---:|---:|---:|---:|---:|
| plan | published | -6.17% | 0/5 | -5.41% | 0/5 | -80.34% | 0/5 |
| apply | community | -98.20% | 0/5 | -98.15% | 0/5 | -97.95% | 0/5 |
| apply | published | -0.80% | 1/5 | -0.90% | 1/5 | +0.00% | 0/5 |

All 12 planner calls produced the same 199-clump plan and identical joined output. A separate process retained normal stdout and stderr and reproduced the independently computed output bytes. All three apply commands recovered all 656 members, removed the expected 457 subordinate files and restored the checkout. The two proposed versions produced identical archives across all 199 roots. The community tool uses its earlier archive layout. [Plan and outputs](original-actions.zip)

The same machine ran all matched trials. Wall time includes the subprocess. CPU time is the user and system time charged to the child. Peak RSS is per process. These measurements cover the Python commands. The ZIP includes the exact three tool sources, timing driver, environment, saved plan, raw trials and both output streams. Its SHA-256 is `79bb234548b459b0916f2f1473d9d34d122cb602f8b5ca8132565ed0026a85c2`. [Raw observations](observations.jsonl) [Paired trials, increases, ties and ranges](verified.json)
