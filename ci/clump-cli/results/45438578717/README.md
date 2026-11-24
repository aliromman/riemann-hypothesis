# Full-checkout clump CLI timings

The stock clump CLI ran on a complete checkout of proposed renderer revision `e7127ce8136d8ed36e610884d8578de1cffadd19` in a fresh Ubuntu 24.04 job. The driver matched all 59,909 tracked Lean files to their Git blob IDs before and after the experiment. The previously published f617 planner and the proposed e712 planner produced the same saved plan on every trial. It contains 199 clumps and 656 members. [Actual Ubuntu job](https://github.com/aliromman/riemann-hypothesis/actions/runs/45438578717/job/138603047345)

Each of 30 invocations used a fresh Python process. Five warm-up invocations preceded the scored rounds within their command. Each implementation had five scored observations. The planner order alternated. The three apply implementations rotated and reversed order. CPU time includes user and system time charged by `wait4`. Peak RSS is reported for each child in bytes. The Linux runner used 3.12.16, 4 available processors and 15.61 GiB RAM. Setup and all independent comparisons ran outside the timers.

| Command | Implementation | Elapsed median, s | CPU median, s | Peak RSS median, MiB |
|---|---|---:|---:|---:|
| plan | `f6177155e8e4` (published) | 31.205 | 30.467 | 3591.26 |
| plan | `e7127ce8136d` (proposed) | 31.633 | 30.887 | 3603.16 |
| apply | `1da818b50f1e` (community) | 27.001 | 26.373 | 3439.42 |
| apply | `f6177155e8e4` (published) | 0.633 | 0.622 | 69.18 |
| apply | `e7127ce8136d` (proposed) | 0.501 | 0.490 | 69.18 |

## Matched outcomes

| Command | Reference to proposed | Elapsed change | Slower elapsed pairs | CPU change | Slower CPU pairs | Peak RSS change | Higher RSS pairs |
|---|---|---:|---:|---:|---:|---:|---:|
| plan | published | +1.37% | 5/5 | +1.38% | 5/5 | +0.33% | 5/5 |
| apply | community | -98.15% | 0/5 | -98.14% | 0/5 | -97.99% | 0/5 |
| apply | published | -20.85% | 0/5 | -21.29% | 0/5 | +0.00% | 0/5 |

The current and proposed archives had identical bytes at every one of the 199 generated roots on every apply. The community implementation uses its older archive layout. All three implementations recovered all 656 original members byte for byte and removed the expected 457 subordinate files. The driver restored the original files outside the timer after every application. The saved plan has SHA-256 `7f008f70f550f162cba7e1b23b8b15309086d8efd3ff8c0c4a2ff9ed4521a175`.

These observations measure the normal Python planning and saved-plan application commands on one checkout and one Linux machine. Lean compilation timings are recorded separately. [Exact driver and Git source bindings](https://github.com/aliromman/riemann-hypothesis/tree/08169693a59bf67b669ec41c94687b480bd0e7f8/ci/clump-cli) [Raw trials](observations.jsonl) [Trial ranges, medians, increases and ties](verified.json)

The original Actions ZIP has SHA-256 `589fb37ea2f621d79f68aea1757c88234f3ece347d2218f5abdcbcac9c472b4a`. [Original Linux artifact](clump-cli.zip)
