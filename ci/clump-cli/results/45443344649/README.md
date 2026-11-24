# Full-checkout clump CLI timings

The stock clump CLI ran on a complete checkout of planner revision `8d792c7fd2c0f411f215762a82145a4484ea29dd` in a fresh Ubuntu 24.04 job. The driver matched all 59,909 tracked Lean files to their Git blob IDs before and after the experiment. The published e712 planner and the proposed 8d79 planner produced the same saved plan on every trial. It contains 199 clumps and 656 members. [Ubuntu timing job](https://github.com/aliromman/riemann-hypothesis/actions/runs/45443344649/job/138620264565)

Each of 30 invocations used a fresh Python process. Five warm-up invocations preceded the scored rounds within their command. Each implementation had five scored observations. The planner order alternated. The three apply implementations rotated and reversed order. CPU time includes user and system time charged by `wait4`. Peak RSS is reported for each child in bytes. The Linux runner used 3.12.16, 4 available processors and 15.61 GiB RAM. Setup and all independent comparisons ran outside the timers.

| Command | Implementation | Elapsed median, s | CPU median, s | Peak RSS median, MiB |
|---|---|---:|---:|---:|
| plan | `e7127ce8136d` (published) | 27.669 | 27.444 | 3603.12 |
| plan | `8d792c7fd2c0` (proposed) | 25.888 | 25.885 | 726.09 |
| apply | `1da818b50f1e` (community) | 23.788 | 23.573 | 3439.41 |
| apply | `e7127ce8136d` (published) | 0.453 | 0.437 | 69.95 |
| apply | `8d792c7fd2c0` (proposed) | 0.441 | 0.438 | 69.95 |

## Matched outcomes

| Command | Reference to proposed | Elapsed change | Slower elapsed pairs | CPU change | Slower CPU pairs | Peak RSS change | Higher RSS pairs |
|---|---|---:|---:|---:|---:|---:|---:|
| plan | published | -6.44% | 0/5 | -5.68% | 0/5 | -79.85% | 0/5 |
| apply | community | -98.14% | 0/5 | -98.14% | 0/5 | -97.97% | 0/5 |
| apply | published | -2.60% | 2/5 | +0.36% | 3/5 | +0.00% | 0/5 |

The current and proposed archives had identical bytes at every one of the 199 generated roots on every apply. The community implementation uses its older archive layout. All three implementations recovered all 656 original members byte for byte and removed the expected 457 subordinate files. The driver restored the original files outside the timer after every application. The saved plan has SHA-256 `7f008f70f550f162cba7e1b23b8b15309086d8efd3ff8c0c4a2ff9ed4521a175`.

The timing step completed all 30 invocations and passed all source, plan, generated archive and restoration checks. A separate output check in that job incorrectly required an empty planner error stream. This caused the workflow to report failure after it saved the timing results. The stock planner writes the count of refused folds to stderr. A second Ubuntu job retained both actual streams from both planner versions. It also checked each of the three apply implementations and restored the checkout after each one. The two planners had identical stdout and identical stderr. Their joined stream matched all 12 timed planner streams. All three apply implementations had identical stdout and identical stderr. [Successful independent output check](https://github.com/aliromman/riemann-hypothesis/actions/runs/45444098126/job/138622964408) [Planner stdout](plan-stdout.txt) [Planner stderr](plan-stderr.txt) [Original output artifact](clump-cli-outputs.zip)

These observations measure the normal Python planning and saved-plan application commands on one checkout and one Linux machine. Lean compilation timings are recorded separately. [Exact driver and Git source bindings](https://github.com/aliromman/riemann-hypothesis/tree/a01b2251fb8c2fd0fd8ea024adbd70c7e9360b97/ci/clump-cli) [Raw trials](observations.jsonl) [Trial ranges, medians, increases and ties](verified.json)

The original Actions ZIP has SHA-256 `5d616235f941bc5bd601aa8b2b87fdc0e86ef941552c150a128d0003b5642d15`. [Original Linux artifact](clump-cli.zip)
