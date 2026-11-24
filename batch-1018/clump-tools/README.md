# Apply a saved clump plan

Community `clump.py apply` read and parsed all tracked Lean modules before it accessed the requested clumps. The follow-up in commit `f3e19bf8371ab5dd383b81e008ec14c4b0331811` filters the existing tracked-file list before opening any source. The loader still reads all modules for planning. The saved-plan command reads each root and member before making its first edit.

The complete plan came from the published 60,493-file source tree `445477315d15f0c5eaea8c076b18063ebd7a17a6`, using the default line limit and the tracked exclusion list. It contains 147 clumps and 565 distinct modules. The candidate's normal plan command produced the exact same JSON. The measurements ran the normal apply CLI on a complete Apple file-system clone of this tree. Each trial began with the same 565 original files. Each run wrote all 147 root files and absorbed the other 418 members. Normal extraction returned the 565 starting files byte for byte after every run. The previous and updated compact renderers also produced the same 147 output file digests in every run.

| Tool | Median elapsed seconds | Median CPU seconds | Median peak memory in decimal MB |
| --- | ---: | ---: | ---: |
| Community parent | 12.576 | 10.840 | 4,054.8 |
| Preceding draft | 10.862 | 10.839 | 4,054.9 |
| Saved-plan filter | 0.229 | 0.225 | 91.7 |

These are five measured rounds after one warm-up round on Apple silicon, using Python 3.12.16. The order of the three tools varied across the rounds. The timed interval includes Python startup, Git's tracked-file listing, source reads, parsing, generation and writes. Source restoration and output verification run outside the interval. The complete plan, its tool and source digests, and all raw timings are in this directory. [Saved plan](saved-plan.json) · [Raw trials](apply-observations.jsonl) · [Run identity](apply-timing-summary.json)

A separate in-memory benchmark calls each tool's extractor and renderer on all 11,579 converted proof clumps. It uses five scored paired trials per file after one warm-up. Summed median reader CPU time changes from 1.230 to 1.163 seconds. Summed median renderer CPU time changes from 2.776 to 4.131 seconds. The saved-plan filter leaves these two functions byte for byte unchanged. [Per-file measurements](python-observations.jsonl.gz) · [Summary](python-timing-summary.json)

The regression fixture omits one tracked module. A plan that requires it fails before applying any clump. A plan that omits it completes and restores its two members. The previous draft fails the second operation. [Regression control](apply-control.log) · [Changed tools](https://github.com/aliromman/riemann-hypothesis/commit/f3e19bf8371ab5dd383b81e008ec14c4b0331811)
