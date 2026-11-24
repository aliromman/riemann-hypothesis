# Current clump tool and stock source measurements

The community parent is `73958da58a8a4d1f61b789745c5444baf6247cae`. The proposed commit is `34177e76b3d63c96565710dd9977ba7155427e13`. Both Lean source trees match the corresponding trees in the preceding batch-896 source comparison. The proposed `src` tree is `2f3a5bc48d255b9683b700ec22411ab69d4b4efa`. All 11,647 recorded source comparisons, including the old reader, current reader, generator and 68,850 original members, reproduce the previous gzip file byte for byte.

The new scanner reads a quoted name that contains a space or comment characters and recognizes a comment immediately after a scope name. In the normal CLI example, the previous clumper lost the outer namespace after `namespace A.«B C»-- a comment` and `end «B C»`. Lean rejected the resulting file. With the current clumper, the generated file, a downstream importer using all three declarations and the two-file round trip pass. `planner.json` compares all 60,630 project sources. The scanner found the same 776,016 declaration names per module, line estimates and 12,569 protected clumps. The new upstream test directory discovers the focused regression tests. The main test directory ran 273 tests with one skip. The runner-specific directory ran nine with four platform skips. These tests used Python 3.12, the real Elan manager linked to the existing pinned Lean installation, the S3 test SDK and a physical temporary directory.

## Timing the clumper

`tool-summary.json` covers all 11,647 changed clumps. On each source the benchmark warms up each tool once and measures five pairs. It alternates their order. The source order is the SHA-256 of `stock-clump-tools:` and the UTF-8 path. Each row of `tool-observations.jsonl.gz` records the path, trial, side (0 parent, 1 proposal), reader CPU, reader wall, renderer CPU and renderer wall in milliseconds. Each total sums the per-file medians. Git I/O and construction of the original in-memory modules are outside the timed regions. Every measured extraction and regeneration checks the member order and the emitted source.

| Stock tool call on all changed sources | Parent CPU | Proposed CPU |
| --- | ---: | ---: |
| Extract original members | 1.771 s | 1.717 s |
| Regenerate clumps | 3.611 s | 5.575 s |

The extra regeneration work amounts to 1.963 CPU seconds over this selection. The reader is slower in 6,127 files although the aggregate decreases. The renderer is slower in 11,638. The 257-file stratified panel and its individual timings are also available. On the same final inputs the follow-up compared with the first public draft, with observed aggregate reader CPU of 81.873 → 53.306 ms and renderer CPU of 290.092 → 184.481 ms. These measurements concern the Python tool. The stock Linux Lean measurements cover the actual published merge, including a 12-source compiler panel and a four-source clean Lake target. [Linux run and complete measurements](https://github.com/aliromman/riemann-hypothesis/tree/e615ffc2b6c6c328e5b895d346d091c58384b07e/ci/stock-batch-896/results/45366826111/)

The pending full selection is measured against individual private proof values and the current parent inputs. The coordination record describes additional focused proposals opened or updated after batch 896. [Native comparison](https://github.com/aliromman/riemann-hypothesis/actions/runs/45366025067)
