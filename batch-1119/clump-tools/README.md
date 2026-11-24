# Clump tool measurements on community batch 5

All three invocations used the same complete saved plan and the same 60,147-file checkout at `989ea9c41e8400a6fe894fe365298c219f8c7e1d`. The plan names 657 members and 186 roots. The full project plan produced identical bytes before and after changing the saved-plan loader. The comparison executed the stock Python command in separate processes. It restored the source files and verified the complete output between trials.

| Implementation | Elapsed seconds | CPU seconds | Peak memory, MB |
| --- | ---: | ---: | ---: |
| Original community tool | 15.807 | 11.762 | 3,999.6 |
| Compact renderer before the saved-plan change | 17.133 | 12.317 | 4,001.8 |
| Proposed tool | 0.272 | 0.259 | 94.1 |

These are medians from five scored rounds after one warm-up round per tool on Apple silicon. The timing includes Python startup, Git's tracked-file list, source reads, parsing, rendering and writes. The order varied between rounds. The host also ran other review tasks. CPU times and peak memory are provided alongside elapsed times. All 186 output files matched the preceding compact renderer byte for byte in each trial. All 657 original member sources were recovered. The isolated source checkout was deleted after its clean Git status had been checked. [Complete plan](saved-plan.json) · [Raw observations](apply-observations.jsonl) · [Inputs and output digests](apply-timing-summary.json)

The second workload times the reader and renderer on all 11,575 changed clumps with their real member bodies already in memory. Each file has a warm-up pair and five scored pairs with alternating first side. The reported CPU times are sums of per-file medians. Extraction took 1.216 → 1.158 seconds. Rendering took 2.734 → 4.054 seconds. [Raw per-file observations](python-observations.jsonl.gz) · [Paired timing summary](python-timing-summary.json)
