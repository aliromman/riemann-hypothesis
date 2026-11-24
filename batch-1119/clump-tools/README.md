# Clump tool measurements on community batch 5

All three invocations used the same complete saved plan and the same 60,147-file checkout at `2b481024a8665bd5b24ca40d28fe90cb4fb86ce0`. The plan names 657 members and 186 roots. The full project plan produced identical bytes before and after changing the saved-plan loader. The comparison executed the stock Python command in separate processes. It restored the source files and verified the complete output between trials.

| Implementation | Elapsed seconds | CPU seconds | Peak memory, MB |
| --- | ---: | ---: | ---: |
| Original community tool | 19.738 | 12.965 | 4,001.1 |
| Compact renderer before the saved-plan change | 20.187 | 13.676 | 4,001.5 |
| Proposed tool | 0.322 | 0.279 | 93.8 |

These are medians from five scored rounds after one warm-up round per tool on Apple silicon. The timing includes Python startup, Git's tracked-file list, source reads, parsing, rendering and writes. The order varied between rounds. The host also ran other review tasks. CPU times and peak memory are provided alongside elapsed times. All 186 output files matched the preceding compact renderer byte for byte in each trial. All 657 original member sources were recovered. The isolated source checkout was deleted after its clean Git status had been checked. [Complete plan](saved-plan.json) · [Raw observations](apply-observations.jsonl) · [Inputs and output digests](apply-timing-summary.json)

The second workload times the reader and renderer on all 11,575 changed clumps with their real member bodies already in memory. Each file has a warm-up pair and five scored pairs with alternating first side. The reported CPU times are sums of per-file medians. Extraction took 1.258 → 1.212 seconds. Rendering took 2.796 → 4.205 seconds. [Raw per-file observations](python-observations.jsonl.gz) · [Paired timing summary](python-timing-summary.json)
