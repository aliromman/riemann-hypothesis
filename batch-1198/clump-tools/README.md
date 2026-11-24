# Clump tool measurements on community batch 6

All three invocations used the same complete saved plan and the same 59,909-file checkout at `f6177155e8e440c0a831d4c15de4c74341de0a93`. The plan names 656 members and 199 roots. The full project plan produced identical bytes before and after changing the saved-plan loader. The comparison executed the stock Python command in separate processes. It restored the source files and verified the complete output between trials.

| Implementation | Elapsed seconds | CPU seconds | Peak memory, MB |
| --- | ---: | ---: | ---: |
| Original community tool | 15.598 | 11.241 | 3,918.1 |
| Compact renderer before the saved-plan change | 12.204 | 11.092 | 3,920.0 |
| Proposed tool | 0.290 | 0.264 | 92.9 |

The memory figures use decimal megabytes. These are medians from five scored rounds after one warm-up round per tool on Apple silicon. The timing includes Python startup, Git's tracked-file list, source reads, parsing, rendering and writes. The order varied between rounds. The host also ran other review tasks. CPU times and peak memory are provided alongside elapsed times. All 199 output files matched the preceding compact renderer byte for byte in each trial. All 656 original member sources were recovered. After the trials, Git could not update optional index timestamps because the disk was full. Once enough space was available, a separate reader compared the contents of all 59,909 restored physical source files with the published Git tree. The existing source checkout was then released. [Final source comparison](released-stock-checkout.json) [Complete plan](saved-plan.json) · [Raw observations](apply-observations.jsonl) · [Inputs and output digests](apply-timing-summary.json)

The second workload times the reader and renderer on all 11,551 changed clumps with their real member bodies already in memory. Each file has a warm-up pair and five scored pairs with alternating first side. The reported CPU times are sums of per-file medians. Extraction took 1.255 → 1.113 seconds. Rendering took 2.802 → 4.212 seconds. [Raw per-file observations](python-observations.jsonl.gz) · [Paired timing summary](python-timing-summary.json)
