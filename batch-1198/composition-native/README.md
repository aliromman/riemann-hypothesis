# Both refactors together

The pinned compiler built 18 roots and 51 modules from the import proposal and from the two proposals together. It compared 2,211 complete declarations, 153 ordinary compiler outputs and 146 warnings on the actual community parent. All matched. The run authenticated all 120 original project archives used by those source modules. [Workload and results](summary.json) · [Per-module measurements](paired-modules.jsonl.gz) · [Official project inputs](official-inputs.json.gz)

During integration, the scope PR restored a blank line in a module outside every measured dependency graph. A second reader traversed all 18 graphs, checked their 120 official archive digests and compared the actual source bytes from both combined Git trees. It matched each resulting input against the original compiler rows. [Exact sources and final joint tree](current-source.json)

A separate exported-theorem comparison ran on community batch 5. The input comparison identifies what changed in its full dependency graph after batch 6. [Comparison to the earlier exported proof](historical-full-cone-inputs.json)

## Complete input graph for one exported theorem

The separate comparison of `PositivityTheory.KB.sPU_of` used its complete 51-module project dependency graph. It checked all sources and 510 original and proposed compiler files against the earlier combined compilation. The stock Lean checker replayed all 1,712 local declaration entries on each side. The pinned exporter then produced the same 608,444,309 bytes from both current inputs. Lean default, Lean paranoid and nanoda accepted the proof. The Comparator also passed its statement and axiom checks. This run used a local machine outside Bubblewrap. The four selected default-sandbox source comparisons have their own records. [Input identities](joint-proof/inputs.json) · [Both whole-graph Lean replays](joint-proof/complete-stock-module-replay.json) · [Exporter and kernel results](joint-proof/verified.json) · [Comparator output](joint-proof/comparator.json) · [Sandboxed source tests](../bounded-checks.md)
