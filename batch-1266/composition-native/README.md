# Both proposals on the same source tree

The paired compiler test covers 18 roots, 51 selected modules and 120 modules across their complete project dependency graphs. One side uses the private import changes. The other uses those imports and the compact proof scopes together. Batch 7 changed inputs in six measured cones. The pinned compiler freshly built 21 selected modules on each side. The other 30 module results use identical original and proposed source blobs, the same complete imported project graph and the same signed owning archives on both batches. [Input changes](changed-inputs.json) · [Fresh compilation](fresh-summary.json) · [Earlier checked inputs](earlier-identical-inputs.json)

The comparisons cover 2,211 complete declaration entries, including their proof values, 146 warnings and 153 public module or IR file comparisons. [All module outcomes](paired-modules.jsonl.gz)

For `PositivityTheory.KB.sPU_of` the complete 51-module project graph, all signed owners, the full relevant source and the pinned tools match the previous compilation. That test replayed 1,712 declarations on each side and produced the same 608,444,309-byte proof export twice. Lean default, Lean paranoid and nanoda accepted it outside Bubblewrap. This record transfers that measurement to identical inputs. [All current module identities](complete-theorem-inputs.json) · [Original exporter and kernel reports](measured-verified.json) · [Whole-cone replay](measured-complete-stock-module-replay.json)

## Current proof export and three kernels

The original and combined current projects produced the same 608,444,309-byte export for `PositivityTheory.KB.sPU_of`. Lean default, Lean paranoid and nanoda each read the full export. All three accepted the proof and rejected a deliberately wrong proof of `Nat.zero_add`. The check verified 510 compiled project files for 51 modules. These three runs used the stock executables outside Bubblewrap. [Current kernel results](streamed-kernels.json) · [Current source and archive bindings](initial-history.json)
