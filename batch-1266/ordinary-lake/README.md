# Ordinary Lake build

The community cache command restored 59,883 modules from parent `307cef33f046955ee79dba47e0d828d06496d75f` on an Apple silicon Mac. It reused 31,091 project archives, verified 28,792 downloaded archives and found 9,133 Mathlib cache files already available. The command includes `lake build --no-build` and returned zero in 184.54 seconds. [Command output](parent.log) · [Toolchain and package commits](parent-restore.json)

The five Lean compiler outputs occupy 66,097,599,808 bytes across all project modules. The full private import of `Main` reaches 59,836 project modules, with 66,081,530,800 bytes across those outputs. These are logical file sizes on disk. [Totals and original Main hashes](parent-sizes.json) · [Size by module](parent-sizes.tsv.gz)

The first three completed groups on the proposed branch requested 776 distinct source targets. Lean emitted new compiler setup files for 574 distinct modules. Both `lake build` and `lake build --no-build` returned zero for each group. Lake used the ordinary project and package libraries. The full plan covers 41,948 potentially affected modules. These initial groups are a checkpoint in that run. [Commands, target names and original output](first-batches.json)
