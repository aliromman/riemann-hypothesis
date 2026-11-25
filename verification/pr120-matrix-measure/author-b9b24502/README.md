# Matrix providers and the amplifier proof on Lean 4.36

The author branch at `b9b24502d0b9e84c5e6c91fd00aa87c658c518d0` and the three-provider change at `c4039c570d0eebd1ebae175be52c11d3bade024f` each built the same 37 project modules. Git source blobs differ only for the three providers. Native `leanchecker` accepted each provider and `Formalism.DoubleCosetMeasures.LatticeCoset` on each revision. The receipt lists all source blobs and eight kernel exit codes. [Author PR #1003](https://github.com/rohanarun/riemann-hypothesis/pull/1003)

## Build the physical modules

Use Lean 4.36.0, Python 3 and the packages from the project lock file. Set `tools` to this directory and `bin` to the absolute directory that contains `lean`, `lake` and `leanchecker`. Run the commands from the repository. Use a new output directory.

```sh
git fetch https://github.com/aliromman/riemann-hypothesis.git codex/pr1003-436-b9b24502-check
python3 "$tools/build_author_matrix.py" --repo "$PWD" --bin "$bin" \
  --packages "$PWD/.lake/packages" --output "$scratch/physical" \
  --parent b9b24502d0b9e84c5e6c91fd00aa87c658c518d0 \
  --candidate c4039c570d0eebd1ebae175be52c11d3bade024f
```

## Check the proof with the original module names

The shard report identifies a `BorelSpace` error inside `AmplifierOfHypotheses`. This control reads the whole proof body from `b9b24502` and replaces the bundled imports with their original members. Its 38 project inputs come from an existing build with the original module names. These inputs give a different import environment from the physical bundles. [Pinned shard report](https://github.com/rohanarun/alpoge-rh-replay/blob/4b877bb5c82744a6f5a0452a8fbd9a9e3973c458/PR120-BUGS.md)

| Imports and local proof | Lean result | Kernel result |
| --- | --- | --- |
| Original members alone | Unknown constant `Formalism.DoubleCosetMeasures.instMeasMat` | No object |
| Original members and three original providers | Pass | Pass |
| Same inputs with `haveI` in place of `have` | Pass | Pass |
| Original members and three repaired providers, original proof | Pass | Pass |

The alias control first loaded three signatures from the original build with IR from the repaired providers. The checker stopped during import with signal 11. Changing only these three `.ir.sig` inputs to match the `.ir` files gave kernel exit 0 for the same proof object. The receipt contains the signature hashes. Keep each provider’s `.olean`, `.olean.server`, `.olean.private`, `.ir` and `.ir.sig` together.

Use the original checkout and the `candidate` library from the 4.36 replay in the parent directory's README. Build the original members listed in `amplifier-logical.json` if their objects are missing. Run from the original checkout with its pinned package lock. The output directory must be empty.

```sh
python3 "$tools/replay_amplifier_436.py" --repo "$PWD" --bin "$bin" \
  --revision b9b24502d0b9e84c5e6c91fd00aa87c658c518d0 \
  --stock "$PWD/.lake/build/lib/lean" --providers "$matrix_replay/candidate" \
  --output "$scratch/amplifier"
```

The physical amplifier still needs a build under the full bundle imports on the author branch. The `Main` build and upstream Comparator for all five protected statements also remain open.
