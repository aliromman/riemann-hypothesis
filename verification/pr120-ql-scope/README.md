# Preserve the QL measure instances' original scope

The [source change](https://github.com/aliromman/riemann-hypothesis/commit/ceaf3e60cfd51cb15e2839137e92731b4d2bfd8b) has one parent, Rohan's 4.36 integration at `f1ee9d0689a257a713e51378c69395714a0118ae`. It splits the existing bundles by their original access to `Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL`. This module registers a measurable space and a Borel space. In a stock Lean probe, importing it changes the inferred measurable space on `GL (Fin 1) ℝ` from `Units.instMeasurableSpace` to `GlobalTheory.CompanionTheory.QL.instMeasGL 1`. TmLev traced this problem across the [Borel and Haar modules](https://github.com/rohanarun/riemann-hypothesis/pull/819) and the [zeta-integral modules](https://github.com/rohanarun/riemann-hypothesis/pull/820).

| Measurement | Shared parent | Partition |
| --- | ---: | ---: |
| Tracked Lean sources in `src/` | 47,885 | 47,926 |
| Reduction from the 149,397 historical sources | 101,512 | 101,471 |
| Retained historical module bodies with different access to this provider | 48,588 | 0 |
| Retained historical module bodies with different public exports for this provider | 48,587 | 0 |

The native Lean header parser checked the historical tree, the shared parent and the candidate. Both comparisons cover 121,223 logical sources. The generator keeps 375 current source sections intact when it repartitions 113 existing files. It then removes 40 obsolete scope erasures in 38 physical files. It restores the historical body of `shell_lemma` after checking that [mrshu's measure transport](https://github.com/rohanarun/riemann-hypothesis/pull/781) was the only change to that body. The one unqualified pair of instance names in `ExistsIsUnrM` resolves to a different provider, `Formalism.DoubleCosetMeasures`, in the original compiler records.

Eleven complete old modules and their fifteen replacements compiled on Lean 4.36.0. The SHA-checked project inputs and dependency traces are in `pinned-graphs-and-inputs.json` and `kernels.json`. Each replacement passed native kernel replay. All 174 named public types and axiom sets match. All 22 definitions and all 152 theorem statements match. Six proof terms refer to private constants through a different module name. Replacing those names makes all six proof terms match. The checker follows 22 helper declarations and verifies all seven renamed helpers. The original release compiler objects for 37 logical source modules also agree with both sets of 174 public types.

The complete ramified shell, `Main`, and the five protected statements have separate verification requirements. This candidate has no full-build or Comparator verdict.

## Reproduce the source change

Use Python 3.9 or later and Git. Set `repo` to the full source repository and `tools` to this evidence directory. Set `lean` to the absolute path of the stock Lean 4.36.0 executable. Fetch the author's branch, the candidate, and the generator from [the supporting generator PR](https://github.com/rohanarun/riemann-hypothesis/pull/15). Use a new temporary directory for the generated files.

```sh
git -C "$repo" fetch https://github.com/rohanarun/riemann-hypothesis.git opt/collapse-and-consolidate-4.36
git -C "$repo" fetch https://github.com/aliromman/riemann-hypothesis.git codex/pr120-ql-provider-scope-4.36 codex/pr120-partition-bundles
tmp=$(mktemp -d)
git -C "$repo" show 6592ce644e82de3e7c8bcd3a2f29f52dedc75b14:scripts/partition_bundles.py > "$tmp/partition_bundles.py"
base=c7791603122c0328f79e49f6be5d7d4402effc53
initial=f94106583626ad6b48ac6e239e0b2e5ffc879555
head=f1ee9d0689a257a713e51378c69395714a0118ae
candidate=ceaf3e60cfd51cb15e2839137e92731b4d2bfd8b
python3 "$tools/git_lean_headers.py" --repo "$repo" --lean "$lean" --out "$tmp/base.jsonl" "$base"
python3 "$tools/git_lean_headers.py" --repo "$repo" --lean "$lean" --out "$tmp/head.jsonl" "$head"
PYTHONPATH="$tmp" python3 "$tools/replay_provider_partition.py" \
  --repo "$repo" --lean "$lean" --out "$tmp/structural" \
  --original-headers "$tmp/base.jsonl" --head-headers "$tmp/head.jsonl" \
  --instance GlobalTheory.CompanionTheory.QL.instMeasGL \
  --instance GlobalTheory.CompanionTheory.QL.instBorelGL \
  "$base" "$initial" "$head" Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
python3 "$tools/restore_partitioned_shell.py" "$repo" "$tmp/structural" "$tmp/complete"
python3 "$tools/check_generated.py" "$repo" "$tmp/complete" "$candidate"
```

The last command compares all 192 generated files with the candidate Git blobs. To repeat the compiled interface check, use a checkout of the parent and another of the candidate. With the pinned toolchain and Mathlib cache, run `xargs lake build < "$tools/targets-before.txt"` in the parent and `xargs lake build < "$tools/targets-after.txt"` in the candidate. Then run `python3 "$tools/check_objects.py" "$parent_checkout" "$candidate_checkout"`. In the candidate, run `PR120_REPLAY_LIST="$tools/targets-after.txt" lake env lean "$tools/../pr120-shard-roots/ReplayOriginalKernel.lean"`.
