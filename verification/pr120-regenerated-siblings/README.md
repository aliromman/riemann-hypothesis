# Regenerate sibling groups on current main

This tool applies eligible groups from rohanarun's Lean 4.36 bundle plan to the clumped sources on Lean 4.37.0-rc1. It reads the ordered import modes from Lean, preserves adjacency at each direct importer, and uses the clump format and exclude list from the exact upstream revision. It also checks that the original bodies inside the affected clumps can be recovered byte for byte. [Author's integration plan](https://github.com/rohanarun/alpoge-rh-replay/issues/35028#issuecomment-7116981839) · [Patch on current main](https://github.com/aliromman/riemann-hypothesis/commit/76530436d89f551c9f4e5fb3754a38af2501634c)

The selection contains 12 groups. It removes 15 source files and rewrites 14 direct importers. Lean's dependency parser found 60,929 source files before and 60,914 after. The reachable input count for `Main` changed from 60,716 to 60,701. The renderer recovered 232 logical sources. The stock targeted build used 909 project inputs and the candidate used 894. Four earlier candidate groups were excluded after comparison of compiled declarations.

All 26 candidate modules passed kernel replay and the interface check. The comparison covered 898 public declarations with axiom records, 42 definitions and 850 theorems. It recorded 883 exact raw types and 846 exact proof terms. The check allows a change to a macro-generated binder's scope number while preserving its name and binder mode. Proof terms can change while their types and axiom sets stay the same. The complete `Main` build and upstream Comparator remain a separate gate.

## Repeat the projection

Set `repo` to a repository that contains the three commits below. Set `tools` to this evidence directory, `scratch` to an empty directory, and `bin` to the Lean 4.37.0-rc1 toolchain bin directory.

```sh
python3 "$tools/git_lean_headers.py" --repo "$repo" --lean "$bin/lean" \
    --out "$scratch/headers.jsonl" 343b1de38bbe4c5c66f1c1c0afd7c34e8645acdf
python3 "$tools/replay_sibling_selection.py" --repo "$repo" --headers "$scratch/headers.jsonl" \
    --selection "$tools/selection.json" --out "$scratch/result" --lean "$bin/lean" \
    16f10fc4b35d0e25866167c112c7232b2cb7f8f8
cmp "$tools/projection.json" "$scratch/result/projection.json"
cmp "$tools/header-check.json" "$scratch/result/header-check.json"
```

The projection records each output source hash and each deletion. The patch commit has parent `d27f71347abceb76cd37dc8a5fccbe556ec2be90`. This parent has the same source tree and Lean build configuration as `343b1de38b`.

## Repeat the compiled comparison

Use two work directories named `before` and `after` under the same directory. Use the parent above in `before` and `76530436d89f551c9f4e5fb3754a38af2501634c` in `after`. Install the locked packages in each directory and put the pinned toolchain first on `PATH`.

```sh
(cd "$pair/before" && xargs lake build < "$tools/targets-before.txt")
(cd "$pair/after"  && xargs lake build < "$tools/targets-after.txt")
python3 "$tools/check_projection_objects.py" "$pair" "$tools" "$bin" "$tools/Interface.lean"
```

The last command checks every changed module and its direct importers, and writes one kernel log per module.
