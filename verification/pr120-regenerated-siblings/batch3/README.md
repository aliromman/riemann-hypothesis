# Twenty sibling groups on the clumped upstream layout

The patch removes 23 more tracked Lean sources from community main, from 60,630 to 60,607. Its parent is `cb4dc6e23a6187db392c96664295415c55b6b01e` on Lean 4.37.0-rc1. The renderer places 423 original logical sources into 20 groups and rewrites 24 direct importers. It preserves the order and visibility of imports and checks the recovered source bodies byte for byte. `Main` reaches 60,560 project sources after the change, down from 60,583. [Patch commit](https://github.com/aliromman/riemann-hypothesis/commit/b80cdeb74291c56519954d450dc08f12c6389e65)

The original 67 targets completed 37,789 Lake jobs over 9,746 project sources. The resulting 44 targets completed 37,743 jobs over 9,723 sources. All 44 candidate modules passed kernel replay. The public interface checks cover 1,297 names and axiom records, 71 definitions and 1,217 theorems. Forty-three passed the direct object comparison. In the conductor group, a definition contains a reference to a renamed private compiler proof. After expanding those proof helpers, both kernels accepted that definition. All 24 public declarations in that group passed the remaining checks. [Targeted builds](builds.json) · [44 object checks](interface-and-kernel.json) · [Conductor checks](conductor/result.json)

## Repeat the source transformation

Use the generator and parser in the parent directory of this record. Point `repo` to a Git repository with upstream main and the closing #120 head. Set `bin` to the Lean 4.37.0-rc1 toolchain’s bin directory and `tools` to `verification/pr120-regenerated-siblings`. The tested source tree, generators and build configuration at `cb4dc6e2` match `c9883164`. Use the latter to reproduce the recorded source manifest.

```sh
python3 "$tools/git_lean_headers.py" --repo "$repo" --lean "$bin/lean" --out "$scratch/headers.jsonl" \
  c9883164b0b3d762cee21f889d03d59a53b3ba3b
python3 "$tools/replay_sibling_selection.py" --repo "$repo" --headers "$scratch/headers.jsonl" \
  --selection "$tools/batch3/selection.json" --out "$scratch/result" --lean "$bin/lean" \
  fbb0941754dee95d15639f3d4d5596a3f508648b
cmp "$tools/batch3/projection.json" "$scratch/result/projection.json"
cmp "$tools/batch3/header-check.json" "$scratch/result/header-check.json"
```

For the native replay, use two work directories `before` and `after` under `pair`, with the patch parent and patch commit above. Build the targets from the two lists. The direct object checker reports the conductor difference. `conductor/AuditBundle.lean` and the two recorded expansion checks document its separate kernel comparison.

```sh
(cd "$pair/before" && xargs lake build < "$tools/batch3/targets-before.txt")
(cd "$pair/after"  && xargs lake build < "$tools/batch3/targets-after.txt")
python3 "$tools/check_projection_objects.py" "$pair" "$tools/batch3" "$bin" "$tools/Interface.lean"
python3 "$tools/batch3/conductor/repeat_conductor.py" --before "$pair/before" --after "$pair/after" \
  --bin "$bin" --audit "$tools/batch3/conductor/AuditBundle.lean" \
  --aux "$tools/../pr120-admloc-dependents/CompareAuxProofs.lean" --record "$tools/batch3/conductor/result.json"
```

At the stated revisions, this patch and #669 remove disjoint files. They touch eight of the same paths, with two Git merge conflicts. A merge simulation with batch #1018 is clean. No full `Main` or upstream Comparator result exists for this patch. [Overlap measurements](sibling-overlap.json) · [Merge simulation with #669](sibling-merge-669.json) · [Merge simulation with #1018](sibling-merge-1018.json)
