# The final rewrite in `fc_conj_k`

PR #1037 makes three project matrix instances reduce to Mathlib's measurable space. This also changes the last rewrite in `PositivityTheory.SiegelWeilFormula.Act.C1.fc_conj_k`. On the PR, the rewrite proves the equality and the following `rfl` fails because there is no goal. The correction rewrites the domain and uses `exact hfd.setIntegral_eq …` to supply the proof. It leaves the theorem statement unchanged. [Proof correction](https://github.com/aliromman/riemann-hypothesis/commit/1650daef8d9ba43cdff53d36dd2fca3283e1c59b)

| Lean 4.37.0-rc1 input | Result for `ThetaKernels.IndepDomK` |
| --- | --- |
| Community main `75e2012dcc6f3093e223ef8d327b88395ff7d27c` | The original 538-line module compiled from source. The up-to-date check passed. |
| Three providers on that main, `6341848acdd84056724d3204b1a24c011721885f` | One Lean error at line 511, column 83, in the original module. |
| Direct integral proof on that main with the original providers | The complete module compiled. |
| Three providers and the direct proof, `1650daef8d9ba43cdff53d36dd2fca3283e1c59b` | The module compiled from source. The up-to-date check and kernel replay passed. |

The test uses 2,589 project modules. The first control compiled the target after restoring its 2,588 dependencies from the authenticated upstream cache. On the broken commit, Lake rebuilt 458 modules before the error. After the correction it rebuilt the target. Both successful stock checks visited 23,474 Lake jobs. [Control](main.json) · [Full comparison](comparison.json) · [Kernel transcript](kernel.log)

## Reproduce

Use separate checkouts for the community main, the broken commit and the proof correction in the table. Make the pinned Mathlib dependencies available in each checkout. Set `REPO` to a repository that has all three commits. Set `EVIDENCE` to `verification/pr1037-after-1324`, `BIN` to the toolchain's `bin` directory and `OUT` to a new output directory.

```sh
python3 "$EVIDENCE/replay_fc_conj_k.py" --repo "$REPO" --project "$BASE" \
  --revision 75e2012dcc6f3093e223ef8d327b88395ff7d27c --bin "$BIN" --output "$OUT/main"
python3 "$EVIDENCE/replay_fc_conj_k.py" --repo "$REPO" --project "$BROKEN" \
  --revision 6341848acdd84056724d3204b1a24c011721885f --bin "$BIN" --output "$OUT/broken" --expect-no-goals
python3 "$EVIDENCE/replay_fc_conj_k.py" --repo "$REPO" --project "$FIXED" \
  --revision 1650daef8d9ba43cdff53d36dd2fca3283e1c59b --bin "$BIN" --output "$OUT/fixed"
```

The script checks the source files in the target's import closure against Git. It runs stock Lake with `--rehash`. The negative case requires the specific Lean error. The positive case also requires an up-to-date build and native kernel replay. [Negative replay](replay-broken.json) · [Positive replay](replay-fixed.json)
