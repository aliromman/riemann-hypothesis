# Matrix instance checks after batch #2318

Community main `75e2012dcc6f3093e223ef8d327b88395ff7d27c` and the PR head `fa5d4e8b053eb3a7c044f41c286d50c8ef45b553` merge cleanly at fork commit `6341848acdd84056724d3204b1a24c011721885f`. The candidate tree is `e25cdafae4413a0198b254a2757fd12ebb62bea1`. The change makes three named matrix measure instances reduce to `Matrix.instMeasurableSpace`. [Candidate](https://github.com/aliromman/riemann-hypothesis/commit/6341848acdd84056724d3204b1a24c011721885f) · [Community PR](https://github.com/leanprover-community/riemann-hypothesis/pull/1037)

| Lean 4.37.0-rc1 check | Main | Main with #1037 |
| --- | ---: | ---: |
| Full `LinUnit.eq_zero_of_ip_eq_zero` proof in each of two import orders, with the GL scope open and closed | 2 errors in each of 4 cases | 0 errors in all 4 cases |
| Three named matrix instances compared with the Mathlib instance by reducible `rfl` | 3 errors | 0 errors |
| Two named scoped GL instances selected | 2 of 2 | 2 of 2 |
| Kernel replay of the original proof module and the intended GL caller | 2 of 2 | 2 of 2 |

Nineteen of the 311 source files in this test changed since batch #2164. These include the GL caller `GJFEInducedLevi`. Stock Lake compiled 113 modules on each side. The subsequent up-to-date checks passed. [Build record](builds.json) · [Closed scope](closed.json) · [Open scope](open.json) · [Caller and provider checks](callers.json)

## Reproduce

Set `BEFORE` and `AFTER` to checkouts of the two commits identified above as main and candidate. Set `BIN` to the pinned toolchain's `bin` directory, `EVIDENCE` to `verification/pr1037-after-1324` in the evidence branch and `OUT` to a directory for test results. Both checkouts need the packages in `lake-manifest.json`. To fetch the Mathlib cache in a fresh checkout, use the command in the [upstream README](https://github.com/leanprover-community/riemann-hypothesis/blob/75e2012dcc6f3093e223ef8d327b88395ff7d27c/README.md#L52-L67).

```sh
export PATH="$BIN:$PATH"
export LAKE_ARTIFACT_CACHE=false
for project in "$BEFORE" "$AFTER"; do
  (cd "$project" && lake --no-cache --rehash build \
    Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace \
    Formalism.DoubleCosetMeasures.StatementZ \
    GroundTheory.AutomorphicForms.GL2.GJMatrixCoord \
    Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfIpEqZero \
    GroundTheory.AutomorphicForms.GL2.GJFEInducedLevi) || exit 1
done
python3 "$EVIDENCE/replay_matrix_selection.py" --before "$BEFORE" --after "$AFTER" \
  --bin "$BIN" --output "$OUT/closed"
python3 "$EVIDENCE/replay_matrix_selection.py" --before "$BEFORE" --after "$AFTER" \
  --bin "$BIN" --output "$OUT/open" --open-double-coset-scope
python3 "$EVIDENCE/replay_matrix_callers.py" --before "$BEFORE" --after "$AFTER" \
  --bin "$BIN" --output "$OUT/callers"
```

The build record gives the Git revisions, source changes, commands, exit codes and SHA-256 hashes of the original Lake logs. The compressed logs in this directory expand to those hashes. These checks cover the five targets listed above.
