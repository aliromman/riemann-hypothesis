# Matrix measure instances after #1324

Lean 4.37.0-rc1 can select three project instances for the measurable space on matrices. Each uses the entrywise product σ-algebra. During typeclass search, the elaborator can leave these instance constants folded. A theorem about a measure built with one instance can then fail with another. [Tracking issue](https://github.com/leanprover-community/riemann-hypothesis/issues/599)

| Source | Revision |
| --- | --- |
| Community main before the scope change | `9282d3a102c4aff0e6026746db2a8990f5d9cddd` |
| Daniel Ang’s scoped GL and matrix instances in #1324 | `7b92c9c688b240646a4e41302f2988e28d6518bc` |
| Main with #1324 incorporated, used as the control | `e25f3cf39817ed5293a05ac1655867fb7e6b2f3f` |
| #1037 with three reducible definitions of the Mathlib instance | `e851a5d2c500ad1c04eb4ddae9706205fd194dbb` |
| Fork follow-up that removes the four named project instances | `eb1a7892994ce07f281da1c8338298944e6d04b7` |

## Results

The two columns for each proof are separate compilations of the same proof body. Each cell gives the diagnostic count for one import order.

| Proof and environment | First order | Reverse order |
| --- | ---: | ---: |
| Archived `SingleBlockDoublingIntegralValue` on main | 8 | 8 |
| Archived doubling proof on main with #1324 | 0 | 0 |
| Archived doubling proof on #1037 | 0 | 0 |
| Live `EqZeroOfIpEqZero` with extra imports on main with #1324 | 2 | 2 |
| Live twisted-operator proof with the same imports on #1037 | 0 | 0 |

For the doubling proof, the two orders put `MatrixMeasurableSpace` and `DoubleCosetMeasures.StatementZ` first in the import header. A third case preserves the original header and adds the foundation last. That case produced nine errors on current main and zero after #1324. The complete 492-line source comes from `cb4dc6e23a6187db392c96664295415c55b6b01e`. Commit `0a25f0a375ee83268035247f56e7468e231e627e` removed it, five companion modules, and most of `QLoc`. The fixture compiles the five historical companion sources and the removed `QLoc` section against each live checkout. It uses the current `piP` and preserves the complete doubling proof body. The retired material belongs only to this test.

For the live proof, the two orders put `DoubleCosetMeasures.StatementZ` and `GJMatrixCoord` after the original imports in opposite orders. Both failed to synthesize `IsFiniteMeasureOnCompacts (volM ν b a)` on the control. The second error reports the unfinished proof. The same comparison passed on #1037 with the DoubleCosetMeasures scope open and closed. Each provider also failed an independent reducible equality with `Matrix.instMeasurableSpace` in its own import cone when active. Mathlib alone passed.

The parent and #1037 both passed 24 Lake targets with 1,065 project modules in their import closure. They include `LocalZetaFunctionalUniqueness`, which passes the GJ matrix instance by name, and `LatticeCoset`, `CutTypeNormMeas`, and `IsCompactKH`. Both environments selected `Formalism.DoubleCosetMeasures.instMeasGL` and `instBorelGL` for the scoped GL control. Lean kernel replay passed for eight candidate modules. Both kernels accepted the old and new values for each of the three provider definitions in six conversion checks.

The fork follow-up removes those three measurable-space declarations, `GJMatrix.borelSpace_matrix`, and 60 caller attribute commands. The 28-file change also migrates the explicit uses. A Git search and a separate scan of all 59,869 Lean source blobs found zero remaining mentions of the four names. Its 24-target build passed. Each tested matrix import cone then selected Mathlib’s own Borel witness.

The M4 operator reported the doubling regression. Kristof Gazso and meltingice identified the reverse case. Daniel Ang supplied the scoping fix. [M4 report](https://github.com/leanprover-community/riemann-hypothesis/pull/120#issuecomment-7128951255) · [Reverse case](https://github.com/rohanarun/riemann-hypothesis/pull/325) · [#1324](https://github.com/leanprover-community/riemann-hypothesis/pull/1324) · [#1037](https://github.com/leanprover-community/riemann-hypothesis/pull/1037)

## Reproduce

Set `MAIN`, `BEFORE`, and `AFTER` to Git checkouts at the first, third, and fourth revisions in the table. Set `EVIDENCE` to this directory in the verification branch and `BIN` to the pinned Lean toolchain’s `bin` directory. Use a checkout with the archived commit in its Git object store. Set `OUT` to an empty directory for the results.

```sh
for project in "$MAIN" "$BEFORE" "$AFTER"; do
  (cd "$project" && "$BIN/lake" exe cache get && "$BIN/lake" build $(cat "$EVIDENCE/targets.txt")) || exit 1
done
python3 "$EVIDENCE/replay_doubling.py" --full --repo "$MAIN" --before "$MAIN" --after "$BEFORE" --bin "$BIN" --output "$OUT/scope-alone"
python3 "$EVIDENCE/replay_doubling.py" --full --repo "$MAIN" --before "$BEFORE" --after "$AFTER" --bin "$BIN" --output "$OUT/doubling"
python3 "$EVIDENCE/replay_matrix_selection.py" --before "$BEFORE" --after "$AFTER" --bin "$BIN" --output "$OUT/closed"
python3 "$EVIDENCE/replay_matrix_selection.py" --open-double-coset-scope --before "$BEFORE" --after "$AFTER" --bin "$BIN" --output "$OUT/open"
python3 "$EVIDENCE/compare_providers.py" --before "$BEFORE" --after "$AFTER" --bin "$BIN" --checker "$EVIDENCE/../pr120-matrix-measure/CompareMatrixDefinitions.lean" --output "$OUT/conversions.json"
(cd "$AFTER" && "$BIN/lake" env "$BIN/lean" "$EVIDENCE/ScopedGL.lean")
while read -r target; do
  (cd "$AFTER" && "$BIN/lake" env "$BIN/leanchecker" -v "$target") || exit 1
done < "$EVIDENCE/kernel-targets.txt"
```

The JSON receipts record the revision, probe source hashes, diagnostics, and kernel checks. A full `Main` build and upstream Comparator on the five final statements are still required on the proposed merge commit. [Upstream verification instructions](https://github.com/leanprover-community/riemann-hypothesis/blob/9282d3a102c4aff0e6026746db2a8990f5d9cddd/README.md#checking-the-proof-yourself)
