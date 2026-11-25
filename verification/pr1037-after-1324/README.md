# Matrix measure instances after #1324

Lean 4.37.0-rc1 can select three project instances for the measurable space on matrices. Each uses the entrywise product σ-algebra. During typeclass search, the elaborator can leave these instance constants folded. A theorem about a measure built with one instance can then fail with another. [Tracking issue](https://github.com/leanprover-community/riemann-hypothesis/issues/599)

| Source | Revision |
| --- | --- |
| Community main before the scope change | `9282d3a102c4aff0e6026746db2a8990f5d9cddd` |
| Daniel Ang’s scoped GL and matrix instances in #1324 | `7b92c9c688b240646a4e41302f2988e28d6518bc` |
| Main with #1324 incorporated, used as the control | `e25f3cf39817ed5293a05ac1655867fb7e6b2f3f` |
| #1037 with three reducible definitions of the Mathlib instance | `e851a5d2c500ad1c04eb4ddae9706205fd194dbb` |
| Fork follow-up that removes the four named project instances | `eb1a7892994ce07f281da1c8338298944e6d04b7` |
| Community main after #1324 merged | `b2f365a68500e2bde98cd60a2324263fc62fba10` |
| #1037 on this main | `5ab7e11d01ee36fa4f32e8be00a4d2529eec5f1b` |
| Proposed GitHub merge of these two revisions | `5446ee0fd9a7c0a2301ccd1a3b476b482896df14` |
| Fork cleanup updated on top of #1037 | `63e4077100de67259780b159cc7c528e9046ab29` |

## Results

The two columns for each proof are separate compilations of the same proof body. Each cell gives the diagnostic count for one import order.

| Proof and environment | First order | Reverse order |
| --- | ---: | ---: |
| Archived `SingleBlockDoublingIntegralValue` on main | 8 | 8 |
| Archived doubling proof on main with #1324 | 0 | 0 |
| Archived doubling proof on #1037 | 0 | 0 |
| Live `EqZeroOfIpEqZero` with extra imports on main with #1324 | 2 | 2 |
| Live twisted-operator proof with the same imports on #1037 | 0 | 0 |

For the doubling proof, the two orders put `MatrixMeasurableSpace` and `DoubleCosetMeasures.StatementZ` first in the import header. A third case preserves the original header and adds the foundation last. That case produced nine errors on main before #1324 and zero after #1324. The complete 492-line source comes from `cb4dc6e23a6187db392c96664295415c55b6b01e`. Commit `0a25f0a375ee83268035247f56e7468e231e627e` removed it, five companion modules, and most of `QLoc`. The fixture compiles the five historical companion sources and the removed `QLoc` section against each live checkout. It uses the current `piP` and preserves the complete doubling proof body. The retired material belongs only to this test.

For the live proof, the two orders put `DoubleCosetMeasures.StatementZ` and `GJMatrixCoord` after the original imports in opposite orders. Both failed to synthesize `IsFiniteMeasureOnCompacts (volM ν b a)` on the control. The second error reports the unfinished proof. The same comparison passed on #1037 with the DoubleCosetMeasures scope open and closed. Each provider also failed an independent reducible equality with `Matrix.instMeasurableSpace` in its own import cone when active. Mathlib alone passed.

The parent and #1037 both passed 24 Lake targets with 1,065 project modules in their import closure. They include `LocalZetaFunctionalUniqueness`, which passes the GJ matrix instance by name, and `LatticeCoset`, `CutTypeNormMeas`, and `IsCompactKH`. Both environments selected `Formalism.DoubleCosetMeasures.instMeasGL` and `instBorelGL` for the scoped GL control. Lean kernel replay passed for eight candidate modules. Both kernels accepted the old and new values for each of the three provider definitions in six conversion checks.

On the controlled integration pair, the public interface check covered all 1,065 modules. All 35,764 declaration types and axiom records matched. All 16,470 theorem proofs matched after the comparison removed compiler macro-scope numbers from binder names. Of 17,637 definition bodies, only the three providers changed. Both kernels accepted all three old and new values. The audit also checks recursor rules and permits only `propext`, `Quot.sound`, and `Classical.choice` in the recorded axiom sets.

The fork follow-up at `eb1a7892994c` removes those three measurable-space declarations, `GJMatrix.borelSpace_matrix`, and 60 caller attribute commands. The 28-file change also migrates the explicit uses. A Git search and a separate scan of all 59,869 Lean source blobs found zero remaining mentions of the four names. Its 33-target build passed. Its 6,781-module import closure includes 17 of the 28 changed files. This includes the complete `ThetaFunctionsSpannedHeckeTwistedStandardFrameStatement` and `VolLevelWtConstStatement` proofs, which lost explicit local witnesses. Each tested matrix import cone selected Mathlib’s Borel witness.

The M4 operator reported the doubling regression. Kristof Gazso and meltingice identified the reverse case. Daniel Ang supplied the scoping fix. [M4 report](https://github.com/leanprover-community/riemann-hypothesis/pull/120#issuecomment-7128951255) · [Reverse case](https://github.com/rohanarun/riemann-hypothesis/pull/325) · [#1324](https://github.com/leanprover-community/riemann-hypothesis/pull/1324) · [#1037](https://github.com/leanprover-community/riemann-hypothesis/pull/1037)

## Verification after #1324 merged

The three changed files have the same old and new Git blobs on the integration pair and on merged main. The updated branch has 59,823 Lean sources under `src/`. The main and candidate builds passed the 24 targets in `targets.txt`. The source graph contains 14,413 modules that use at least one of the three providers, directly or through imports. The import closure of `Main` contains 14,400 of them. The 12 targets in `outside-targets.txt` cover the other 13, with 3,145 distinct source modules in their import closure.

On `b2f365a68500` and `5ab7e11d01ee`, the archived doubling body passed in both import orders and with the original header widened. The live proof changed from two errors to zero in both orders with the scope open and closed. Eight candidate kernel replays and six provider conversions passed. All 35,759 public types and axiom records in the 1,065-module comparison agreed. All 16,465 theorem proof terms agreed under the same audit. Only the three provider definitions changed body. The GitHub merge and the tested branch have the same complete tree, `550b6b254bff48daa7e5515d38db0535d1d9c6c7`. The merge pin remains available on the fork. [Pinned merge](https://github.com/aliromman/riemann-hypothesis/tree/codex/pr1037-merge-5446ee0f).

The 36 targets in `combined-targets.txt` passed on the community main parent and the exact GitHub merge. Their union contains 3,340 project modules. The audit found the same 85,211 public types and recorded axiom sets in both builds. All 47,458 theorem proofs agreed. Of 34,073 definition bodies, 34,070 agreed under the structural comparison. Lean accepted each of the three changed provider bodies in both environments. The 12 additional targets accounted for all 13 affected modules outside `Main`. These counts include each module once.

Both Git revisions also passed `lake build Challenge` and `lake env leanexport Challenge` with the upstream export list. The two five-statement challenge exports had 363,237,517 bytes and SHA-256 `bb37c4bb518fe68a13f12aa3929dd62dfecb663f0c063ad8c338e39601f28a60`. The solution export and the final Comparator verdict still require a full run on the merge. Roy7 accepted the full build and Comparator run on the pinned merge. [Runner assignment](https://github.com/leanprover-community/riemann-hypothesis/issues/599#issuecomment-7148937434).

## Optional removal of the four names

The updated cleanup at `63e4077100de` removes four instance declarations and 60 local attribute commands in 28 files. It also removes two local measurable-space witnesses and one Borel-space witness. It retains main’s changes to the local instance list in `SumOKEx` and the theorem reference `PI.WUN.exp_mem_UH` in `AtChoice`. Two other overlapping files had upstream edits to comments and matrix priority commands that the cleanup deletes. A Git search and a SHA-checked scan of all 59,823 project source blobs found zero uses of the four names. [Change from the #1037 head](https://github.com/aliromman/riemann-hypothesis/compare/5ab7e11d01ee36fa4f32e8be00a4d2529eec5f1b..63e4077100de67259780b159cc7c528e9046ab29).

This revision passed the 25 targets in `followup-port-25.txt`, with 2,959 distinct source modules. This includes the two explicit GL comap proofs, `LocalZetaFunctionalUniqueness`, and `SumOKEx`. The matrix probes selected Mathlib’s Borel witness, and both import orders passed for the live and archived proof bodies. Lean selected both original scoped GL names. The eight candidate modules in `kernel-targets.txt` passed kernel replay. Nine of the 28 changed files occur in the tested source closure. Eleven more terminal targets cover the other 19. The complete changed-file closure contains 17,360 modules. The optional cleanup stays on the fork while these checks are open.

The generator reads source files directly from Git. It verifies each changed file against the expected commit before it writes any output. It can use either the merged main parent or the three-file #1037 head to produce the same 28 files. Run this command from a repository that has both commits. Set `EVIDENCE` to this directory and `OUT` to a directory for the results.

```sh
python3 "$EVIDENCE/regenerate_cleanup.py" --repo . \
  --base 5ab7e11d01ee36fa4f32e8be00a4d2529eec5f1b \
  --expected 63e4077100de67259780b159cc7c528e9046ab29 --output "$OUT/cleanup-src"
```

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

To repeat the interface and import checks on merged main, set `PARENT` to the full ID of `b2f365a68500` and `CANDIDATE` to the full ID of the PR head or proposed merge. Use their checkouts for `BEFORE` and `AFTER`. Build the selected targets on both sides before reading the compiled objects.

```sh
python3 "$EVIDENCE/audit_cone.py" --repo "$BEFORE" --before "$BEFORE" --after "$AFTER" --bin "$BIN" --parent "$PARENT" --candidate "$CANDIDATE" --targets "$EVIDENCE/targets.txt" --checker "$EVIDENCE/../pr120-admloc-dependents/AuditPublic.lean" --output "$OUT/interfaces"
python3 "$EVIDENCE/check_named_gl.py" --before "$BEFORE" --after "$AFTER" --bin "$BIN" --fixture "$EVIDENCE/ScopedGL.lean" --modules "$EVIDENCE/kernel-targets.txt" --output "$OUT/kernels"
python3 "$EVIDENCE/../pr120-ql-scope/git_lean_headers.py" --repo "$AFTER" --lean "$BIN/lean" --out "$OUT/headers.jsonl" "$CANDIDATE"
python3 "$EVIDENCE/matrix_build_targets.py" "$OUT/headers.jsonl" > "$OUT/build-targets.json"
(cd "$AFTER" && "$BIN/lake" build Main $(cat "$EVIDENCE/outside-targets.txt"))
```

To repeat the 36-target measurement, build the names in `combined-targets.txt` in each checkout. Use that file for `--targets` in the interface command. To check the two challenge exports, run the following command with the locked Mathlib dependencies installed.

```sh
python3 "$EVIDENCE/verify_challenge_export.py" --repo "$AFTER" --bin "$BIN" --packages "$AFTER/.lake/packages" --base "$PARENT" --merge "$CANDIDATE" --output "$OUT/challenge"
```

In a Git checkout of the cleanup, the following commands repeat the name scan and cover all 28 changed files.

```sh
python3 "$EVIDENCE/verify_retired_names.py" --repo . --revision 63e4077100de67259780b159cc7c528e9046ab29 --output "$OUT/removed-names.json"
"$BIN/lake" build $(cat "$EVIDENCE/followup-all-leaves.txt")
```

The JSON receipts record the revision, probe source hashes, diagnostics, and kernel checks. A full `Main` build and upstream Comparator on the five final statements are still required on the proposed merge commit. [Upstream verification instructions](https://github.com/leanprover-community/riemann-hypothesis/blob/9282d3a102c4aff0e6026746db2a8990f5d9cddd/README.md#checking-the-proof-yourself)
