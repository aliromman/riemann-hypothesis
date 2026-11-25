# Matrix instance checks after batch #2960

Community main `8e5cefeeaffe7e4c12153385b7bb33fb7223c41a` and the #1037 head `ef7b2af7f6017c9e6875d4d8803907ac0cd8804b` merge without conflicts. The verification commit has these two parents in that order. Its Git tree is `a03ec152b3a37f25023d24325531448bf08ab0ca`. Both source trees have 59,360 Lean files. The PR changes four files, with 12 additions and eight deletions. [Verification commit](https://github.com/aliromman/riemann-hypothesis/commit/ac7b31c0da50c61cf2d0408818076ac442742650) · [Git counts and changed paths](merge.json)

Daniel Ang removed 40 private Mathlib imports from `MatrixMeasurableSpace.lean`. The merge retains those removals and adds the public import that supplies `Matrix.instMeasurableSpace`. The batch also changed seven files that refer to the providers. Compared with the preceding proposed merge, all 26 files retain the same lines that name the three providers. [Daniel's change](https://github.com/leanprover-community/riemann-hypothesis/commit/6e155e618231abc8913eeadf4af82564a5aebfbc) · [Changes in the seven consumers](caller-changes.json)

| Lean 4.37.0-rc1 check | Batch #2960 | Batch #2960 with #1037 |
| --- | --- | --- |
| Full `LinUnit.eq_zero_of_ip_eq_zero` proof with each provider order and with the GL scope open or closed | 2 errors in each of 4 cases | All 4 pass |
| Three provider definitions compared with Mathlib by reducible `rfl` | 3 errors | All 3 pass |
| Two scoped GL instance names | Both selected | Both selected |
| Native kernel replay of `EqZeroOfIpEqZero` and `GJFEInducedLevi` | Both pass | Both pass |
| Archived `localZ_map` proof fragment, both provider orders | Both pass | Both pass |

Stock Lake built the five targets and confirmed that they were up to date. Of 311 project sources, 11 changed in the batch. Lake compiled 40 modules on each side. The commands completed 10,471 jobs on main and 10,473 on the merge. The archived fragment already passes with Daniel Ang's #1324. The earlier comparison also checks the complete archived doubling proof. [Builds](builds.json) · [Scope closed](scope-closed.json) · [Scope open](scope-open.json) · [Caller checks](callers.json) · [Archived fragment](doubling.json) · [Complete archived proof](../batch-2491/doubling.json)

Two scans of all 59,360 sources agree. The three names occur as whole words on 66 lines. These include three declarations, five comment lines, 53 attribute commands and five direct term references. There are 23 consumer files. Three additional lines contain the longer identifiers `matrixMeasurableSpaceReal` or `matrixMeasurableSpaceComplex`. [Main source lines](base-named-lines.json) · [Merge source lines](candidate-named-lines.json) · [Reviewed uses](named-uses.json)

## Reproduce

Use separate checkouts of the main and verification commits above. Set `EVIDENCE` to the directory that contains the matrix test scripts. Use the five-target build and both scope commands from the previous instructions. Run the caller and doubling probes in the same two checkouts. [Build and scope commands](../batch-2318/README.md#reproduce) · [Doubling command](../batch-2787/README.md#reproduce)

```sh
python3 "$EVIDENCE/scan_matrix_names.py" --repo "$BEFORE" \
  --revision 8e5cefeeaffe7e4c12153385b7bb33fb7223c41a --output "$OUT/main-names.json"
python3 "$EVIDENCE/scan_matrix_names.py" --repo "$AFTER" \
  --revision ac7b31c0da50c61cf2d0408818076ac442742650 --output "$OUT/merge-names.json"
```
