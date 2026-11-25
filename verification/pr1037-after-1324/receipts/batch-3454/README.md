# Matrix measures after community batch #3454

This comparison uses community main `91b273530883b723ef4422436e0dc3557749325a` and the verification merge `072861f0298383f29c96fdf23141dc4412530713`. The merge has main and the submitted #1037 head `ef7b2af7f6017c9e6875d4d8803907ac0cd8804b` as its parents. Git gives tree `b7661647765848f6b0b0476f56ad3c537caea1fe`. The four-file change preserves all protected inputs. The community batch left the three cross-directory instance definitions for a maintainer decision. [Batch](https://github.com/leanprover-community/riemann-hypothesis/pull/3454) · [Verification merge](https://github.com/aliromman/riemann-hypothesis/commit/072861f0298383f29c96fdf23141dc4412530713) · [Git inputs](integration.json)

| Test on the pinned Lean 4.37.0-rc1 release | Main | With #1037 |
| --- | --- | --- |
| Actual `eq_zero_of_ip_eq_zero` proof with widened imports, each of two orders and two GL scope settings | 2 errors per case | 0 in all four cases |
| Three named matrix instances equal to Mathlib's instance by `rfl` | 3 errors | 0 |
| Archived `SingleQ.localZ_map` fragment after Daniel Ang's #1324, both import orders | Both pass | Both pass |
| Two scoped GL instances and the compiled `GJFEInducedLevi` caller | Pass | Pass |
| Compiled `GJFELevi` with the direct use of `GJMatrix.measurableSpace_matrix` at line 307 | Pass | Pass |

In the widened proof, instance synthesis fails for `IsFiniteMeasureOnCompacts (volM ν b a)`. The three reducible definitions in #1037 use Mathlib's matrix measurable space. This lets Lean use the measure instance under both import orders. The project Borel instance still appears in some successful probes. [Both orders with the scope closed](scope-closed.json) · [Both orders with the scope open](scope-open.json) · [Named instances and kernels](callers.json) · [Archived proof fragment](doubling.json) · [Complete archived proof on the submitted tree](../batch-2491/doubling.json)

The five-target test now needs 314 project sources. Three entered the closure and 77 existing sources changed since batch #2960. Stock Lake rebuilt 201 modules per side. The extra GL caller required 109 project sources. The test reused 101, compiled eight and excluded 213 modules from the earlier build. The caller passed stock kernel replay on both revisions. [Five-target builds](builds.json) · [Extra caller builds](explicit/builds.json) · [Caller source and kernel receipts](explicit/kernel.json)

Two scans of all 59,239 Lean sources agree on the 66 whole-name lines. There are three declarations, five comments, 53 attribute lines and five direct term uses in the source inventory. The same 23 files consume the declarations. Since #2960, 21 of those files have other source changes. On the submitted PR tree, the nine default targets and all 23 callers passed. The full Linux Comparator uses that submitted tree. [Main inventory](base-names.json) · [Merge inventory](candidate-names.json) · [Full native build](../batch-2491/native/README.md) · [Five protected statements](../batch-2491/native/protected/README.md)

## Reproduce

Use separate checkouts of the two commits above with their pinned toolchain and dependencies. Set `BEFORE` and `AFTER` to the checkout paths. Set `EVIDENCE` to the directory containing the matrix scripts and `OUT` to an empty directory for the results. Run the five-target build, both scope probes and the named caller checks. [Five-target commands](../batch-2318/README.md#reproduce) · [Archived proof command](../batch-2787/README.md#reproduce)

```sh
for project in "$BEFORE" "$AFTER"; do
  (cd "$project" &&
    lake --no-cache --rehash build GroundTheory.AutomorphicForms.GL2.GJFELevi &&
    lake --no-cache --rehash build --no-build GroundTheory.AutomorphicForms.GL2.GJFELevi &&
    lake --no-cache env leanchecker -v GroundTheory.AutomorphicForms.GL2.GJFELevi) || exit 1
done
```

For incremental reproduction, `advance_matrix_probes.py` reads each new import closure from the pinned Lean parser and checks the sources against Git. It copies only build facets for modules present in both closures. Lake rehashes the inputs. The optional `--targets` file selects the additional caller. Local Lake setup files contain checkout paths and are generated in the new workspace. [Build driver](../../advance_matrix_probes.py) · [Git and Lean import check](../../audit_cone.py)
