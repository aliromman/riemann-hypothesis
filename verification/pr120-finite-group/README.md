# Finite enumeration on Lean 4.36.0

The M4 clean build reported three failures that involve the enumeration of the same finite product. The first appears in a convolution sum in `Bundle0041`, the second in the cardinality calculation in `AllRowsKpp`, and the third in the translated sum in `Bundle0381`. The original `finiteLevelGroupFintype` uses `Fintype.ofFinite`. The other enumeration, `finiteReductionGroup`, uses the dependent function instance. [M4 diagnostics](https://gist.github.com/maugomez77/9290bc2f18bcd6ec529050d1c1763cd9/19f1ea8a998e749ab8baa5c0f8f7243d805aa71c)

Select the dependent function instance in the provider with `by classical infer_instance`. Lean then proves equality with `finiteReductionGroup` by reflexivity. Equality with the previous enumeration follows from the subsingleton instance for `Fintype`. In each of the three complete source controls, the original imports compile, the extra provider causes one error, and the corrected provider gives zero errors. The six successful controls pass kernel replay. Both arms of the flag-measure test include the provider for the existing measurable-space attribute. [One-line change](https://github.com/aliromman/riemann-hypothesis/commit/f601612034a693e65e5e4ba73d8b8cf4eb285b1a) · [Rohan's merge](https://github.com/rohanarun/riemann-hypothesis/pull/937)

ArjunB3hl also repaired the consumers. These fixes are compatible with the provider change. Maugomez77 pinned the full comparison to Rohan's merge commit `2d20aa9035becfe380b9fe619e3d3fc968cf3400`. [Convolution](https://github.com/rohanarun/riemann-hypothesis/pull/906) · [Cardinality](https://github.com/rohanarun/riemann-hypothesis/pull/910) · [Flag measures](https://github.com/rohanarun/riemann-hypothesis/pull/913) · [Runner confirmation](https://github.com/leanprover-community/riemann-hypothesis/pull/120#issuecomment-7125768660)

## Repeat the controls

Use a clean checkout of `c7791603122c0328f79e49f6be5d7d4402effc53` with its locked packages. Make commit `376bacf238f6f3a7a4f120aeb01c89d124ea7a66` available in the same Git object database. Set `tools` to this directory in the evidence checkout. Use an empty directory for `out`.

```sh
python3 "$tools/check_finite_group.py" --repo "$PWD" --list-targets > "$out-targets.txt"
xargs lake build < "$out-targets.txt"
lake env python3 "$tools/check_finite_group.py" --repo "$PWD" \
    --original-lib "$PWD/.lake/build/lib/lean" --out "$out"
```

`receipts.json` contains the compiler and kernel results, source hashes, and the physical provider builds on Lean 4.36.0 and 4.37.0-rc1. The 4.36 provider build used 3,198 project inputs and 24,645 Lake jobs. These results cover the stated modules. The complete project and the five protected statements require separate checks.
