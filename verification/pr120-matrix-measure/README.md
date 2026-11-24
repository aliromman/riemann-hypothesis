# Entrywise measurable spaces on matrices

The M4 operator reported eight errors in `SingleBlockDoublingIntegralValue` on Lean 4.36. The first failed tactic rewrites an integral against a mapped measure. The binder and the expected argument use different instances for the measurable space on the same matrix type. Kristof Gazso and meltingice found the reverse problem in `EqZeroOfIpEqZero`. [M4 diagnostic](https://github.com/leanprover-community/riemann-hypothesis/pull/120#issuecomment-7128951255) · [Earlier reverse case](https://github.com/rohanarun/riemann-hypothesis/pull/325) · [Initial repair](https://github.com/rohanarun/riemann-hypothesis/pull/323)

All three project instances now use Mathlib’s `Matrix.instMeasurableSpace`. Each retains its original name, type and instance priority. The reducible attribute lets Lean see the same product measurable space through each name. The previous `inferInstanceAs` bodies in `StatementZ` and `GJMatrixCoord` introduced separate auxiliary definitions. Marking the old definitions reducible leaves all eight errors. [4.36 fix](https://github.com/rohanarun/riemann-hypothesis/pull/1003) · [Current-main fix](https://github.com/leanprover-community/riemann-hypothesis/pull/1037)

| Complete proof body or check | Stock | Repaired |
| --- | ---: | ---: |
| Doubling integral, 4.36 and 4.37 | 8 | 0 |
| Finite measure on compact sets, 4.36 and 4.37 | 2 | 0 |
| Six equalities among the four instance names at reducible transparency, 4.37 | 6 | 0 |

The two opposite import orders of the finite-measure proof on 4.36 each produce the second row. A separate control in `LConvSepI` still fails to find a right-invariant Haar measure on GL. The operator stopped after the terminal run of `2d20aa90`. The closing head of upstream #120 did not receive a full build or a Comparator result. [Terminal run](https://github.com/rohanarun/alpoge-rh-replay/issues/35028#issuecomment-7129630352)

## Repeat the Lean 4.36 test

Use an original checkout at `c7791603122c0328f79e49f6be5d7d4402effc53` with its pinned packages. Fetch the fix branch into that repository. Set `tools` to this verification directory and `scratch` to an empty directory. Build these original modules once. The compiler uses the resulting project and Mathlib objects for all six test runs.

```sh
git fetch https://github.com/aliromman/riemann-hypothesis.git codex/pr120-doubling-integral
lake build \
  Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SingleBlockDoublingIntegralValue \
  Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfIpEqZero \
  Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq \
  Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup \
  Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL \
  Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace \
  Formalism.DoubleCosetMeasures.StatementZ GroundTheory.AutomorphicForms.GL2.GJMatrixCoord
lake env python3 "$tools/replay_matrix.py" --repo "$PWD" --stock-lib "$PWD/.lake/build/lib/lean" \
  --output "$scratch" --patch 23c7afaae01c537a52a59af26be71d65027b645f
```

The doubling-integral proof body comes from the integration base `21f32da2751f7db09c38ef6d1dfb1cf961eb3c3b`. Its physical module on the M4 has 22,435 project inputs. The portable test uses 1,365 historical inputs. A separate 8,066-input replay reproduced the eight failures and checked the repaired proof with `leanchecker`. The two widened proof bodies, the original two proof bodies with the new providers, and the three revised providers each passed native kernel replay. The five original-header modules retain all 87 public type and axiom records. [Compiler diagnostics](4.36-replay.json) · [Kernel results](4.36-kernels.json)

## Repeat the Lean 4.37 test

Use two checkouts with the same locked packages. Set `before` to `cb4dc6e23a6187db392c96664295415c55b6b01e` and `after` to `9e3763eda12bcd2e82c4a7d6b0378b6a4c3feb10`. Set `bin` to the pinned Lean 4.37.0-rc1 toolchain’s bin directory. Build the five targets in each checkout.

```sh
(cd "$before" && xargs lake build < "$tools/targets-4.37.txt")
(cd "$after" && xargs lake build < "$tools/targets-4.37.txt")
python3 "$tools/replay_current_matrix.py" --before "$before" --after "$after" --bin "$bin" --output "$scratch"
```

Both normal builds completed 11,989 Lake jobs across the same 829 project source paths. Each of the five candidate targets passed native kernel replay. All 88 public types and axiom records agree. The definition checks compare the old and new values in both kernels with the Mathlib declaration in scope. They expand each obsolete compiler auxiliary from the object that defines it before comparing the two values. Three provider bodies and the compiler’s unfolding height for `rowEqM` changed. [Build and kernel results](4.37-verification.json) · [Definition comparisons](4.37-definitions.json) · [Widened proofs](4.37-widened.json)


The three providers have 293 direct project importers. The transitive set has 14,667 modules including the providers. Of these, 14,653 are dependencies of `Main`. The two source cones used here contain 23 affected modules. The upstream draft still requires the complete build. [Project import graph](affected-import-graph.json)

## Repeat the definition checks

The Lean checker reads the stock and candidate objects for each of the three providers and for `rowEqM`. It checks their types and values in both environments. The Python driver verifies all eight results against the receipt for the selected toolchain.

On 4.36, run the proof replay above first. It recompiles the original doubling-integral source with the three changed providers in a separate directory. From the original checkout, run the following commands with the same `scratch` and `tools` paths.

```sh
stock_path=$(lake env printenv LEAN_PATH)
python3 "$tools/compare_matrix_definitions.py" --lean "$(command -v lean)" \
  --stock-path "$stock_path" --candidate-path "$scratch/original-header:$stock_path" \
  --expected "$tools/4.36-definitions.json"
```

On 4.37, use the two built checkouts from the previous section. Lake supplies the absolute object paths for each checkout.

```sh
stock_path=$(cd "$before" && "$bin/lake" env printenv LEAN_PATH)
candidate_path=$(cd "$after" && "$bin/lake" env printenv LEAN_PATH)
python3 "$tools/compare_matrix_definitions.py" --lean "$bin/lean" \
  --stock-path "$stock_path" --candidate-path "$candidate_path" \
  --expected "$tools/4.37-definitions.json"
```
