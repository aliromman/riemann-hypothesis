# Lean 4.36 check of the adelic GL instances

Brian Zhou's upstream PR #696 provides direct topological instances for the full, finite, and infinite adelic general linear groups. The port preserves the original Git author and patch ID. Its parent is Rohan's pinned integration commit. [Upstream PR](https://github.com/leanprover-community/riemann-hypothesis/pull/696) · [4.36 port](https://github.com/aliromman/riemann-hypothesis/commit/2cc9602ef874fbdf9f913545c8bc895c3e9cb812)

The original `IntegralLeToReal` proof builds on its original imports. Adding the two GL providers gives seven errors, including three timeouts for `SigmaCompactSpace`. Lowering the priority of the two local compactness instances and the SplitFlip second-countability instance leaves two errors. The first remaining failure asks for `T2Space`. Applying Brian's change clears all seven errors. The entire proof passes Lean's kernel with both providers present. The comparison with the original object found 12 matching public types and axiom records, one unchanged definition, and eight matching proof terms across 11 theorems. The five class probes give four errors before the port and zero after it. These counts apply to the controlled sources. [Compiler and kernel receipts](receipts.json)

The physical provider built and passed kernel replay before and after the change. All 16 project inputs matched Git. Each build completed 18,281 Lake jobs. The port retains the types and recorded axiom sets of all 39 existing public declarations. The kernel verified that the 36 new or updated instances return propositions and that their recorded axioms are permitted. The full integration still requires `Main`, `Challenge`, and upstream Comparator.

## Repeat the controls

Use Lean 4.36.0 and the pinned Mathlib packages. Set `repo` to a Git repository that contains both port commits and upstream PR #696. Set `original` to a checkout at `c7791603122c0328f79e49f6be5d7d4402effc53`. Use the original compiled project library there. Set `tools` to this directory and `out` to an empty directory.

```sh
cd "$original"
lake build \
  Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2Gluing.IntegralLeToReal \
  Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup \
  Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
lake env python3 "$tools/check_adelic_gl.py" --repo "$repo" \
  --original-lib "$original/.lake/build/lib/lean" --out "$out"
```

To repeat the physical build, run the following commands in checkouts of the parent and the port. Keep their compiled objects in separate directories.

```sh
lake build GroundTheory.AutomorphicForms.AdelicGLn
lake env leanchecker -v GroundTheory.AutomorphicForms.AdelicGLn
```

In the port checkout, compare the two objects. Keep the adjacent `.olean.server` and `.olean.private` files in their respective directories.

```sh
lake env lean --run "$tools/CheckAdelicHub.lean" "$oldOlean" "$newOlean" \
  GroundTheory.AutomorphicForms.AdelicGLn
```
