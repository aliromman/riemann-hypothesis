# Unit morphisms in two divisibility proofs

At Waterloo the pinned full `Bundle1269` still failed on the domain unit after #952. ArjunB3hl’s #999 qualified `MonoidHom.map_one` and the complete module passed on the 20,764-input native dependency graph. On the later integration, the complete member and reconstructed bundle also pass native kernel replay. Cheng’s #1000 retains all 44 public types and axiom sets of its previous Hecke–Fubini bundle. [Waterloo check](https://github.com/rohanarun/riemann-hypothesis/pull/999) · [Successor checks](successor-21f32.json)

The M4 build at `2d20aa9035becfe380b9fe619e3d3fc968cf3400` reached `DivisorProofs.Bundle1269` after its dependency `Bundle1254` built. The compiler failed at `map_one` on line 123. Rmsnorm supplied the unit on the relevant morphism type in author PR #952. The fix is also in `92e91959e3fbd8a3533172cffdb6272143341d1f`. The same PR changes a second proof in `Bundle1447`. [M4 report](https://github.com/leanprover-community/riemann-hypothesis/pull/120#issuecomment-7128029551) · [Rmsnorm’s patch](https://github.com/rohanarun/riemann-hypothesis/pull/952)

`CanonicalUnit.lean` proves by reflexivity that the supplied `OfNat` instance is the standard instance on morphisms into a monoid object in a Cartesian monoidal category. It also checks Mathlib’s `Hom.one_def`. Both proofs use only the three axioms listed in the project’s Comparator configuration. [Lean source](CanonicalUnit.lean) · [Axiom output](canonical.log)

The complete repaired `FiniteEtalePointOfExt` member compiled on its historical imports with an extra `rfl` check at the point of use. Kernel replay passed. Lean’s `Expr.equal` matched all nine stored public theorem types. Their nine recorded axiom sets agree with the original object. The complete three-member bundle body compiled and passed kernel replay both before and after the repair when its direct imports were expanded to historical modules (4,478 project inputs). Separately, the old proof compiled with up to 1,317 additional instance-provider modules (8,815 historical project inputs). The actual M4 target has 20,764 physical project inputs. Its exact compiler diagnostic and a build of the repaired physical bundle on the author’s integration remain relevant. [Targeted native checks](bundle1269.json)

To repeat the member comparisons, fetch the three author commits used by the script. Use a checkout of the original source revision `c7791603122c0328f79e49f6be5d7d4402effc53` with its stock Lean 4.36.0 toolchain and package lock. Set `evidence` to the `verification/pr120-hom-units` directory in this evidence commit. Use an empty output directory.

```sh
lake build Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEtalePointOfExt \
           Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisibleAlgClosureOfKillsTorsionSepClosed
lake env python3 "$evidence/replay_units.py" --repo "$PWD" \
  --original-lib "$PWD/.lake/build/lib/lean" --out "$out"
lake env lean "$evidence/CanonicalUnit.lean"
```

For a check with the physical imports on the integration commit, run `lake build Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1269 Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1447` on that commit. The project-wide proof check is `lake build Main` followed by the upstream Comparator on the same commit.
