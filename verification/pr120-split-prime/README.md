# Reproduce the split-prime interface failure on Lean 4.36

The two theorems `GlobalTheory.DualSplitRel.exists_idem` and `GlobalTheory.DualSplitRel.dual_rel` take a condition on a conjugate prime. The original interface uses `Formalism.DivisionValues.conjPl`. The interface after author PR #701 uses `Formalism.L2.DIV.conjPl`. The caller in `GlobalTheory.Hk3.Link.eig_rel` supplies the first condition.

The test uses the complete provider body from each Git revision and the complete caller body from the integrated bundle. It gives both builds the same original imports and includes the second prime provider. The original dependency closure for the test contains 1,901 project modules. The parent provider compiles, but the caller fails at `DualSplitRel.dual_rel V P hP`. On the repair, the provider and the same caller compile. Both compiled modules pass native kernel replay. The source environment for this experiment uses the original member dependencies. The full bundle build still runs against the integrated imports.

Use a clean original 4.36 checkout at `c7791603122c0328f79e49f6be5d7d4402effc53`. Fetch the repair branch to make both Git revisions available there. Set `replay` to the absolute path of `replay_split_prime.py`. Then run the commands below.

```sh
git fetch https://github.com/aliromman/riemann-hypothesis.git codex/pr120-restore-split-prime-interface
lake build Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualSplitLabelOperatorMulScalarOperator Development.AbelianVarietyTheory.Proofs.SatakeParameters.LiftSplitHeckePolysEqTransferResidualPolys Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
lake env python3 "$replay" --repo "$PWD" --original-lib "$PWD/.lake/build/lib/lean"
```

The program gives each revision separate outputs in a temporary directory. It checks the diagnostic from the old caller. It runs the pinned `leanchecker` on both repaired modules. The JSON records the Git revisions, source hashes, native diagnostic and kernel exit codes.

To build the integrated physical files, use `lake build Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualSplitLabelOperatorMulScalarOperator Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0184` on the parent and repair. [Earlier proof repair and diagnosis](https://github.com/rohanarun/riemann-hypothesis/pull/701).
