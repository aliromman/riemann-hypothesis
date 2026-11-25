# Reproduce the AdmLoc instance conflict

Batch #1739 removed the local registration of `UpperTheory.V.W.coefLocal` from `TOrdVan`. PR #911 removes the adjacent global `AdmLoc.modFun` erasure. Commit `de4bda63f26e11fc0b312f4a890dd46fd05d6217` keeps both removals. Its stock parent for this comparison is `4a5b4a2d2a5177a2b6cb876425f0cb4cb6b85061`. The five-source patch also applies on batch #1801 as `b57e4300c7a69d82a26b6262670ffe1274f2722e`. The binary Git diff against each batch is identical.

Build the five modules in `targets.txt` and `Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound` in each checkout. Use the locked packages and Lean 4.37.0-rc1. Then run the script. It takes the complete Satake proof from Git, inserts the instance provider as the first or last import and checks the intended caller with the Lean kernel.

```sh
python3 "$tools/replay_exposed_satake.py" --repo "$repo" \
  --before "$stock" --after "$candidate" --bin "$lean_bin" --output "$out" \
  --parent 4a5b4a2d2a5177a2b6cb876425f0cb4cb6b85061 \
  --candidate de4bda63f26e11fc0b312f4a890dd46fd05d6217
```

Both native Lake builds passed five targets over 2,068 project modules. Each import order produced 45 error diagnostics on stock and zero on the candidate. The original `ResBound` passed kernel replay on both sides. This run covers four of the five changed files. The large `TOrdVan` target, full `Main`, and the five-statement Comparator still need results on the integration revision. Roy7’s full affected-module results use the earlier `e05737b0d310` candidate. [Roy7’s results](https://github.com/leanprover-community/riemann-hypothesis/pull/911#issuecomment-7144623036)
