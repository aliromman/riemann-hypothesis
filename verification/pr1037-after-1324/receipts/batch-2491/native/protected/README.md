# Protected statements on the submitted #1037 tree

On `0e33c950c14ed48833fa38e401c9db04c4be5567`, all five compiled theorems have the types requested in the protected challenge. For each of the four project-defined propositions, Lean also accepted `rfl` between the solution definition and the definition copied from the challenge. For each theorem, `#print axioms` reported exactly `propext`, `Classical.choice` and `Quot.sound`. [Lean check](ProtectedStatements.lean) · [Theorem types and axioms](axioms.json) · [Compiled Main and full build](../README.md)

The kernel replay read the five proof terms from the compiled `Main`. It used the exact import setup that stock Lake generated for that module, with trust level zero. Lean rejected a control that substituted `True.intro` for the proof of `riemannHypothesis`. It then accepted all five original terms. The imported dependencies come from the native build. [Replay program](ReplayMain.lean) · [Kernel output](kernel.log) · [Input and program hashes](kernel.json)

The standalone native `leanchecker -v Statements Main` stopped when macOS reached its system file-table limit while reading private module data. The replay above uses the exported import data selected by Lake. The donor’s sandboxed Linux Comparator has its own run and receipt.

## Reproduce

Start at the root of a checkout of the tested commit. Build `Main` as described in the parent directory. Set `checks` to the absolute path of this evidence directory.

```sh
lake --no-cache lean "$checks/ProtectedStatements.lean"
lake --no-cache env lean -j1 --tstack=400000 --run "$checks/ReplayMain.lean" \
  .lake/build/lib/lean/Main.olean .lake/build/ir/Main.setup.json \
  riemannHypothesis riemannZeta_eq_zero_re LFunction_ne_zero_of_half_lt_re \
  LFunction_eq_zero_re LFunction_eq_zero_re_of_isPrimitive
```
