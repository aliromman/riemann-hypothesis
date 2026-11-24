# Scope of the two AdmLoc instances after batch 3

Community main is `c9883164b0b3d762cee21f889d03d59a53b3ba3b`. The candidate is `e05737b0d310930177bc746e7cf64f12d7731438`. The batch deleted the unreachable `CtrlMu` module. The candidate changes the provider and the four remaining modules that disabled `modFun`. There are 271 direct importers. The provider and its transitive importers account for 1,587 modules. Their eight terminal targets use 60,591 project sources on Lean 4.37.0-rc1. [Dependency list and revisions](dependents.json)

The first two runs cover the provider, `UnramifiedEnlargementCutCocyclesBlochKato`, `ImportsSide`, and `Smooth`. The second run verified 1,753 project source blobs on each side and completed all 14,240 Lake jobs. The four modules retain 217 public declarations and all 217 axiom sets. All 95 computational definitions match. Three stored types differ. Both kernels checked that each pair is definitionally equal. The records list each changed declaration. The previous 467-module run used the revisions in the parent directory. [Current run](stage2/result.json) · [Kernel records](stage2/new-conversion.jsonl) · [Build summaries](builds.json)

Use two clean checkouts at the revisions above with their pinned dependencies. Set `tools` to this evidence commit's `verification/pr120-admloc-dependents` directory. The first command repeats the four-module check. The second checks the full affected set, including `Main`. Use separate output directories. [Upstream candidate](https://github.com/leanprover-community/riemann-hypothesis/pull/911)

```sh
python3 "$tools/run_dependents.py" --plan "$tools/c988/dependents.json" \
  --stock "$stock" --candidate "$candidate" --modules "$tools/c988/stage2/modules.txt" --out "$out/four"
python3 "$tools/run_dependents.py" --plan "$tools/c988/dependents.json" \
  --stock "$stock" --candidate "$candidate" --out "$out/all"
```

The separate Lean 4.36 experiment uses the complete `CoordWD` member from the failed M4 build at `376bacf238f6f3a7a4f120aeb01c89d124ea7a66`. Its original graph has 1,639 project sources. Importing the provider adds two sources and reproduces the scalar-action timeout on the tensor product. Lev Khoroshansky's local erasure clears that diagnostic. Scoping only the two shortcuts at their source also clears it with the emitted proof unchanged. Both repaired modules pass kernel replay. [Lean 4.36 control and source hashes](coordwd-436.json) · [Lev's repair](https://github.com/rohanarun/riemann-hypothesis/commit/277ddc9ce64950f25f7742b0b730749fb90267c5)
