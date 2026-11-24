# Scope of the two AdmLoc instances after batch 3

Roy7 built the stock and candidate versions of 1,000 affected modules. Both Lake runs exited 0. The strict comparison exited 1. All 12,825 public axiom records agree. Of 872 changed term fields, 869 passed direct kernel comparison in both environments. The other three passed after expansion of proof helpers. Six modules account for the strict failure. For each of their twelve flagged definitions, the two metadata dumps differ only in the regular unfolding height, from 9 to 8. These receipts cover six of the eight terminal targets. The remaining two are `Main` and `TwistRatios.AutIso`. [Roy7's run](https://github.com/leanprover-community/riemann-hypothesis/pull/911#issuecomment-7139478023) · [Pinned receipts](https://gist.github.com/roy7/db4def455fe93b5b7d58c87e86635b26/84d61140ee7235dce6fa95681fa0e1b03ab2c363)

To repeat the receipt check and run the remaining 587 modules, set `tools` as described below. Reuse the two original checkouts and build directories. Use a fresh output directory for this run.

```sh
git clone https://gist.github.com/db4def455fe93b5b7d58c87e86635b26.git "$out/roy7-gist"
python3 "$tools/c988/verify_roy7_receipt.py" "$out/roy7-gist" "$tools/c988/dependents.json" > "$out/remaining.txt"
cmp "$out/remaining.txt" "$tools/c988/remaining-587.txt"
python3 "$tools/run_dependents.py" --plan "$tools/c988/dependents.json" \
  --stock "$stock" --candidate "$candidate" --modules "$out/remaining.txt" --out "$out/remaining"
```

Community main is `c9883164b0b3d762cee21f889d03d59a53b3ba3b`. The candidate is `e05737b0d310930177bc746e7cf64f12d7731438`. The batch deleted the unreachable `CtrlMu` module. The candidate changes the provider and the four remaining modules that disabled `modFun`. There are 271 direct importers. The provider and its transitive importers account for 1,587 modules. Their eight terminal targets use 60,591 project sources on Lean 4.37.0-rc1. [Dependency list and revisions](dependents.json)

The first two runs cover the provider, `UnramifiedEnlargementCutCocyclesBlochKato`, `ImportsSide`, and `Smooth`. The second run verified 1,753 project source blobs on each side and completed all 14,240 Lake jobs. The four modules retain 217 public declarations and all 217 axiom sets. All 95 computational definitions match. Three stored types differ. Both kernels checked that each pair is definitionally equal. The records list each changed declaration. The previous 467-module run used the revisions in the parent directory. [Current run](stage2/result.json) · [Kernel records](stage2/new-conversion.jsonl) · [Build summaries](builds.json)

The third run adds `TOrdVan` and covers all four surviving sites that had disabled `modFun`, plus the provider. Both revisions completed all 42,045 Lake jobs after the runner checked 11,874 project source files against Git on each side. All 230 public declarations retain their axiom sets. All 96 definitions match. Four public types have different stored expressions. Lean's kernel accepts each pair as definitionally equal on each revision. To repeat this run, use `stage3/modules.txt` in the first command below. [Final direct-consumer run](stage3/result.json) · [Stock kernel](stage3/old-conversion.jsonl) · [Candidate kernel](stage3/new-conversion.jsonl)

The run over the 271 affected modules already present in this source closure includes all five direct cases above. Both revisions completed 42,045 Lake jobs. All 2,251 public declaration names and axiom sets agree. Both kernels checked 106 stored types, 36 definition bodies and three recursor rules that had changed. For three definition fields, the runner expanded private compiler proofs before the final conversion test. The 271 modules include direct and transitive importers. A further 1,316 affected modules remain outside this check. [Module list](271/modules.txt) · [Result](271/result.json) · [Candidate kernel](271/new-conversion.jsonl)

Use two clean checkouts at the revisions above with their pinned dependencies. Set `tools` to this evidence commit's `verification/pr120-admloc-dependents` directory. The first command repeats the four-module check. The second checks the full affected set, including `Main`. Use separate output directories. [Upstream candidate](https://github.com/leanprover-community/riemann-hypothesis/pull/911)

```sh
python3 "$tools/run_dependents.py" --plan "$tools/c988/dependents.json" \
  --stock "$stock" --candidate "$candidate" --modules "$tools/c988/stage2/modules.txt" --out "$out/four"
python3 "$tools/run_dependents.py" --plan "$tools/c988/dependents.json" \
  --stock "$stock" --candidate "$candidate" --out "$out/all"
```

The separate Lean 4.36 experiment uses the complete `CoordWD` member from the failed M4 build at `376bacf238f6f3a7a4f120aeb01c89d124ea7a66`. Its original graph has 1,639 project sources. Importing the provider adds two sources and reproduces the scalar-action timeout on the tensor product. Lev Khoroshansky's local erasure clears that diagnostic. Scoping only the two shortcuts at their source also clears it with the emitted proof unchanged. Both repaired modules pass kernel replay. [Lean 4.36 control and source hashes](coordwd-436.json) · [Lev's repair](https://github.com/rohanarun/riemann-hypothesis/commit/277ddc9ce64950f25f7742b0b730749fb90267c5)
