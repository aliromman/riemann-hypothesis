# Reproduce the clump source comparison

This branch contains source evidence for [community pull request 977](https://github.com/leanprover-community/riemann-hypothesis/pull/977). The audit runs the actual clump readers and renderer from the two named Git commits. It also checks the original import headers, member order, preserved proof lines, the permitted scope fusions and the measured line counts. It has no Lean build or external Python package dependency.

The initial published comparison uses upstream `e23fe94c20626997fceadcc817237335a0602c20` and PR commit `bde5d32d9681e0e3b30295b53d7bdb45b6cf463a`. Use Python 3.12 with a local clone that contains both commits.

```sh
python3 audit_source.py e23fe94c20626997fceadcc817237335a0602c20 bde5d32d9681e0e3b30295b53d7bdb45b6cf463a --repo /path/to/riemann-hypothesis --output reproduced.jsonl.gz
cmp source-rows.jsonl.gz reproduced.jsonl.gz
```

Each compressed JSON line gives the path and SHA-256 for both source versions. The summary gives the totals across the changed clumps. Kernel checking and native artifact checks run separately, as documented on the pull request.
