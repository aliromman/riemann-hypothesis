# Matrix instance checks after batch #2057

Community main `27b55787485ac2a5b5b3ed2dffc697e0ae6a2f59` still has the two matrix-measure errors from #1037. With `LinUnit.eq_zero_of_ip_eq_zero` unchanged, the proof fails in both provider import orders. The same proof compiles in both orders with the three-file change. Opening the scoped GL instances gives the same result.

| Check on Lean 4.37.0-rc1 | Merged main | Main with #1037 |
| --- | ---: | ---: |
| Errors on the full proof, providers in forward order | 2 | 0 |
| Errors on the full proof, providers in reverse order | 2 | 0 |
| Errors in the three reducible equalities naming the providers | 3 | 0 |
| Errors in the scoped GL test | 0 | 0 |
| Kernel checks of `EqZeroOfIpEqZero` and `GJFEInducedLevi` | 2 passed | 2 passed |

The source tree with #1037 is `076dbeb7aef775429d59a1fc853f5b83e31d2878`. Reproduce it with `git merge-tree --write-tree 27b55787485ac2a5b5b3ed2dffc697e0ae6a2f59 41596f52921c716692c643accdcb210ef1e470d0`. The five targets use 311 project modules. Compared with the earlier batch #1739 control, 24 sources in this set changed. All 311 input blobs for the candidate agree with the merge tree. Stock Lake built the five targets on both revisions. It compiled all 15 affected modules in the candidate. [Build record](build.json) · [Changed dependencies](dependencies.json)

To repeat the import-order tests, build the targets in `build.json` in both checkouts. Run `replay_matrix_selection.py --before "$main" --after "$candidate" --bin "$lean_bin" --output "$closed"`. Repeat with `--open-double-coset-scope` and a separate output directory. Use `lake env lean` on the two named probes and `lake env leanchecker -v` on each caller. The confirmed Linux build pin remains `0c252f795aa6a96b7dd3c21896114f0611428594`. [Replay program](../../replay_matrix_selection.py) · [Closed scope](closed.json) · [Open scope](open.json) · [Named probes and kernel exits](callers.json)
