# Current private-import comparison

The community parent is `cb4dc6e23a6187db392c96664295415c55b6b01e`. The proposal is `c2c7fc890448cf0c8eab464f115e5e370129697a`. The coordination review restored the original header in the diagonal trace formula and 21 headers in the Siegel–Weil proof. The other module bodies retain the earlier proposal. [Shared trace formula](https://github.com/leanprover-community/riemann-hypothesis/pull/1010) · [Siegel–Weil proof migration](https://github.com/leanprover-community/riemann-hypothesis/pull/798)

Run this command in a checkout that contains the two commits and the current community clump reader. Set `evidence` to a checkout of this evidence branch.

```sh
python3 "$evidence/audit_source.py" cb4dc6e23a6187db392c96664295415c55b6b01e c2c7fc890448cf0c8eab464f115e5e370129697a \
  --targets "$evidence/targets.txt" --extra "$evidence/verified/extra-imports.json" --unclump > source-counts.json
cmp "$evidence/verified/source-counts.json" source-counts.json
```

The source comparison reads all 60,630 Lean files under `src`. It checks the commands that changed, the order of the surviving imports and the complete bytes after every changed header. The stock clump reader recovers the same 58,990 member sources from the 9,281 affected clumps. The 39,137 changed files lose 1,019,288 private imports and gain 382 specific imports from eight modules. Both the physical and nonblank line counts fall by 1,018,906.

Each row in `pairs.jsonl.gz` identifies the project module, the two Git blob IDs, the two complete source SHA-256 values and the numbers of removed and added imports. The dependency table counts the untouched direct and transitive importers. The declaration table identifies 882,106 occurrences from the authenticated parent. These include 744,640 theorem occurrences. Some private declaration names occur in more than one module. This gives 866,001 distinct typed Lean names, including 728,535 distinct theorem names.

The stock Linux timing sample and its independent theorem exports cover the same exact 143-module dependency closure on this head. All 715 relevant parent artifact hashes match. The whole-project default-target Lake build and full independent five-theorem Comparator export remain outstanding. [Stock Linux observations and public revision transfer](https://github.com/aliromman/riemann-hypothesis/tree/eb4fe9d9c9cb672237955b3fb3b000975d1e9b4d/ci/stock-batch-896/results/45370408013/)
