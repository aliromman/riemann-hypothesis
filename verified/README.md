# Current private-import comparison

The community parent is `cb4dc6e23a6187db392c96664295415c55b6b01e`. The proposal is `b880abd478236b392db065624391b785ad648b36`. The previous proposal included one more file. Restoring `TraceBlocks.lean` preserves the clean three-way merge of that file with the shared diagonal trace formula in community PR #1010. All other Lean blobs match the previous proposal. [Focused change](https://github.com/leanprover-community/riemann-hypothesis/pull/1010)

Run this command in a checkout that contains the two commits and the current community clump reader. Set `evidence` to a checkout of this evidence branch.

```sh
python3 "$evidence/audit_source.py" cb4dc6e23a6187db392c96664295415c55b6b01e b880abd478236b392db065624391b785ad648b36 \
  --targets "$evidence/targets.txt" --extra "$evidence/verified/extra-imports.json" --unclump > source-counts.json
cmp "$evidence/verified/source-counts.json" source-counts.json
```

The source comparison reads all 60,630 Lean files under `src`. It checks the commands that changed, the order of the surviving imports and the complete bytes after every changed header. The stock clump reader recovers the same 58,997 member sources from the 9,284 affected clumps. The 39,158 changed files lose 1,019,813 private imports and gain 382 specific imports from eight modules. Both the physical and nonblank line counts fall by 1,019,431.

Each row in `pairs.jsonl.gz` identifies the project module, the two Git blob IDs, the two complete source SHA-256 values and the numbers of removed and added imports. The dependency table counts the untouched direct and transitive importers. The declaration table identifies 882,359 occurrences from the authenticated parent. These include 744,881 theorem occurrences. Some private declaration names occur in more than one module. This gives 866,223 distinct typed Lean names, including 728,745 distinct theorem names.

The stock Linux timing sample and its independent theorem exports cover the same exact 143-module dependency closure on this head. All 715 relevant parent artifact hashes match. The whole-project default-target Lake build and full independent five-theorem Comparator export remain outstanding. [Stock Linux observations and public revision transfer](https://github.com/aliromman/riemann-hypothesis/tree/fab92b46202428ce498f9138773afe17c19c3917/ci/stock-batch-896/results/45370408013/)
