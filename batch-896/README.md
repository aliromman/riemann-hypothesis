# Batch 896 source and dependency evidence

This comparison uses `c9883164b0b3d762cee21f889d03d59a53b3ba3b` and the published import branch `c4b66990077a462b2e2d35777fe0f55644463e87`. The new community batch changed 338 owners in the previous selection. The integration retains their new proof bodies. The selection sets aside 1,322 sources after checking 271 active proposals and the parent clump records. This includes an existing clump that the parent's own unclumper cannot parse. The parent has 60,630 files under `src/`.

Run the source comparison from a repository checkout that contains both commits. Set `evidence` to the path of a checkout of this evidence branch.

```sh
python3 "$evidence/audit_source.py" c9883164b0b3d762cee21f889d03d59a53b3ba3b c4b66990077a462b2e2d35777fe0f55644463e87 \
  --targets "$evidence/targets.txt" --extra "$evidence/batch-896/extra-imports.json" --unclump > source-counts.json
cmp "$evidence/batch-896/source-counts.json" source-counts.json
```

`source-pairs.json.gz` maps each qualified module name to its two Git blob IDs, two source SHA-256 values, number of removed imports and number of added imports, in that order. The 39,159 rows cover the entire source change. `dependencies.json` counts distinct unedited downstream modules and records the parent import graph. `held-paths.json` lists the returned paths. The seven targets of project `import all` are outside the edited set.

The source audit checks the import flags, order of all surviving imports, every proof body and the original members reconstructed by the community unclumper. The native comparison uses the official parent receipt, original project objects, pinned compiler and Mathlib. `transferred-inputs.json` records the subset whose source and effective imported files match an earlier native comparison. The other 29,208 files are assigned to fresh comparisons. The complete five declarations, their proofs, axiom lists, and the frozen Challenge are checked separately at the assembled root. The full default-target stock build and complete five-theorem independent Comparator export are additional obligations.

The previous revision has a permanent receipt under `previous-649/` at the root of this evidence branch. It refers only to the earlier 40,481-file selection. [Earlier five-claim job](https://github.com/aliromman/riemann-hypothesis/actions/runs/45365163169) · [Current native comparison](https://github.com/aliromman/riemann-hypothesis/actions/runs/45365901389) · [Current stock Lake and theorem sample](https://github.com/aliromman/riemann-hypothesis/actions/runs/45368083272)
