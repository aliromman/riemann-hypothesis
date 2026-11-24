# Reproduce the clump source comparison

This branch contains source evidence for [community pull request 977](https://github.com/leanprover-community/riemann-hypothesis/pull/977). The audit runs the actual clump readers and renderer from the two named Git commits. It also checks the original import headers, member order, preserved proof lines, the permitted scope fusions and the measured line counts. It has no Lean build or external Python package dependency.

The initial published comparison uses upstream `e23fe94c20626997fceadcc817237335a0602c20` and PR commit `bde5d32d9681e0e3b30295b53d7bdb45b6cf463a`. Use Python 3.12 with a local clone that contains both commits.

```sh
python3 audit_source.py e23fe94c20626997fceadcc817237335a0602c20 bde5d32d9681e0e3b30295b53d7bdb45b6cf463a --repo /path/to/riemann-hypothesis --output reproduced.jsonl.gz
cmp source-rows.jsonl.gz reproduced.jsonl.gz
```

Each compressed JSON line gives the path and SHA-256 for both source versions. The summary gives the totals across the changed clumps. Kernel checking and native artifact checks run separately, as documented on the pull request.

## Published follow-up

The current comparison is from community `9893104138b909cddb3dea39fb23d62d8f83141a` to PR commit `1ae1f79ed3f27986e4493a1c8fb6e21455d7467a`. The latter's `src` tree is `e4578d9cb1c96062bc9a81dbb3cb3aae8156cd6e`. Use the same command with those commits and compare the result to `current-source-rows.jsonl.gz`. The audit recovered all 68,250 members in 11,582 clumps. It permits exactly one of two scope adjustments to a changed original. It can combine the leading public scope and a file-wide noncomputable scope. When the erased command had an empty line directly on each side, it can remove one of those two empty lines. Every other line in each recovered original must match.

`count_lean_trees.py` inventories every tracked Lean file, including the nine outside `src/`. The four entries in `source-trees.json` are the parent, the two separate PRs and the local Git merge tree. To recreate the latter with Git, run the following command in the community clone after fetching both branches.

```sh
git merge-tree --write-tree --name-only --no-messages 07eee57ea636754a789d92f28c74bfa7d054157a 1ae1f79ed3f27986e4493a1c8fb6e21455d7467a
```

The result is `34dc399440138c56a6e20db29278f096b0053f8d`. No merge commit was created. Each row in `composition-bindings.jsonl.gz` gives the source module and SHA-256 values for the common parent, import PR, scope PR and combined file, in that order. Every one of the 9,220 shared files is the import PR's header followed by the scope PR's body. The sampled cross-PR check compiled 18 roots and their 49 affected project inputs in dependency order on both sides. `composition-native.jsonl` contains the original 49 proof and binary comparisons. `composition-transfer.json` records that all 49 pairs of source inputs to those comparisons also match the current pair of PRs. `planner-and-source.json` reports the independent full source, recovery, planner and downstream checks.

The clumper timing panel takes at most 10 files in each pair of top-level source directory and original member-count band (2, 3–4, 5–8, 9–16, or 17+). It orders eligible paths by the SHA-256 of `stock-clump-tools:` followed by the repository path. There are 257 selected paths. The timed calls are `unclump_text` and `render`. They exclude Git I/O and the common work to construct the in-memory modules. The run used Python 3.12 on macOS, one warm-up pair and five measured alternating pairs per file. `tool-summary.json` sums the per-file medians. Each row of `tool-timings.jsonl.gz` gives the path, trial, side (0 parent, 1 PR), then reader CPU, reader wall, renderer CPU and renderer wall in milliseconds.

```sh
python3 benchmark_clump.py 9893104138b909cddb3dea39fb23d62d8f83141a 1ae1f79ed3f27986e4493a1c8fb6e21455d7467a --repo /path/to/riemann-hypothesis
```

The repository's plan, apply and unclump CLI also passed a pinned Lean test with a quoted namespace component containing a dot. `cli-result.txt` records the comparison. `clumper-pr-compatibility.json` gives the actual upstream PR heads and outcomes for the three concurrent changes to the Python clumper. A successful combined test after adjusting a fixture is recorded separately from an unmodified combined run.

To measure the Python change independently from the additional scope sharing, use the same 257 files for both tool revisions. The following command reads the final sources on both sides. Its matching regenerated source check runs for every pair. The sums of median CPU times for reading were 79.622 and 52.112 milliseconds. The sums for rendering were 282.105 and 173.138 milliseconds. The raw pairs are in `tool-post-publication-timings.jsonl.gz`. The comparison with the upstream renderer remains in `tool-summary.json`.

```sh
python3 benchmark_clump.py bde5d32d9681e0e3b30295b53d7bdb45b6cf463a 1ae1f79ed3f27986e4493a1c8fb6e21455d7467a --same-inputs-from 1ae1f79ed3f27986e4493a1c8fb6e21455d7467a --repo /path/to/riemann-hypothesis
```
