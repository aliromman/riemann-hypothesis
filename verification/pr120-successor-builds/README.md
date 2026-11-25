# Community successor builds

The receipts in this directory record stock Lake builds on specific Git merge commits. They include the command, exit code, compiler, source tree and SHA-256 of each log. The build reads verified CI artifacts for modules whose source and transitive imports are unchanged. It compiles the affected modules from the proposed merge. The separate Linux Comparator checks the five protected theorems and the permitted axioms.

## Reproduce a build

Start in a clean checkout of the merge. Use Python 3.12 and the Lean version in `lean-toolchain`. Fetch the Mathlib cache with the upstream command. Set `evidence` to the root of a checkout of this verification branch. Keep the run directory until all build stages finish.

```bash
project=$PWD
run=$(mktemp -d)
bin=$(dirname "$(elan which lean)")
merge=$(git rev-parse HEAD)
base=$(git rev-parse HEAD^1)
scripts="$evidence/verification/pr120-successor-builds"
MATHLIB_CACHE_GET_URL=https://cache.mathlib.org/mathlib4 lake exe mathlib/cache get
python3.12 "$evidence/verification/pr120-ql-scope/git_lean_headers.py" \
  --repo "$project" --lean "$bin/lean" --out "$run/headers.jsonl" "$merge"
warm=(python3.12 "$scripts/warm_unaffected_native.py" --project "$project" \
  --headers "$run/headers.jsonl" --metadata "$run/base-cache" --out "$run/receipts" \
  --bin "$bin" --base "$base" --head "$merge")
record=(python3.12 "$scripts/record_native_full.py" --project "$project" \
  --out "$run/receipts" --bin "$bin" --jobs 3)
"${warm[@]}" --stage main Main
"${record[@]}" --stage main Main
"${warm[@]}" --stage all
"${record[@]}" --stage all
```

Each record includes a second `lake build --no-build` check. To reuse archives already on disk, add `--donor /path/to/artifacts` to the `warm` arguments. The script checks each archive against the SHA-256 in the first parent's CI manifest. Without a local archive it fetches the matching file from the community cache. To run a smaller target set, give both commands the same stage name and the same target list.

## PR #911

Merge `c3679d4a79d297efdb223876790f02faf1819618` includes PR head `b57e4300c7a69d82a26b6262670ffe1274f2722e` and community batch `fcb6eac7534875d32d68030967e2deae6d686151`. The first seven targets cover all five edited modules, the intended `ResBound` caller and the complete Satake proof. Both Lake commands exited 0. The first command completed 42,245 jobs. The dependency graph contains 11,974 project modules for these targets. Of those, 272 depend on the change. [Target list](911-c3679d4a/callers.txt) · [Build receipt](911-c3679d4a/callers.json) · [Archive counts and manifest](911-c3679d4a/callers-restored.json) · [Compressed build log](911-c3679d4a/callers-build.log.gz)

## Linux Comparator

Use a fresh checkout of the proposed merge on a Linux machine with bubblewrap. Run as an ordinary user. Set `expected` to the full commit that the operator agreed to check. Set `results` to an existing directory outside the checkout. Run the script from the checkout. It prints the name of a new directory for the report.

```sh
sh "$evidence/verification/pr120-successor-builds/run_linux_comparator.sh" "$expected" "$results"
```

The script adds the pinned Lean release to `PATH` so Comparator can find the external kernels. It fetches the Mathlib cache, runs upstream `lake comparator --json`, and records each exit code. Keep the revision, Lean version, report and stderr together. A successful run exits 0 and reports `sandboxed: true` and `judgement: accepted`. Check the five theorem names and the three permitted axioms against the pinned `comparator.json`. Check the statement comparison, axiom check and results for Lean default, Lean paranoid and nanoda. Comparator writes the JSON report when it finishes. [Upstream procedure](https://github.com/aliromman/riemann-hypothesis/blob/0e33c950c14ed48833fa38e401c9db04c4be5567/README.md#checking-the-proof-yourself)
