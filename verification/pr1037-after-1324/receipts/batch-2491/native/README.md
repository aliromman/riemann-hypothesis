# Full build of the matrix-measure change

Stock Lake built all nine default targets on `0e33c950c14ed48833fa38e401c9db04c4be5567`, including `Main`. The build and the up-to-date check each completed 137,117 jobs and exited 0. The PR head `ef7b2af7f6017c9e6875d4d8803907ac0cd8804b` has the same Git tree. The first parent is community batch #2491 at `ef451fc356cbc66861df031531aaafd2843797ac`. [Tested commit](https://github.com/aliromman/riemann-hypothesis/commit/0e33c950c14ed48833fa38e401c9db04c4be5567) · [Build and check](default.json)

The build used the pinned Lean 4.37.0-rc1 release for macOS on ARM64. It reused 45,210 verified baseline archives. The full log records 13,408 distinct modules compiled in this invocation. Smaller checks had already compiled part of the changed dependency graph. The full build has two separate logs. The receipts contain the SHA-256 of each uncompressed log. [Archive selection](restore.json) · [Full build](default-build.log.gz) · [Up-to-date check](default-check.log.gz)

A separate `lake build Main` and an up-to-date check for `Main` and all 23 modules that name the matrix providers each completed 137,041 jobs. Stock `leanchecker` replayed all five modules that use a provider directly in a term. The compiled `Main.olean` retained the same SHA-256 throughout these checks. [Caller results](callers.json) · [Source coverage](closure.json) · [Summary and Main checksum](summary.json)

## Reproduce

Use a clean checkout of the tested commit. Use the compiler in its `lean-toolchain` file. The existing build instructions show how to restore only the unchanged modules from the first parent's public cache. Set `results` to the absolute path of this receipt directory. [Cache and build scripts](../../../../pr120-successor-builds/README.md#reproduce-a-build)

```sh
lake --no-cache --rehash build
lake --no-cache --rehash build --no-build
lake --no-cache build Main
xargs lake --no-cache build --no-build Main < "$results/consumers.txt"
while IFS= read -r module; do
  lake --no-cache env leanchecker -v "$module" || exit 1
done < "$results/term-callers.txt"
```

This receipt covers the native build. The sandboxed Linux Comparator has a separate operator and report. The protected challenge produced the same export on both source revisions. [Challenge export](../challenge/receipt.json)
