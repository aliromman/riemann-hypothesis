# Changed theta caller on batch #2787

The complete `RegConstEqAwayUnitMulFactor` module compiled on both revisions. Its stock kernel replay passed on each. The caller imports 9,756 project modules. Batch #2787 changed its proof at line 1536. Its explicit matrix-instance command at line 371 stayed in place. [Baseline](https://github.com/leanprover-community/riemann-hypothesis/commit/251c7b05dd869ceba1aa42c6001c00b4010f23f9) · [Merge with #1037](https://github.com/aliromman/riemann-hypothesis/commit/0f6a46608035dae6e767ce73dc11da996fa1a240)

Each stock Lake build and up-to-date check completed 31,556 jobs. On the baseline, Lake compiled the caller from source after restoring its 9,755 dependencies. Its public `.olean` is byte-identical to the baseline CI archive. On the merge, 2,090 modules depend on the four PR edits. Eleven had already been checked on this revision. Lake compiled the other 2,079, including the caller. [Build and kernel receipts](receipt.json) · [Comparison with the CI artifact](baseline-artifact.json)

The first candidate invocation compiled 2,008 distinct modules before an interruption. Stock Lake resumed from those files and compiled 71 more. A separate kernel attempt stopped when the host reached its open-file limit. The isolated retry replayed the same compiled caller and exited 0. [First build segment](candidate-interrupted.log.gz) · [Completed build](candidate-build.log.gz) · [Kernel log](candidate-kernel.log.gz)

## Reproduce

Use separate clean checkouts of the two commits above with pinned Lean 4.37.0-rc1. Set `before` and `after` to their paths and `results` to the absolute path of this directory.

```sh
target=$(cat "$results/target.txt")
for tree in "$before" "$after"; do
  (
    cd "$tree" &&
    lake --no-cache --rehash build "$target" &&
    lake --no-cache --rehash build --no-build "$target" &&
    lake --no-cache env leanchecker -v "$target"
  ) || exit 1
done
```
