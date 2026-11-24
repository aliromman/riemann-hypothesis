# Compiler results for the remaining unitary-group references

The Lean 4.36 compiler resolves all 21 references from [author PR #649](https://github.com/rohanarun/riemann-hypothesis/pull/649) to their original constants on `965d3f0aa89d57ce85de56207bea4d785e37c896`. This commit includes TmLev's [#631](https://github.com/rohanarun/riemann-hypothesis/pull/631) and [#635](https://github.com/rohanarun/riemann-hypothesis/pull/635), Ali's [#648](https://github.com/rohanarun/riemann-hypothesis/pull/648) and #649, and mrshu's [#792](https://github.com/rohanarun/riemann-hypothesis/pull/792).

| Revision | Four physical targets |
| --- | --- |
| `b2c5a15e74d12f88d5b4a4cb3603c3fb0a4f33b5` | Two build with twelve incorrect resolutions. A separate dependency gives three errors. The rank-one proof gives one error. |
| `06f623ee16c15a745990f46c204eff9064ba4fe7` | The same twelve resolutions are correct. The separate dependency still blocks the other nine sites. |
| `46128e89b5e4a68fc9f32b0f673e3fb0493100b0` | The rank-one target passes with 27,051 Lake jobs and passes kernel replay. It exports fifty axiom records. |
| `965d3f0aa89d57ce85de56207bea4d785e37c896` | All four build. There are 12,897 project source files and 44,043 Lake jobs. All 21 selections match the historical records. Four native kernel replays pass. All 149 exported axiom records use permitted axioms. |

To repeat the combined check, keep this evidence directory outside the source checkout. Use the author's repository at the last revision in the table. Set `evidence` to the absolute path of this directory. Run these commands in the source checkout with the pinned Lean 4.36 toolchain and Mathlib cache.

```sh
xargs lake build < "$evidence/targets.txt"
python3 "$evidence/check_bindings.py" . "$evidence/joint-bindings.tsv"
PR120_REPLAY_LIST="$evidence/targets.txt" lake env lean "$evidence/../pr120-shard-roots/ReplayOriginalKernel.lean"
sed 's|\.|/|g;s|^|.lake/build/lib/lean/|;s|$|.olean|' "$evidence/targets.txt" | xargs lake env lean --run "$evidence/CheckAxioms.lean"
```

The editor data records the constant that Lean selected at each source span. The original compiler data comes from source tree `69b331ce0e429c7632dac6aa642e5875a50b1218`. The earlier [134-site comparison](../qualification-check/) covers the entire unitary-group qualification change. These four targets are part of the final proof build. The full `Main` and Comparator checks need a separate result.
