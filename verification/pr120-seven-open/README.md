# Seven open shard rows at 74f1320f

The [05:52 UTC shard report](https://github.com/rohanarun/alpoge-rh-replay/blob/e9f5c45a9fd79d596c0c71fc5f8873beb4282934/PR120-BUGS.md) lists seven source lines. At the recorded head, all nine occurrences of the disputed names already spell the declarations that the Lean 4.36 compiler selected in the original release. The two root-lattice files share the same repair.

| Shard row | Original compiler selection | Commit that supplied the current line |
| --- | --- | --- |
| FoundationProofs.Bundle0295 | GlobalTheory.VacuumScalar.sd_of_moves (twice) | [maugomez77](https://github.com/rohanarun/riemann-hypothesis/commit/49e1f27896a2c63048f9a8e61e91441478c5f346) |
| SupercuspidalSupportUniqueGL | GlobalTheory.SmGL.twist | [mrshu](https://github.com/rohanarun/riemann-hypothesis/commit/0d13ce91fd7be21523f26ff8c4d58d0bd7a04874) |
| HodgeTatePoints.Bundle0058 | GlobalTheory.FrameTangent.smT_zero_ovT | [Vladimir Zhilin](https://github.com/rohanarun/riemann-hypothesis/commit/2ba21946b8ab9b68bfd321279c224f5c5c9c194c) |
| KernelLattices.ColumnData.SelfDual | Formalism.L2.Ker.Cd.TaylorLogMetric.embT | [Petyrrrrr](https://github.com/rohanarun/riemann-hypothesis/commit/6338e4ef1499cca0cffbd8952ae56c1730a73d7b) |
| DualFamilyCounting.Bundle0018 | Formalism.HermitianLattices.Ext.L3.locF (twice) | [Lev Khoroshansky](https://github.com/rohanarun/riemann-hypothesis/commit/edc94ca5ba43d79493d9f9cf397623350421a767) |
| RootLatticeThresholds.Bundle0025 and LoopsTies | Formalism.L2.SG.PackageTie2.sOf | [Nolan Andrews](https://github.com/rohanarun/riemann-hypothesis/commit/925afc9c3db8f7ae23fdaf9038ab5cc8972597b6) |

Each row in `references.json` records the bundled and original locations and the exact source spans' compiler selections. To repeat the check, use a repository that contains both revisions. Obtain the original compiler objects at `c7791603122c0328f79e49f6be5d7d4402effc53`. Alternatively, build `original-targets.txt` on an original checkout with the pinned toolchain. Set `evidence` to this directory and run the following commands.

```sh
python3 "$evidence/check_references.py" "$repo" "$original_checkout/.lake/build/lib/lean"
git -C "$current_checkout" rev-parse HEAD
cd "$current_checkout"
xargs lake build < "$evidence/targets.txt"
```

The first command checks nine occurrences in seven files. The current source checkout for the native build must be `74f1320f2e1acc6c67f74c62afa04791ac354457`. The dependency closure for these seven files has 17,853 project modules. A complete build at that revision is the test for any further errors.
