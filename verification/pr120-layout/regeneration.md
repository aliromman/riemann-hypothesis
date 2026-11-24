# File reduction and merge conflicts at two fixed revisions

The 4.36 integration at `965d3f0aa89d57ce85de56207bea4d785e37c896` contains 47,885 tracked Lean sources in `src/`. Its original 4.36 base has 149,397. The branch removes 101,512 files (67.9478%). The community merged [James Shore's duplicate removal](https://github.com/leanprover-community/riemann-hypothesis/pull/295) at `a28ad7ec8b9f5ff4ec448fe210d3ac57aacfffe1`. That 4.37.0-rc1 tree has 60,932 Lean sources. The two trees differ by 13,047 files (21.4124%). Recount after regeneration on the agreed merge base.

A normal Git trial merge reports 62,721 conflicting paths, of which 62,717 are under `src/`. The stage sets show 43,247 paths that main modified and the integration deleted, 7,561 in the opposite direction, 11,912 that both modified, and one that both added. Two merge runs produced the same tree and set of conflict paths. Git emitted no warnings. A source-line search found a direct whole-library `import Mathlib` in 86 files on main and in 32,681 on the integration. The search includes import modifiers and trailing line comments. These counts describe source lines only. Restore the narrowed imports when regenerating the candidate. [Requested changes](https://github.com/leanprover-community/riemann-hypothesis/pull/120#pullrequestreview-6029894503) · [Author's integration plan](https://github.com/rohanarun/alpoge-rh-replay/issues/35028#issuecomment-7116981839).

Run both commands from a clone containing the four revisions. The merge uses a temporary Git object directory. The layout check compares NUL-delimited tree paths with an independent name-status diff. `counts-965d.json` records the toolchain and protected-input blob IDs. All four revisions have identical challenge, statement, export-list, and Comparator configuration files. The full build and proof exports must still pass on the proposed merge revision.

```sh
base=c7791603122c0328f79e49f6be5d7d4402effc53
initial=f94106583626ad6b48ac6e239e0b2e5ffc879555
main=a28ad7ec8b9f5ff4ec448fe210d3ac57aacfffe1
candidate=965d3f0aa89d57ce85de56207bea4d785e37c896
python3 measure_layout.py --repo . "$base" "$initial" "$main" "$candidate"
python3 merge_measurement.py --repo . "$main" "$candidate"
```
