# Lean file counts on the 4.36 integration branch

The table counts unique tracked files at four fixed Git revisions. The last column includes Lean files outside `src/`.

| Source tree | Lean files in `src/` | All tracked Lean files |
| --- | ---: | ---: |
| Original 4.36 base `c779160312` | 149,397 | 149,406 |
| First reported #120 head `f941065836` | 47,882 | 47,891 |
| Community main after #591, `c827d9fe32` | 60,790 | 60,804 |
| Author 4.36 integration, `7b6f4b929c` | 47,884 | 47,893 |

The author branch removes 101,513 Lean source files from the 4.36 base. The physical source count differs by 12,906 from main, which already contains #324 and #438. Across the entire repository, the difference from main is 12,911 Lean files. These figures compare the named Git trees. A regenerated merge candidate needs its own comparison, build, and protected-statement checks.

Run the command in a repository containing all four commits.

```sh
python3 measure_layout.py --repo . c7791603122c0328f79e49f6be5d7d4402effc53 f94106583626ad6b48ac6e239e0b2e5ffc879555 c827d9fe3249dbd50b6bb82c948fcae88cfff583 7b6f4b929c2857ac175c35b21382022b7ac6f752
```

The program reads NUL-delimited Git trees and cross-checks the path additions and deletions with a second Git command. Its JSON records the revision, the pinned toolchain, and the blob IDs for the challenge, statements, export target list, and Comparator configuration. All four protected input blobs match across these four revisions. Compiling `Main` and checking the exported proof in the two independent kernels are separate requirements. [Maintainer review](https://github.com/leanprover-community/riemann-hypothesis/pull/120#pullrequestreview-6029894503) · [Host and verification procedure](https://github.com/leanprover-community/riemann-hypothesis/pull/120#issuecomment-7089960595).
