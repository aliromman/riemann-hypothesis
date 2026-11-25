# Lean source count on the 4.36 author branch

The original `c7791603122c` tree has 149,397 Lean sources under `src/`. The `b964e9b2e15a`, `a2f70f62b6e4` and `93c5a5d23cc5` trees have 47,885. The net reduction is 101,512 files (67.95%). Git records 121,772 deleted paths and 20,260 added paths with rename detection off. The original Git blobs for `src/Challenge.lean`, `comparator.json`, `export-targets.txt` and `lean-toolchain` match each measured revision. [Author source](https://github.com/rohanarun/riemann-hypothesis/tree/93c5a5d23cc5d8adab1fa24d6f6d317eb9207646)

From a repository that contains both commits, run the following command. The script reads the two Git trees and checks the added and deleted paths with `git diff`. It writes the four protected blob IDs to the result.

```sh
python3 count_current_author_files.py /path/to/checkout 93c5a5d23cc5d8adab1fa24d6f6d317eb9207646 result.json
```

The operator reported 41,991 of 47,885 modules compiled at `93c5a5d23c` at 03:39 UTC on November 25. The board lists 30 open root failures and 13 other files that changed since their reported errors. Those 13 await a rebuild. A complete `Main` build and the official five-statement Comparator are still required on the proposed merge revision. [Operator report](https://github.com/rohanarun/alpoge-rh-replay/blob/989fdd6d6a26a5277930c94344471dbd73c035f7/PR120-BUGS.md)
