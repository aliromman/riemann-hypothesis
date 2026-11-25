# Lean source count on the 4.36 author branch

The original `c7791603122c` tree has 149,397 Lean sources under `src/`. Both `b964e9b2e15a` and `a2f70f62b6e4` have 47,885. The net reduction is 101,512 files (67.95%). Git records 121,772 deleted paths and 20,260 added paths with rename detection off. The original Git blobs for `src/Challenge.lean`, `comparator.json`, `export-targets.txt` and `lean-toolchain` match each measured revision. [Author source](https://github.com/rohanarun/riemann-hypothesis/tree/a2f70f62b6e42d57697e7ab53a476ede276e78f6)

From a repository that contains both commits, run the following command. The script reads the two Git trees and checks the added and deleted paths with `git diff`. It writes the four protected blob IDs to the result.

```sh
python3 count_current_author_files.py /path/to/checkout a2f70f62b6e42d57697e7ab53a476ede276e78f6 result.json
```

The shard report on `b964e9b2e1` recorded 41,905 of 47,885 modules compiled and 43 listed root failures at 03:04 UTC on November 25. A complete `Main` build and the official five-statement Comparator are still required on the proposed merge revision. [Operator report](https://github.com/rohanarun/alpoge-rh-replay/blob/4b877bb5c82744a6f5a0452a8fbd9a9e3973c458/PR120-BUGS.md)
