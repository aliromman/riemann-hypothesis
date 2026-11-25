# Lean source count on the 4.36 author branch

The original tree at `c7791603122c` has 149,397 tracked Lean sources under `src/`. Both the November 25 shard revision `4e9c4d24ea6a` and the later branch tip `fd6d45a2fd04` have 47,885. The reduction is 101,512 files (67.95%). With rename detection off, Git records 121,772 deleted paths and 20,260 added paths. The original blobs for `src/Challenge.lean`, `comparator.json`, `export-targets.txt` and `lean-toolchain` match on both revisions. [Reported revision](4e9c4d24.json) · [Later branch tip](fd6d45a2.json) · [Source branch at the later revision](https://github.com/rohanarun/riemann-hypothesis/tree/fd6d45a2fd048144119be695f370f04bf064d30f)

The operator reported 43,930 of 47,885 modules compiled at 17:03 UTC on November 25. The report identifies 38 open failures at `4e9c4d24ea6a`. The matrix `BorelSpace` failure in `AmplifierOfHypotheses.lean` appears at line 168. The later tip has a separate source count. A full `Main` build and the five-statement Comparator still need to pass on a proposed 4.36 merge. [Shard report](https://github.com/rohanarun/alpoge-rh-replay/blob/c306f17b4254ae74b31e770d30f782e2a28ba910/PR120-BUGS.md)

From a repository that contains the original and measured commits, run the following command. The script compares the full set of source paths and checks the result with a separate Git diff.

```sh
python3 count_current_author_files.py /path/to/checkout 4e9c4d24ea6a9e582ff8146f3f7312429ca88305 result.json
```

Three earlier revisions gave the same source counts. [b964e9b2](b964e9b2.json) · [a2f70f62](a2f70f62.json) · [93c5a5d2](93c5a5d2.json)
