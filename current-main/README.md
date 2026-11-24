# Source and compiled-file measurements on the integrated parent

These files compare the source of community commit `d27f71347abceb76cd37dc8a5fccbe556ec2be90` with fork commit `6c9263df4fa0de0e7719aebb952e0e44df47b421`. The source counts cover every Lean file under `src/`. The compiler file sizes cover the 40,481 edited modules. Sizes are in bytes and refer to uncompressed files.

The public file and both IR file hashes for each module were matched to real compiler outputs. Sixteen modules required new measurements when upstream merged #644. The other 40,465 had the same projected hashes as the previous source check. A separate native run recompiles the files whose elaboration inputs changed. Its results determine which proof comparisons transfer to the new parent.

The dependency report counts distinct project modules. Its transitive count includes direct importers. The source closure of `Main` includes privately imported source needed to build its dependencies. Its effective import count is the set that Lean loads when it compiles `Main`.
