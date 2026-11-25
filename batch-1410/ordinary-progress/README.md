# Regular Lake build checkpoint

The first 54 completed groups contain 10,250 of the 59,822 project modules. The first group contains seven downstream roots and their imports. The other groups follow the dependency order. Lake built each group and accepted a second build with `--no-build`. This count includes valid cached files.

The comparison reads each original module from the community archive and checks every declaration, including private proof values, against the candidate. A separate check compares the public and both IR file hashes with the inputs used to check the five final theorems. The totals count compiler output for this workload. They do not measure whole-project compile time. [Counts and group receipts](summary.json) · [Module results](modules.jsonl.gz)
