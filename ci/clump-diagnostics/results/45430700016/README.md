# Community tests and compiler diagnostics for PR #977

Ubuntu 24.04 tested author revision `c0228c0ae22d9cbf3e5466760718fd19111058ac` after the community's batch #1198. All 313 tests in `scripts/tests` passed. The separate clump run passed all 13 of its tests, which are included in those 313. All 60 tests in `tools/ci_native` passed. No test was skipped. The job used Python 3.12.16, GNU cp 9.4, PyYAML 6.0.2, the repository boto3 and botocore 1.44.9 pins, and Lean 4.37.0-rc1. [Original Ubuntu job](https://github.com/aliromman/riemann-hypothesis/actions/runs/45430700016/job/138574895166)

The new parent changed three community test modules and their supporting scripts. Four real pinned Lake builds also reproduced deliberate type errors in the diagnostic fixtures. The clump tool gave no archive owner for the ordinary-file or pre-banner errors. It returned `Examples.Leaf` for the compact-member and legacy-literal cases. The original source files were restored byte for byte in every case. The recorded previous blame implementations and the equal Darwin fixtures give independent controls. [Sources, diagnostic lines and every owner](diagnostic-control.json)

The original Actions ZIP has SHA-256 `0706a34540ebf3d1962400789eecb3d51f0ae99f898b671ca56bbf24c7afa0fa`. [Original logs](ubuntu-python.zip) [Source and test counts](verified.json)
