# Clump planner tests and compiler diagnostics

The Linux job tested revision `963ebea3bb3d7c2c5738946fca45317b8084f972` from the fork ref `refs/heads/ci/clump-scopes/batch-1266-source`. Relative to the immediately preceding source revision `70f5e2c0737a9289949627d834612ed30d25432f`, this update changes `scripts/clump.py` and its focused tests. Ubuntu passed 314 repository script tests, 14 included clump tests and 60 native CI tests, with zero skips. It used the repository's pinned Lean 4.37.0-rc1, boto3 and botocore 1.44.9, PyYAML 6.0.2, Python 3.12 and GNU cp. [Actual job](https://github.com/aliromman/riemann-hypothesis/actions/runs/45448060512/job/138637195704)

Four stock Lake errors exercised the ordinary, pre-banner, compact-member and literal-marker legacy cases. Every compiled fixture, error line, owner list and recovered input exactly matched its earlier control. The tests compiled the new planner output and ran the real clump CLI for each case. [Fixtures and owners](diagnostic-control.json) [Original compiler and unit-test logs](ubuntu-python.zip)

The complete Lean source tree is `bd038d97d3d9f38ac0ea2eba4e4d7a8ec4cc3749`. The separate batch 1266 Linux jobs run stock Lake and the default sandbox on this source and its fixed compiler and package pins. [Original stock verification](https://github.com/aliromman/riemann-hypothesis/actions/runs/45446277703) [Original default-sandbox verification](https://github.com/aliromman/riemann-hypothesis/actions/runs/45446517890)

The original Actions ZIP has SHA-256 `f31170cbf6c6a6e9c5c60bc9d897ca5afdd93c8a6198ad63995fd59fc33f5c3c`. [Exact source and environment](verified.json)
