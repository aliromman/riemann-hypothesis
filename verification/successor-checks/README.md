# Build the batch #1801 successor targets

Use an empty project checkout with Git, Python 3.11 or later, and elan on the path. The script restores published project archives by SHA-256. It checks the complete project import graph on both source revisions. It builds the parent first, then rebuilds each changed module and its affected dependents in the selected cone. It checks the listed callers with the Lean kernel.

```sh
git clone --depth 1 --branch codex/rh-successor-target-checks \
  https://github.com/aliromman/riemann-hypothesis.git harness
git init project
cd project
git fetch --depth 1 https://github.com/leanprover-community/riemann-hypothesis.git \
  c40250a50104b7e02e7d74f658d00fa7b1f4827c
git checkout --detach FETCH_HEAD
elan toolchain install "$(cat lean-toolchain)"
export LEAN_NUM_THREADS=3 LEAN_ABORT_ON_PANIC=1 MATHLIB_NO_CACHE_ON_UPDATE=1
checks=../harness/verification/successor-checks
python3 "$checks/verify_targets.py" "$checks/plan.json" matrix
```

Choose one group per fresh checkout. The `matrix` group builds 36 targets over 3,341 project modules. The `admloc` group builds seven targets over 11,977 project modules. It includes all five files in #911, the Satake caller and the intended `ResBound` caller. The `cleanup` group builds 29 targets over 17,377 project modules. It includes all 28 edited sources. Save the `RH_TARGET_SIDE` and `RH_TARGET_RESULT` lines and the exit status. Each group checks three named modules with the kernel. Full `Main` and Comparator results require separate runs.
