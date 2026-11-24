# Replay the five proofs after the clump marker fix

The original Linux job compiled commit `989ea9c41e8400a6fe894fe365298c219f8c7e1d`. Its successor is `be239239d08c7bf865ba618cf6515891b4596c84`. The child changes two Python files. The entire Lean source tree and every other Git path have the same content and mode.

The reviewer script checks the complete Git diff and hashes the original Linux ZIP. It reads the five archived Main outputs and the ten outputs for its two fresh imports. It replaces the old runner paths with paths to the same public objects on the reviewer's system. It hashes all 59,296 effective project inputs and compares the ordered table with the one published for the original run. It then executes the original Lean replay. The kernel must reject the deliberately wrong proof and accept each of the five genuine proofs.

Use Python 3 and the project's pinned Lean and Mathlib. Set `RH_CHECKOUT` to a repository with both Git commits, `RH_LIB` to the extracted batch 1119 project library, `ROOT_ZIP` to the original ZIP and `REVIEW_DIR` to the directory containing `replay_977_tool_successor.py`. Use absolute paths.

```sh
set -eu
curl -fsSL -o "$REVIEW_DIR/ReplayMain.lean" https://raw.githubusercontent.com/aliromman/riemann-hypothesis/90c6a9928b431666d6f565665cbc42d49a8c7285/ci/root-replay/ReplayMain.lean
cd "$RH_CHECKOUT"
lake env python3 "$REVIEW_DIR/replay_977_tool_successor.py" "$RH_CHECKOUT" "$ROOT_ZIP" "$RH_LIB" "$REVIEW_DIR/ReplayMain.lean"
```

The expected output contains the rejection of `True.intro` as a proof of the Riemann Hypothesis and one `kernel accepted` line for each target in `comparator.json`. The original ZIP is also available in the [immutable proof record](https://github.com/aliromman/riemann-hypothesis/tree/ac83ca84627e2f8fbeec57f8ea40f4fe1be15100/batch-1119/five-theorems).
