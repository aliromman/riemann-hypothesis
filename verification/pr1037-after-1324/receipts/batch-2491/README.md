# Matrix and theta checks after batch #2491

The proposed merge of community PR #1037 is `0e33c950c14ed48833fa38e401c9db04c4be5567`. Its parents are main `ef451fc356cbc66861df031531aaafd2843797ac` and PR head `ef7b2af7f6017c9e6875d4d8803907ac0cd8804b`. The head and merge share tree `5aaf227d22e4db7fc59dd9ae4d279fed43eecfa6`. These tests use the pinned Lean 4.37.0-rc1. [Git inputs](identity.json) · [PR](https://github.com/leanprover-community/riemann-hypothesis/pull/1037)

| Check | Main | Proposed merge |
| --- | --- | --- |
| Full `LinUnit.eq_zero_of_ip_eq_zero` proof with the two provider orders, with the GL scope open and closed | 2 errors in each of 4 cases | All 4 pass |
| Reducible equality of each named matrix instance with Mathlib's instance | 3 errors | All 3 pass |
| Selection of the two named scoped GL instances | Both pass | Both pass |
| Native kernel replay of `EqZeroOfIpEqZero` and the GL caller `GJFEInducedLevi` | Both pass | Both pass |
| Archived `localZ_map` expression in both provider orders | Both pass | Both pass |
| Complete archived doubling proof in both provider orders and with the original import widening | All 3 pass | All 3 pass |

Daniel Ang's #1324 already covers the doubling regression. The matrix-provider change fixes the separate failure in `LinUnit.eq_zero_of_ip_eq_zero`. The five live regression targets depend on 311 project modules. Lake compiled 124 on each side. The archived test uses 795 project modules. It restores the original body of the retired `glR_open` forwarding theorem in its test setup. Commit `090c5c30324b439603c39094fa35ca911cbd25b0` removed this unused name from main. The archived target proof body matches its source byte for byte. [Scope closed](closed.json) · [Scope open](open.json) · [Callers](callers.json) · [Archived proof](doubling.json) · [Archived build](doubling-build.json)

The two current theta targets `ThetaKernels.IndepDomK` and `ThetaKernels.SiegelWeilKfpDefs` built on the proposed merge. The up-to-date check passed with 23,476 Lake jobs. [Target receipt](theta.json) · [Failure and correction on the preceding batch](../fc-conj-k/README.md)

The stock `Challenge` build and five-statement export passed on both revisions. The two exports have the same 363,237,517 bytes and SHA-256 `bb37c4bb518fe68a13f12aa3929dd62dfecb663f0c063ad8c338e39601f28a60`. The receipt covers the challenge side of Comparator. [Challenge inputs and results](challenge/receipt.json) · [Export check](../../verify_challenge_export.py)

## Reproduce

Use checkouts of the main and proposed merge revisions above as `BEFORE` and `AFTER`. Set `REPO` to a checkout that contains archived commit `cb4dc6e23a6187db392c96664295415c55b6b01e`. Set `BIN` to the pinned Lean toolchain's bin directory, `EVIDENCE` to the absolute path of `verification/pr1037-after-1324`, and `OUT` to a directory for the test results. Install the dependencies in each checkout's `lake-manifest.json`. The upstream README gives the Mathlib cache command. [Upstream instructions](https://github.com/leanprover-community/riemann-hypothesis/blob/0e33c950c14ed48833fa38e401c9db04c4be5567/README.md#checking-the-proof-yourself)

```sh
export PATH="$BIN:$PATH"
export LAKE_ARTIFACT_CACHE=false
for project in "$BEFORE" "$AFTER"; do
  (cd "$project" && xargs lake --no-cache --rehash build \
    < "$EVIDENCE/receipts/batch-2491/doubling-targets.txt") || exit 1
  (cd "$project" && xargs lake --no-cache --rehash build --no-build \
    < "$EVIDENCE/receipts/batch-2491/doubling-targets.txt") || exit 1
  (cd "$project" && lake --no-cache --rehash build \
    Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfIpEqZero \
    GroundTheory.AutomorphicForms.GL2.GJMatrixCoord \
    GroundTheory.AutomorphicForms.GL2.GJFEInducedLevi) || exit 1
done
python3 "$EVIDENCE/replay_matrix_selection.py" --before "$BEFORE" --after "$AFTER" \
  --bin "$BIN" --output "$OUT/closed"
python3 "$EVIDENCE/replay_matrix_selection.py" --before "$BEFORE" --after "$AFTER" \
  --bin "$BIN" --open-double-coset-scope --output "$OUT/open"
python3 "$EVIDENCE/replay_matrix_callers.py" --before "$BEFORE" --after "$AFTER" \
  --bin "$BIN" --output "$OUT/callers"
python3 "$EVIDENCE/replay_doubling.py" --full --repo "$REPO" --before "$BEFORE" \
  --after "$AFTER" --bin "$BIN" --output "$OUT/doubling"
(cd "$AFTER" && lake --no-cache --rehash build \
  Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.IndepDomK \
  Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpDefs)
```

The build receipts record the native inputs and checks on both sides. The compressed logs expand to the SHA-256 digests in the receipts. [Five live targets](builds.json) · [Archived prerequisites](doubling-build.json)
