# Matrix instance checks after batch #2787

The published #1037 head, `ef7b2af7f6017c9e6875d4d8803907ac0cd8804b`, merges cleanly with community main `251c7b05dd869ceba1aa42c6001c00b4010f23f9`. Git produced tree `55bdb75c3f61fa939dad5687193658fe2095f98a`. Its four changed files contain 12 additions and 8 deletions. The batch changed none of those four files or the protected inputs. Both sides contain 59,364 Lean files under `src/`. The separate full verification on the preceding batch uses merge commit `0e33c950c14ed48833fa38e401c9db04c4be5567`. [Git comparison](merge.json) · [Previous checks](../batch-2491/README.md)

| Lean 4.37.0-rc1 check | Current main | Current main with #1037 |
| --- | --- | --- |
| Full `LinUnit.eq_zero_of_ip_eq_zero` proof in each provider order with the GL scope open and closed | 2 errors in each of 4 cases | All 4 pass |
| Three named matrix instances compared with Mathlib's instance by reducible `rfl` | 3 errors | All 3 pass |
| Two named scoped GL instances | Both selected | Both selected |
| Kernel replay of `EqZeroOfIpEqZero` and `GJFEInducedLevi` | Both pass | Both pass |
| Archived `localZ_map` proof fragment in both provider orders | Both pass | Both pass |

Three sources changed in the 311-module test. Stock Lake compiled 23 modules per side. Both up-to-date checks passed. The one explicit matrix caller changed elsewhere in the batch was `RegConstEqAwayUnitMulFactor`. Its single edited line calls the target of a removed forwarding theorem directly. The matrix instance command is unchanged. [Five-target build](builds.json) · [Scope closed](closed.json) · [Scope open](open.json) · [Caller and provider checks](callers.json) · [Doubling fragment](doubling.json) · [Forwarding theorem removal](https://github.com/leanprover-community/riemann-hypothesis/commit/05d406f113e438b37f132ddc2b59bbd5c0e01013)

## Reproduce

Fetch the two parent commits in a Git clone. The following commands name the exact test tree. A local merge commit gives the tree a revision that can be checked out.

```sh
base=251c7b05dd869ceba1aa42c6001c00b4010f23f9
head=ef7b2af7f6017c9e6875d4d8803907ac0cd8804b
tree=$(git merge-tree --write-tree "$base" "$head")
test "$tree" = 55bdb75c3f61fa939dad5687193658fe2095f98a
candidate=$(git commit-tree "$tree" -p "$base" -p "$head" -m 'Check the matrix changes on batch 17')
```

Use a checkout of `$base` for `BEFORE` and a checkout of `$candidate` for `AFTER`. Build the five targets and run both scope probes and the two caller replays as in the earlier instructions. To replay the two orders for the archived proof fragment, use the last command below. [Five-target commands](../batch-2318/README.md#reproduce)

```sh
python3 "$EVIDENCE/replay_doubling.py" --repo "$REPO" --before "$BEFORE" \
  --after "$AFTER" --bin "$BIN" --output "$OUT/doubling"
```

The compressed Lake logs expand to the SHA-256 digests in the build receipt. The earlier batch receipt contains the comparison for the complete archived doubling proof. [Full historical proof](../batch-2491/doubling.json)
