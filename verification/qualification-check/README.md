# Check Lean 4.36 name qualifications

A global declaration can be reachable from the original module while the proof uses a local hypothesis with the same name. A bundle can also expose an unrelated constant to a theorem that still compiles. Use the original Lean compiler record to check the declaration at each changed source position.

## Check a proposed mechanical edit

Use Git, Python 3.9 or later, and the pinned Lean 4.36.0 environment. The original checkout must contain the pre-consolidation sources at `c7791603122c0328f79e49f6be5d7d4402effc53`. Set `repo` to a repository that contains that commit and the proposed commits. Set `original` to a separate clean checkout of the original commit. Set `check` to this script. These commands show the check for the original commit of author PR #631.

```sh
base=c7791603122c0328f79e49f6be5d7d4402effc53
change=92535fb9abaca2d6a72e11c2bd66d3ec0eb50d4e
python3 "$check" --repo "$repo" --original "$base" --list-members "$change^" "$change" > members.txt &&
  (cd "$original" && xargs lake build) < members.txt &&
  python3 "$check" --repo "$repo" --original "$base" --ilean-dir "$original/.lake/build/lib/lean" "$change^" "$change"
```

The script reads the tracked sources at the three requested revisions. It locates each original bundle member, matches the source line, and reads the constant at that token's exact UTF-16 span in the original `.ilean`. Repeated lines need a unique match from adjacent source lines. Use editor data from the exact original build. The script checks the module identity and expects the Lean 4.36 editor format.

Exit 0 means each changed token on the supplied diff is an absolute qualification of the same recorded constant. A changed header, another kind of edit, an ambiguous source line, a missing compiler record, or a different constant requires manual review and gives exit 1. Each output row gives the source position and original name when available. This check applies to pure qualification commits. It does not check instance search, proof bodies, changes at other sites, or the five protected statements. Compile the candidate and run the integration checks separately.

| Author PR | Matches | Needs review | Observed result |
| --- | ---: | ---: | --- |
| #625 | 20 | 2 | One local `hval`, one different `secPull` constant. The two spellings of `secPull` each compile in the original proof. |
| #626 | 40 | 1 | One local `hval`. |
| #631 | 15 | 1 | One local `hs`. |
| #635 | 51 | 0 | All 51 restored names agree with the original compiler. |
| #649 | 21 | 0 | All 21 restored unitary-group names agree with the original compiler. |

The JSON-lines receipts include every changed token in the five commits. The summary files give the full Git identities. An item that needs review is not by itself a build failure. [Two local theta equalities](https://github.com/rohanarun/riemann-hypothesis/pull/680) · [Local rank-one equality](https://github.com/rohanarun/riemann-hypothesis/pull/648) · [Remaining unitary-group names](https://github.com/rohanarun/riemann-hypothesis/pull/649).

## Replay the three failing substitutions

Run this in the clean original checkout. Set `replay` to the absolute path of `replay_local_proofs.py`.

```sh
lake build Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableUnipotentRankOne Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowGeneratorEqConstMulVacuumTheta Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstOrtho
lake env python3 "$replay" --repo .
```

Each original proof compiles. Changing only the local use to the proposed global name gives one unsolved goal in the rank-one proof and two errors in each theta proof. The replay checks the expected return codes and diagnostic counts. It writes each result to standard output. See `native-local-proofs.jsonl`.

## Replay the five arithmetic proofs

The same check accepts a repair that replaces an incorrect qualification with the absolute name from the original compiler. All 13 changes in [author PR #705](https://github.com/rohanarun/riemann-hypothesis/pull/705) match. Five complete source controls compiled with their original spelling and with the repaired spelling. The branch spelling gave nine diagnostics across the five proofs. The 15 compiled input hashes and diagnostics are in `native-typed-maps.jsonl`.

Set `tools` to this directory. Set `controls` to an empty directory on the same machine. Use absolute paths for both. Run these commands in the clean original checkout with its pinned dependencies.

```sh
base=c7791603122c0328f79e49f6be5d7d4402effc53
python3 "$tools/make_name_controls.py" --repo . --original "$base" --receipt "$tools/typed-maps.jsonl" --output "$controls"
python3 -c 'import json,sys; print("\n".join(sorted({r["member"] for r in map(json.loads,open(sys.argv[1]))})))' "$tools/typed-maps.jsonl" > "$controls/members.txt"
xargs lake build < "$controls/members.txt"
for arm in original previous restored; do
  while IFS= read -r module; do
    path=$(printf '%s' "$module" | tr . /)
    lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 -DmaxHeartbeats=4000000 --root="$controls/$arm" "$controls/$arm/$path.lean"
  done < "$controls/members.txt"
done
```

The constructor uses the original UTF-16 source span and writes three complete files per module. Its 15 output hashes match the inputs used for the native controls. The `previous` arm must fail in each module. These results concern the source occurrences identified in the receipt. The physical consolidated modules also need to compile with their integrated dependencies.

The native totals include diagnostic names such as `error(lean.unknownIdentifier)`. This corrects the initial total of eight for #705. The original and repaired arms each had zero.
