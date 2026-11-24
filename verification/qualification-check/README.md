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

## Theta doubling function

[Author PR #452](https://github.com/rohanarun/riemann-hypothesis/pull/452) added 26 explicit names to resolve a tactic ambiguity. Seven sites need the generic function `GlobalTheory.ThK.Dbl.flat`. The editor data from Lean 4.36 records this function at every site. Each uses the specialized `GlobalTheory.Doubling.flat` at parent `696a2f9d37a216fb63eed77543a4d57a8878fb5d`. All seven are in the five files changed by `322a074332d984449c116c89dc715e22b50c3b61`.

The six complete original modules compile with both providers in scope. Every module fails when it uses the specialized function in place of the original. The six modules give seven native diagnostics in total. All six compile when they use the absolute name of the original function. Read `theta-flat-references.jsonl` for the seven original source positions and `theta-flat-native.jsonl` for all 18 runs.

To reproduce the controls, use the same original 4.36 checkout and `tools` and `controls` paths as above. Build the six original modules and the additional import before running Lean. Run the three arms with the Lean command above. The option adds the same provider to every arm.

```sh
python3 "$tools/make_name_controls.py" --repo . --original c7791603122c0328f79e49f6be5d7d4402effc53 --receipt "$tools/theta-flat-references.jsonl" --extra-public-import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing --output "$controls"
python3 -c 'import json,sys; print("\n".join(sorted({r["member"] for r in map(json.loads, open(sys.argv[1]))})))' "$tools/theta-flat-references.jsonl" > "$controls/members.txt"
lake build Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
xargs lake build < "$controls/members.txt"
```

## Structure field assignments

Lean records the projection name for a structure field label. Changing the label `twist :=` to a fully qualified projection still makes the assignment invalid. With both providers imported, each of the two complete original modules accepts its bare label. Each reports two errors with the external name and two with the absolute name of the original projection. [Restored fields](https://github.com/rohanarun/riemann-hypothesis/pull/722) · [Sibling repair](https://github.com/rohanarun/riemann-hypothesis/pull/707).

The checker now sends a changed name that precedes `:=` to manual review, including across nested comments and line breaks. Valid terms can also occur in that position, for example at the end of a proposition just before its proof. Use a native compile for these edits. The rule catches both known field-label errors. All seven earlier qualification diffs retain their verdicts across 171 sites.

Run the commands below from the original 4.36 checkout. The test builds a temporary Git fixture from the two original files. It checks the actual compiler spans for the two field labels.

```sh
lake build Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecOfRecLiteral
python3 "$tools/field_label_controls.py" --repo "$PWD" --ilean-dir "$PWD/.lake/build/lib/lean" --checker "$tools/check_qualifications.py"
```

## Automorphic lift premise and gauge-lattice rewrite

The original 4.36 compiler records `UpperTheory.Esk.H0` as the premise of `lift` in `PfHolWC`. The name `ReciprocityTheory.Gal.H0` produces a type error at the premise. Two more errors follow when a proof calls the missing `lift`. In `SlabNDensePf`, the matrix rewrite uses `Formalism.L2.SG.Pf.SlabNDensePf.gE`. It fails with `Formalism.MainNotions.S.gE`.

Both providers were in scope in each arm. The original, integration, and repaired spellings gave 0, 3, and 0 diagnostics in the complete lift module. The counts were 0, 1, and 0 in the complete lattice module. The import closures had 19,876 and 1,153 original project modules. Each per-member receipt contains the original compiler span. `lift-gauge-native.jsonl` contains all six input hashes and diagnostics. The source constructor reproduces all six hashes.

Use the clean original 4.36 checkout at `c7791603122c0328f79e49f6be5d7d4402effc53`. Set `tools` and `controls` to absolute paths as above. Build both providers and both original modules. Run the three arms with the Lean command in “Replay the five arithmetic proofs.”

```sh
base=c7791603122c0328f79e49f6be5d7d4402effc53
for pair in 'PfHolWC ReciprocityTheory.GaloisValuations.SeparatedDvrSecondCohomologyMem' 'SlabNDensePf Formalism.SharpRestriction.CuspSpanNormBounds.StandingNumericalData'; do
  set -- $pair
  python3 "$tools/make_name_controls.py" --repo . --original "$base" --receipt "$tools/$1.jsonl" --extra-public-import "$2" --output "$controls"
  lake build "$2"
done
cat "$tools/PfHolWC.jsonl" "$tools/SlabNDensePf.jsonl" | python3 -c 'import json,sys; print("\n".join(r["member"] for r in map(json.loads,sys.stdin)))' > "$controls/members.txt"
xargs lake build < "$controls/members.txt"
```

## Namespace selections

Use `--check-syntax` before applying an automatic qualification. This mode asks Lean 4.36 to elaborate each changed original module and reads its syntax tree. It checks names in selective `open`, `export`, `hiding`, and both sides of `renaming`. This also covers a local `open` in a term or tactic. A namespace resolves its selected names relative to itself. The editor file can record the same constant for a relative selection and an ordinary term. Changing both to the absolute spelling breaks the selection.

Mrshu first restored the two relative `fibre` selections in OrbitLimits. A later qualification pass reintroduced them. Maugomez77 repaired them with the imports they need. Roy7 found the corresponding `logNorm_ofWeight_one` selection in `ChartDensityIntegrable`. The original, absolute and restored spellings give 0, 16 and 0 diagnostics in `PSegreChartIntegral`, 0, 12 and 0 in `PPtsIntegralProjIndep`, and 0, 8 and 0 in `ChartDensityIntegrable`. Restoring the relative spelling reproduces the original bytes in these controls. The three original import closures contain 580 distinct project modules. [First OrbitLimits repair](https://github.com/rohanarun/riemann-hypothesis/pull/679) · [Later qualification](https://github.com/rohanarun/riemann-hypothesis/pull/759) · [OrbitLimits repair](https://github.com/rohanarun/riemann-hypothesis/pull/785) · [ChartDensityIntegrable repair](https://github.com/rohanarun/riemann-hypothesis/pull/790).

Build the three original modules at `c7791603122c0328f79e49f6be5d7d4402effc53`. Set `tools` to the absolute path of this directory. Run the test from the pinned original checkout.

```sh
lake build Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartDensityIntegrable GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartIntegral GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsIntegralProjIndep
lake env python3 "$tools/selector_controls.py" --repo . --ilean-dir "$PWD/.lake/build/lib/lean"
```

The test generates a five-edit Git fixture. The editor records match at all five sites. Syntax checking flags the three namespace entries and accepts the two uses in a rewrite. The checker sends a module to manual review if its original source cannot elaborate. Run qualification checks from the same environment with `lake env python3 "$tools/check_qualifications.py" --check-syntax` and the usual Git and editor-data arguments. See `selector-control-results.jsonl` and `selector-native.json` for the compiler positions and diagnostics.
