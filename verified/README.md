# Current private-import comparison

The community parent is `cb4dc6e23a6187db392c96664295415c55b6b01e`. The proposal is `c2c7fc890448cf0c8eab464f115e5e370129697a`. The coordination review restored the original header in the diagonal trace formula and 21 headers in the Siegel–Weil proof. The other module bodies retain the earlier proposal. [Shared trace formula](https://github.com/leanprover-community/riemann-hypothesis/pull/1010) · [Siegel–Weil proof migration](https://github.com/leanprover-community/riemann-hypothesis/pull/798)

Run this command in a checkout that contains the two commits and the current community clump reader. Set `evidence` to a checkout of this evidence branch.

```sh
python3 "$evidence/audit_source.py" cb4dc6e23a6187db392c96664295415c55b6b01e c2c7fc890448cf0c8eab464f115e5e370129697a \
  --targets "$evidence/targets.txt" --extra "$evidence/verified/extra-imports.json" --unclump > source-counts.json
cmp "$evidence/verified/source-counts.json" source-counts.json
```

The source comparison reads all 60,630 Lean files under `src`. It checks the commands that changed, the order of the surviving imports and the complete bytes after every changed header. The stock clump reader recovers the same 58,990 member sources from the 9,281 affected clumps. The 39,137 changed files lose 1,019,288 private imports and gain 382 specific imports from eight modules. Both the physical and nonblank line counts fall by 1,018,906.

Each row in `pairs.jsonl.gz` identifies the project module, the two Git blob IDs, the two complete source SHA-256 values and the numbers of removed and added imports. The dependency table counts the untouched direct and transitive importers. The declaration table identifies 882,106 occurrences from the authenticated parent. These include 744,640 theorem occurrences. Some private declaration names occur in more than one module. This gives 866,001 distinct typed Lean names, including 728,535 distinct theorem names.

The stock Linux timing sample and its independent theorem exports cover the same exact 143-module dependency closure on this head. All 715 relevant parent artifact hashes match. The whole-project default-target Lake build and full independent five-theorem Comparator export remain outstanding. [Stock Linux observations and public revision transfer](https://github.com/aliromman/riemann-hypothesis/tree/eb4fe9d9c9cb672237955b3fb3b000975d1e9b4d/ci/stock-batch-896/results/45370408013/)

## Native records and compiled bytes

Each of the 39,137 changed modules has either a fresh current-parent comparison (29,187) or a prior comparison with identical owner source and effective compiler inputs (9,950). These cover 882,106 module-local declarations. Every normalized warning multiset agrees. Their 117,411 raw public-module, IR-body and IR-signature SHA-256 values match a stock Lean serialization of the original module with only its actual, Git-confirmed direct-import header changed. The total reduction across those three compiled facets is 380,813,352 bytes. The public module files fell from 6,659,016,984 to 6,471,202,656 bytes. IR bodies fell from 500,667,672 to 307,668,648 bytes and the signatures occupied 9,705,976 bytes on each side. The bounded stock sample recorded increases of 1,104 bytes in the server files and 20,168 bytes in the private files across its 94 changed modules. A total for those two facets across the full proposal was not measured. [Native jobs](https://github.com/aliromman/riemann-hypothesis/actions/runs/45365901389)

Both batches #1018 and #1025, the proof-name cleanup #1021 and the revised Siegel–Weil proof #798 merge cleanly in the recorded Git tests. These are Git integration checks. A merge that changes a proof or compiler input needs its own mathematical verification. The two proposed PRs compose exactly across all 9,179 shared source paths. [Peer merge trees](peer-merges.json) · [Composition with the clump refactor](composition.json)

## Five final theorems

The exact published head `c2c7fc890448cf0c8eab464f115e5e370129697a` and source tree `4a04249b1ba74ed4740591a6d864145ab47c187d` were used for this run. Lean re-elaborated `Main` with all 59,901 effective public project inputs. It compared the five theorem types and proof values with the authenticated parent. All five matched, and Lean's kernel accepted all five proofs at trust level zero. A control that supplied a proof of `True` for the Riemann Hypothesis failed. Every theorem used exactly `propext`, `Quot.sound` and `Classical.choice`. The public, server and private `Main` file bytes matched the parent's files. The independent frozen challenge export had the expected SHA-256 and length of 363,237,517 bytes. The full independent solution export remains the maintainers' separate check. [Five-theorem job](https://github.com/aliromman/riemann-hypothesis/actions/runs/45382775628) · [Original kernel log](five-theorems/replay.log) · [Axioms by theorem](five-theorems/axioms.log)

GitHub artifact `14916660212` has SHA-256 `ea12fb149e155b1bfa0e56a98f2deb456112d8409eb8d97126a9658d78468710`. This directory retains the original ZIP and the selected raw reports. Community main subsequently advanced to `ba5e0217`. Its only new file change is `verification/NOTES.md`. The official parent module manifest is identical, and the two merge trees differ from the checked heads only in that documentation. [Current main input comparison](latest-main.json)
