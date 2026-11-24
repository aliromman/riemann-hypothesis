# PR #977 on community batch 8

This record compares community main `9282d3a102c4aff0e6026746db2a8990f5d9cddd` with fork commit `28e9eedf5e13abbe174794bb69fa8363296cf2ad`. The source tree is `e0641dda707407a73d29502a55f1789eab873789`. Both use Lean 4.37.0-rc1 and Mathlib `31ce06eaadf4a200c0e1407c5f10953cf606b8f8`. The official cache contains 59,868 compiled project modules. The source also includes the separate challenge file. [Community merge](https://github.com/leanprover-community/riemann-hypothesis/pull/1313) · [Proof files, pins and target names](protected-inputs.json) · [Official archive receipt](official-inputs.json)

The renderer removes 251,087 Lean scope commands. The patch removes 250,639 lines of code after all 448 net added Python lines, including tests. The reader recovers all 68,154 proposed members byte for byte. Compared with main, 43,688 member files are byte-identical. The other 24,466 change only their outer section commands, including 3,024 that also remove an adjacent blank line. All declaration and proof text is preserved. [Per-member comparison](member-source-comparison.json) Both tool revisions read all 12,348 extractable current archives and recover the same 72,974 members in order. One unchanged legacy archive already fails the community extractor. [Command counts](scope-command-counts.json) · [Archive coverage and the exception](archive-reads.json)

| Under `src/` | Official main | Proposed |
| --- | ---: | ---: |
| Nonblank Lean lines | 14,279,063 | 13,896,813 |
| Physical Lean lines | 16,000,373 | 15,607,564 |
| Lean source bytes | 1,057,758,519 | 1,037,032,468 |
| Lean files | 59,869 | 59,869 |

The edited files own 531,371 declaration occurrences and 526,472 distinct names. The project import graph contains 367,789 edges. Of the other modules, 9,875 import an edited module directly and 30,392 depend on one at any depth. Each graph edge agrees with the official compiled header. [Per-owner names](declarations) · [Downstream counts](dependencies.json) · [Compiled graph comparison](compiled-graph.json)

Stock Lake built 27 requested roots in a 239-module workload on Ubuntu. The declaration comparator checked 7,656 declarations, including proof terms, normalized warnings and the required raw compiler outputs. The stock kernel checker replayed 6 selected downstream targets. The artifact also contains the three positive and negative Comparator controls. [Run and full comparison](bounded/summary.json) · [Original GitHub artifact](bounded/github-artifact.zip) · [Earlier workload input comparisons](bounded/prior-workload-inputs.json)

For the complete comparison, 8,227 changed owners require new compilations. Another 3,313 have matching original and candidate source bytes, the whole official owner archive, and ordered effective compiler inputs. The two tables give the reason for each decision. [Selection](project-inputs/selection.json) · [Fresh](project-inputs/fresh.tsv.gz) · [Reusable](project-inputs/reusable.tsv.gz)

The official parent has 65,982,391,336 bytes of project compiler data across five files per module. The complete table gives all 299,340 file hashes and sizes. Whole-project clean build time remains unmeasured. [Parent files and sizes](ordinary-lake)

The two proposals combine cleanly. Across all 9,139 shared source paths, Git preserved the proposed import header and scope body byte for byte. Together they remove 1,396,755 nonblank Lean lines. The peer inventory reports additional Git conflicts against each peer's own control merge with main. [Combined tree and path counts](composition.json) · [Per-file checks](composition-source.jsonl.gz) · [Open PR inventory](coordination/summary.json) · [Precedents and source comparisons](coordination/current-precedents.json)

## Additional checks

The parent control rebuilt both real proof providers and Main. Main’s 59,011 public project inputs and MainConclusion’s additional private dependency on Lemmata.TracePi were authenticated separately. The rebuilt provider and Main files matched all fifteen official outputs. Replacing the provider-only input with a wrong file failed the check. [Parent control](parent-control/pinned-parent.json) · [Wrong-input control](parent-control/wrong-provider-only-input.json)

The inspected draft of community batch #1410 was `10b741f004e9878adc2b5f8b5adc915df4b94f6a`. Across the two refactors, it shares 5,680 source files. A source-only reconstruction accounted for each one. The batch replaces StrongMultiplicityOne.Strong’s 25-member archive with a 16-line proof file, which supersedes the old renderer change on that path. The preview preserves those source bytes. A future community merge needs its own compiler comparisons. [Draft source comparison](coordination/batch9-preview.json) · [Per-file decisions](coordination/batch9-sources.jsonl.gz)

The current Ubuntu test run passed 314 repository script tests, including 14 clump tests, and 60 native CI tests. All four compiler diagnostics matched their reference inputs, stock errors and recovered member names. [Tests and logs](tests/summary.json) · [Full tool timing and memory](planner/README.md)
