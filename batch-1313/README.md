# PR #879 on community batch 8

This record compares community main `9282d3a102c4aff0e6026746db2a8990f5d9cddd` with fork commit `e44617765779eb58a6edab2c957ea3c4a9cd4337`. The source tree is `6af81f1c5c2293469175c13cfd47bc25932da66c`. Both use Lean 4.37.0-rc1 and Mathlib `31ce06eaadf4a200c0e1407c5f10953cf606b8f8`. The official cache contains 59,868 compiled project modules. The source also includes the separate challenge file. [Community merge](https://github.com/leanprover-community/riemann-hypothesis/pull/1313) · [Proof files, pins and target names](protected-inputs.json) · [Official archive receipt](official-inputs.json)

The candidate removes 1,014,886 private Mathlib imports and inserts 381 imports of eight narrower providers. All bytes after the import block match the community source. The community extractor recovers 58,670 original modules from 9,240 edited archives. The 28 sources shared with #1402 stay entirely with that contributor. [Header counts](source-audit.json) · [Peer source and merge comparison](coordination/overlap-1402.json)

| Under `src/` | Official main | Proposed |
| --- | ---: | ---: |
| Nonblank Lean lines | 14,279,063 | 13,264,558 |
| Physical Lean lines | 16,000,373 | 14,985,868 |
| Lean source bytes | 1,057,758,519 | 1,007,806,200 |
| Lean files | 59,869 | 59,869 |

The edited files own 874,546 declaration occurrences and 858,637 distinct names. The project import graph contains 367,789 edges. Of the other modules, 2,584 import an edited module directly and 10,341 depend on one at any depth. Each graph edge agrees with the official compiled header. [Per-owner names](declarations) · [Downstream counts](dependencies.json) · [Compiled graph comparison](compiled-graph.json)

Stock Lake built 7 requested roots in a 74-module workload on Ubuntu. The declaration comparator checked 3,452 declarations, including proof terms, normalized warnings and the required raw compiler outputs. The stock kernel checker replayed 1 selected downstream targets. The artifact also contains the three positive and negative Comparator controls. [Run and full comparison](bounded/summary.json) · [Original GitHub artifact](bounded/github-artifact.zip) · [Earlier workload input comparisons](bounded/prior-workload-inputs.json)

For the complete comparison, 26,037 changed owners require new compilations. Another 12,929 have matching original and candidate source bytes, the whole official owner archive, and ordered effective compiler inputs. The two tables give the reason for each decision. [Selection](project-inputs/selection.json) · [Fresh](project-inputs/fresh.tsv.gz) · [Reusable](project-inputs/reusable.tsv.gz)

The official parent has 65,982,391,336 bytes of project compiler data across five files per module. The complete table gives all 299,340 file hashes and sizes. Whole-project clean build time remains unmeasured. [Parent files and sizes](ordinary-lake)

The two proposals combine cleanly. Across all 9,139 shared source paths, Git preserved the proposed import header and scope body byte for byte. Together they remove 1,396,755 nonblank Lean lines. The peer inventory reports additional Git conflicts against each peer's own control merge with main. [Combined tree and path counts](composition.json) · [Per-file checks](composition-source.jsonl.gz) · [Open PR inventory](coordination/summary.json) · [Precedents and source comparisons](coordination/current-precedents.json)
