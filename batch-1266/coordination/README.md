# Compatibility with other pull requests

At 2026-11-24T17:25:13Z there were 145 open proposals. Of the 143 other proposals, 43 share paths with this patch. For each such head the same Git version merged it into the community parent and into this proposal. The inventory lists the baseline conflicts and the additional conflicting paths. A clean source merge does not establish mathematical preservation. [Summary](summary.json) · [All comparisons and paths](peer-merges.jsonl.gz) · [Open PR heads](open-heads.json)

| Peer PR | Additional conflicting paths |
| --- | ---: |
| [#988](https://github.com/leanprover-community/riemann-hypothesis/pull/988) | 11,494 |
| [#97](https://github.com/leanprover-community/riemann-hypothesis/pull/97) | 5,382 |
| [#645](https://github.com/leanprover-community/riemann-hypothesis/pull/645) | 1,479 |
| [#1294](https://github.com/leanprover-community/riemann-hypothesis/pull/1294) | 9 |
| [#1099](https://github.com/leanprover-community/riemann-hypothesis/pull/1099) | 7 |
| [#1171](https://github.com/leanprover-community/riemann-hypothesis/pull/1171) | 6 |
| [#1163](https://github.com/leanprover-community/riemann-hypothesis/pull/1163) | 6 |
| [#1236](https://github.com/leanprover-community/riemann-hypothesis/pull/1236) | 4 |
| [#173](https://github.com/leanprover-community/riemann-hypothesis/pull/173) | 4 |
| [#1306](https://github.com/leanprover-community/riemann-hypothesis/pull/1306) | 3 |
| [#1296](https://github.com/leanprover-community/riemann-hypothesis/pull/1296) | 3 |
| [#1134](https://github.com/leanprover-community/riemann-hypothesis/pull/1134) | 3 |
| [#1283](https://github.com/leanprover-community/riemann-hypothesis/pull/1283) | 2 |
| [#1121](https://github.com/leanprover-community/riemann-hypothesis/pull/1121) | 2 |
| [#1115](https://github.com/leanprover-community/riemann-hypothesis/pull/1115) | 2 |
| [#1297](https://github.com/leanprover-community/riemann-hypothesis/pull/1297) | 1 |
| [#1290](https://github.com/leanprover-community/riemann-hypothesis/pull/1290) | 1 |
| [#1285](https://github.com/leanprover-community/riemann-hypothesis/pull/1285) | 1 |
| [#1281](https://github.com/leanprover-community/riemann-hypothesis/pull/1281) | 1 |
| [#1149](https://github.com/leanprover-community/riemann-hypothesis/pull/1149) | 1 |

The earlier pruning, consolidation and proof changes in #45, #55, #63, #68, #87 and #120 are covered by the source comparison. #45 and #68 merged. #55, #63, #87 and #120 closed without merging. [Latest status and Git IDs](current-precedents.json) · [Prior source comparison](https://github.com/aliromman/riemann-hypothesis/tree/4ff4a916dea1434b564f83253d729595fcd019d6/prior-work)

## Preview of community batch 8

An additional snapshot found 151 open PRs. It includes the new file-name proposal #1314 and the 46-PR community batch #1313. On the latter's draft `dda69e8303156955dfaddbc0e7192c9ceff81855`, this proposal shares 120 files. The source preview honors all 8 upstream deletions and reconstructs all 112 retained files. It projects 250,639 fewer code lines. In one import header, the community batch added a new instance of an existing line. The preview keeps the new import and the complete revised proof body. These numbers cover the source on an unmerged draft. [Full file comparison](batch8-peer-sources.jsonl.gz) · [Totals](batch8-peer-sources.json) · [Concurrent import and proof edits](batch8-concurrent-imports.json) · [Changed peer heads](incremental-pr-coordination.json)
