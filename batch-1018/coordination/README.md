# Parallel proposals

The inventory covers the 189 pull requests open at 12:30 UTC on 24 November 2026. For each independent proposal with intersecting paths, the comparison runs Git's normal three-way merge against the community parent and against the proposed head. The records distinguish conflicts already present on the parent from conflicts introduced by each refactor. The two refactor PRs are excluded from the peer count. Their joint result is in the adjacent composition records.

The archive-removal proposal #988 and scope folding in #977 both edit all 11,579 retained clumps and the generator. The former drops the archived imports and the extraction command. Scope folding keeps all 68,401 headers. On #988's own parent, filtering out those headers recreates its source on every common clump, with zero edits to the active proof body. Coordination between these formats needs a decision about retaining the round trip.

PR #1057 changes the visibility of project imports and of individual clump members. The import PR intersects 968 of its files and has 373 additional Git conflicts. The scope PR intersects 219 and has 208 additional conflicts. The source reconstruction starts from #1057's actual modified files. It applies the private Mathlib import edits on those headers, and uses the normal readers and renderer on the modified members. Across the 219 clumps, 1,193 member sources round-trip in order. The study finds a source resolution on all 971 distinct intersecting files. It preserves the visibility choices in #1057. An integrated Lean build still needs to check those different declarations and imports.

The large rename, formatting, consolidation and other conflicts are recorded per path in the compressed table. This snapshot describes the heads named in each record. [Archive removal](https://github.com/leanprover-community/riemann-hypothesis/pull/988) · [Import privatization](https://github.com/leanprover-community/riemann-hypothesis/pull/1057)

A later import-pruning change, #1103 by @dga471, edits 3,141 files outside Development. A direct Git comparison shows zero common files with #879. It shares 423 files with #977. The merged bytes in each contain its import header and the scope branch’s clump body. [Peer source check](later-independent-imports.json) · [PR #1103](https://github.com/leanprover-community/riemann-hypothesis/pull/1103)

## Follow-up on community batch 5

Community batch #1119 shares 143 source files with this proposal at its reviewed head. The source pass preserves the 4 files that the batch deletes as deletions and applies the same transformation to all 139 surviving sources. The exercise counts 23 additional textual conflicts in a normal Git merge. A combined build on that future baseline would have to check the new proof text. [Source inventory for the open batch](batch5-peer-sources.json) · [Per-file records](batch5-peer-sources.jsonl.gz) · [Other new or updated open proposals](incremental-peer-heads.json)
