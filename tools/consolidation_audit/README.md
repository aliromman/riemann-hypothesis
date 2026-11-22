# Audit a module consolidation

Compare compiled Lean declarations across two Git revisions. A proof can still compile after an unqualified name resolves to a different theorem. The report identifies the declaration, the changed expression, and the constants that entered or left its type or body.

## Run the comparison

Use Python 3.9 or later and the Lean toolchain pinned by the checkouts. Build the modules of interest in each checkout with Lake, or restore their published artifacts. The new checkout must contain both Git revisions. Use a new report directory for each run.

```sh
mkdir -p .lake/consolidation-audit
lean -c .lake/consolidation-audit/Compare.c tools/consolidation_audit/Compare.lean
leanc -O2 -o .lake/consolidation-audit/compare .lake/consolidation-audit/Compare.c -lLake

python3 tools/consolidation_audit/audit.py \
  --before "$OLD_CHECKOUT" --after "$NEW_CHECKOUT" \
  --base "$OLD_COMMIT" --head "$NEW_COMMIT" \
  --worker .lake/consolidation-audit/compare --out "$REPORT"
```

A published cache can have a trusted `modules.jsonl.gz` index. Pass it with `--base-index` or `--head-index`. The script checks the source tree, toolchain, Lake configuration and package manifest against the chosen revision. A recorded module must have the indexed dependency hash. With no indexed entry, the script checks the working source against its Git blob and its Lake source trace. In both cases the worker checks the actual bytes of every compiled module part against the Lake trace. A stock Lake build on each revision establishes the freshness of its dependency closure.

Use `--base-overlay DIR` for original artifacts restored separately from their checkout. Supply the `lib/lean` directory with the original module hierarchy and traces.

## Read the result

- `scope.json` records both Git commits and the module inventory. The default scope includes every `.lean` file under `src/` at the new revision. Bundle member names come from the generator's `-- bundled from` markers.
- `comparisons.jsonl` records each completed module and each difference. Declaration checks include export visibility, declaration kind, safety, reducibility class, inductive and recursor metadata, public argument names, binder plicity, types, full theorem proofs, definition bodies, and the direct constants in types and bodies.
- `removed-declarations.jsonl` records the original wrapper, target, provider and other public names in each removed module. The script matches the compiler's reference index to the old proof term. It accepts a direct constant or its eta expansion, with matching binder names and plicity. When types differ structurally, the original Lean kernel must accept a fresh `rfl` witness at the common type. Source, descriptor, compiler log and output are under `conversions/`. Use `--skip-conversion-checks` to leave these substitutions unresolved.
- `substitutions.tsv` records each accepted wrapper and its surviving target. A chain must have evidence at every step. Other public declarations in a deleted wrapper must be present in the surviving provider. Missing exports appear in the comparison.
- `summary.json` counts compared modules, pending modules, aligned declarations and differences by field. Exit status 0 requires complete coverage of the requested scope and zero findings. Use `--targets "$REPORT/pending-targets.txt"` with the same two revisions to check additional builds. `unavailable.jsonl` and unavailable records in `comparisons.jsonl` give the reasons for missing coverage.

The worker reads the public, server and private parts of each module. It discards binder labels and metadata when comparing expressions, normalizes universe levels, and rebases private names only when their original module and target identify a unique declaration. Separate checks retain public binder names and binder plicity. Some differences can be definitionally equal or arise from proof search. Each difference is an item for review.

The comparison does not certify environment extensions such as notation and tactic attributes. Use the repository's complete build and protected theorem checks for release verification. James Shore's `routeb` tool and PR #173 describe the private-level constant dependency method. This tool reads each available bundle independently while the complete build is in progress. [routeb](https://github.com/james-shore/rh-proof-dependencies/tree/70fbb2fc21fed8de3c02d9f6df0b6067bf22e879/tools/routeb) · [PR #173](https://github.com/leanprover-community/riemann-hypothesis/pull/173)

## Run the controls

```sh
AUDIT_WORKER="$PWD/.lake/consolidation-audit/compare" python3 tools/consolidation_audit/test_audit.py
```

The fixture builds two temporary Lake projects. It checks a successful proof retarget, a proof change with the same reference set, a definition change, an implicit argument change, a moved private theorem, a transitive wrapper replacement, a kernel conversion, a missing export, and damaged artifacts. It then repairs the fixture and requires zero differences.
