# Reproduce the PR 120 namespace correction

This package reproduces the source patch for consolidated PR head `f94106583626ad6b48ac6e239e0b2e5ffc879555`. Its input records the namespace registrations visible to each named lookup. These come from the original Lean 4.36.0 compiler objects and the original and consolidated import graphs. It also records the active open declarations and the Git and original compiler archive identities. This snapshot is specific to the two source revisions.

The cumulative patch restores 1,454 selectors in 1,020 files. The incremental patch starts at author PR 16 revision `f2ecfceb6b75cc21565a2a0e21a1aa2ba10470f7`. It adds 1,336 selectors in 932 files. It leaves the 113 selectors already in PR 16 and the five selectors supplied by author PRs 3 and 7 to those PRs.

Run these commands in a checkout that contains the submitted commit, its parent, and the PR 16 base commit. Use Python 3.9 or later and the pinned compiler.

```sh
python3 restore_open_scopes.py --repo . --variant cumulative --verify-lean lean --output cumulative.patch
python3 restore_open_scopes.py --repo . --variant incremental --output extend-16.patch
git apply --check extend-16.patch
```

Run the last command in a checkout of the exact PR 16 base. The generator reads Git objects and writes only the specified patch. It verifies the source spelling under each original compiler reference, the expected source and protected Git blobs, the existing source changes at the incremental base, and the patch SHA-256.

Add `--archive-manifest /path/to/base-modules.jsonl.gz` to check each original module identity against the pinned baseline artifact manifest. Add one or more `--original-library /path/to/lib/lean` options to verify the original selective-open bindings against the actual Lean `.ilean` files.

The native checker runs `Lean.ResolveName.resolveNamespace` in the recorded states. It checks the ordered list of opened namespaces for every ordinary and scoped command and for every selective command with one original namespace. One selective command originally searched two namespaces for `pullback`. Its original compiler reference selects `CategoryTheory.Limits.pullback`. The patch opens this declaration from its recorded owner. The checker verifies this case by its selected binding.

Source rebuilding and the final `Main` and axiom checks use the project’s upstream tools. The registry check tests namespace selection only.
