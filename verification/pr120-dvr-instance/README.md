# The DVR parent of IsCD on Lean 4.36

Jonathan Roy identified a derived instance in `UpperTheory.V.Pr.IsCD` and changed the discrete valuation ring parent to a stored instance field. This test ports his exact class change to Rohan’s 4.36 consolidation. The Lean 4.36 parent is `1c5f0accc9a1e44d4166867f5452c8bc68440979`. The candidate is `fa785cee0bec564a80e9020765bd516c68aec60c`. [Roy’s original PR](https://github.com/leanprover-community/riemann-hypothesis/pull/611).

The parent fails at `CurveDVRSpecialization/Bundle0008.lean:192:57`. Lean times out at 20,000 typeclass heartbeats while looking for `IsLocalRing L.R`. The old DVR instance asks for two commutative rings and an algebra before it searches for an `IsCD` witness. The new projection searches directly for the witness. The class still supplies a domain, a discrete valuation ring, completeness, a local structure map, and a finite residue field.

The 16 selected physical targets and all 623 project inputs were checked against Git on each revision. One provider source changes. The parent build reports one error in one target. The candidate build completes all 19,495 Lake jobs. All 16 selected objects pass native kernel replay. All 227 records in their exported axiom tables use only `propext`, `Quot.sound` and `Classical.choice`.

Two further controls remove the existing local IsCD instance exclusions from the complete `FinCrit` and `PxIsCont` files. The `FinCrit` source is byte-identical across class forms. It reports 29 diagnostics with the original class, including 27 timeouts, and zero with the new class. On this branch, `PxIsCont` succeeds in both controls.

Run the commands below in a clean checkout at each of the two revisions. Set `evidence` to the absolute path of this directory and `scratch` to a writable directory. Use the repository’s pinned Lean and Mathlib. The last command checks both restored instance projections and the class conditions. The original class also triggers a declaration type linter timeout in that probe.

```sh
xargs lake build < "$evidence/targets.txt"
lake env python3 "$evidence/check_iscd_callers.py" "$PWD" "$scratch" control FinCrit PxIsCont
lake env lean "$evidence/CheckIsCDInterface.lean"
```

For the native kernel check on the candidate, run the following command.

```sh
while IFS= read -r module; do
  LEAN_NUM_THREADS=1 lake env leanchecker -v "$module" || exit 1
done < "$evidence/targets.txt"
```

The integration graph contains 859 other modules that import the provider directly or transitively, including `Main`. The complete project and the five-statement Comparator require the coordinator’s full check. [Pinned shard failure](https://github.com/rohanarun/alpoge-rh-replay/blob/5e9aa6777a581de62b321234921fc536439c0b50/PR120-BUGS.md).
