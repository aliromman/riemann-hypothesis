# Batch #2057 resolves the #911 regression

Daniel Ang’s #1971 removed seven duplicate module instances, including the two that #911 scoped. The four files that erased `AdmLoc.modFun` now have the same Git blobs as #911’s proposed merge. Kim Morrison added local typeclass search limits to `Lem0`, `ResBound` and `Vanish`. The test below uses both changes as merged. [Daniel’s change](https://github.com/leanprover-community/riemann-hypothesis/pull/1971) · [Kim’s caller repair](https://github.com/leanprover-community/riemann-hypothesis/commit/bcd818069cf225f177b61475fe88c5a8e56769b8) · [Merged batch](https://github.com/leanprover-community/riemann-hypothesis/pull/2057)

| Lean 4.37.0-rc1 | Before · `fcb6eac75348` | Merged main · `27b55787485a` |
| --- | ---: | ---: |
| Satake errors with the instance provider imported first | 45 | 0 |
| Satake errors with the instance provider imported last | 45 | 0 |
| `ResBound` source build exit | 0 | 0 |
| `ResBound` kernel replay exit | 0 | 0 |

The Satake proof is the complete `DmulMulDRight.lean` file. Each import-order fixture has the same SHA-256 on both sides. Three targets were built from source on each revision with 939 verified project dependencies. Both Lake builds exited 0 after 12,274 jobs. [Compiler errors, fixture hashes and kernel exits](results.json) · [Stock build receipts](builds.json)

## Reproduce the check

Use separate clean checkouts of `fcb6eac7534875d32d68030967e2deae6d686151` and `27b55787485ac2a5b5b3ed2dffc697e0ae6a2f59`. In each checkout fetch the official Mathlib cache, then run the three targets. The original fixture script inserts one import and preserves the proof body. [Fixture and kernel check](../../pr120-admloc-dependents/replay_exposed_satake.py)

```sh
MATHLIB_CACHE_GET_URL=https://cache.mathlib.org/mathlib4 lake exe mathlib/cache get
lake --no-cache build \
  Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle \
  Development.AbelianVarietyTheory.Proofs.SatakeParameters.DmulMulDRight \
  Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
python3 "$evidence/verification/pr120-admloc-dependents/replay_exposed_satake.py" \
  --repo "$after" --before "$before" --after "$after" --bin "$(dirname "$(elan which lean)")" \
  --parent fcb6eac7534875d32d68030967e2deae6d686151 \
  --candidate 27b55787485ac2a5b5b3ed2dffc697e0ae6a2f59 --output "$results"
```
