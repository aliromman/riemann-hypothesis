# Reproduce the AdmLoc instance controls

Gledos isolated `GlobalTheory.AdmLoc.modTens` and `modFun` in [author PR #867](https://github.com/rohanarun/riemann-hypothesis/pull/867). Maugomez77 verified the physical Satake target and supplied an independent [explicit-argument control](https://github.com/rohanarun/riemann-hypothesis/pull/869). Roy7 proposed changing the instance registrations in [community issue #599](https://github.com/leanprover-community/riemann-hypothesis/issues/599).

## Lean 4.36.0

The physical Satake target at `8feebfa6747502c29909a193b5a67df585e46571` produced 51 errors. The controlled experiment uses all six sections from that commit. It combines their original imports from `c7791603122c0328f79e49f6be5d7d4402effc53`. The original and consolidated providers have the same declaration text. Each arm compiles the provider with the original header so that all imports use one file layout.

| Satake imports and provider | Errors | Target exit |
| --- | ---: | ---: |
| Original imports | 0 | 0 |
| Add the unmodified provider | 51 | 1 |
| Use the default priority for the two instances | 51 | 1 |
| Keep high priority and add `@[reducible]` | 51 | 1 |
| Use low priority for the two instances | 0 | 0 |
| Register the two high-priority instances with `scoped instance` | 0 | 0 |

The last row passed `leanchecker`. Compared with the first row, all 38 public types, three definition bodies, 35 proof terms and 38 axiom records match. The high and low providers have 169 matching types and axiom records, 96 matching definition bodies and 63 matching theorem proofs. The checker compares binder modes and checks the permitted axioms. Its six output columns give public names, identical raw types, definitions, theorems, matching proof terms and axiom records.

The scoped Satake control also passed kernel replay and retained the same 38 types and axiom records. On the consolidated branch at `16f10fc4b35d0e25866167c112c7232b2cb7f8f8`, global low priority produced two errors in `ResBound`. The original and scoped builds passed. Their respective kernel checks passed for the provider and `ResBound`. Both types and bodies matched the originals for all 41 public declarations in `ResBound` that the checker could compare.

Use a separate checkout at `c7791603122c0328f79e49f6be5d7d4402effc53`. Fetch the author branch into that clone so that Git can read the diagnostic commit. Set `checks` to the absolute path to this directory. Run these commands from the original checkout with its pinned Mathlib.

```sh
repo="$PWD"
trial=$(mktemp -d)
python3 "$checks/check_priorities.py" --repo "$repo" --list-targets > "$trial/targets"
xargs lake build < "$trial/targets"
lake env python3 "$checks/check_priorities.py" --repo "$repo" \
  --original-lib "$repo/.lake/build/lib/lean" --output "$trial/priorities"
lake env python3 "$checks/check_scoped_caller.py" --repo "$repo" \
  --original-lib "$repo/.lake/build/lib/lean" \
  --original-object "$trial/priorities/original/SatakeProof.olean" --out "$trial/scoped"
```

## A required instance on community main

The following test uses `343b1de38bbe4c5c66f1c1c0afd7c34e8645acdf` with Lean 4.37.0-rc1. `ResBound.lean:138` defines `TopSit.Vanish`. It needs the tensor-product module over `OL S.LL` for the residual representation. The original code opens `GlobalTheory.AdmLoc`. The stock 157-module target passed. After the two global demotions, `ResBound` failed at the existing 20,000-heartbeat typeclass limit. Registering the same two instances with `scoped instance (priority := high)` let the 157-module target build. These tests cover the named consumer and its prerequisites. A change to the declaring module still needs verification on its other dependents.

Both scoped 4.37 kernel checks passed. The public-type comparison for the last consumer found a different expression for `GlobalTheory.UseLoc.Cases.partW`. This leaves the effect of scoping on that declaration open. The physical `SatakeParameters.DmulMulDRight` control on this same revision had 51 errors with the added global provider and zero with the scoped provider. Its kernel replay, 22 public types, three definition bodies, 19 proofs and 22 axiom records passed.

Use separate clean checkouts of the indicated commit for the stock, low and scoped cases. Fill the stock cache with `lake exe cache get` if available. In the two modified checkouts, first run `git apply "$checks/main-low.patch"` or `git apply "$checks/main-scoped.patch"`. Run this target in each checkout.

```sh
lake build Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedEnlargementCutCocyclesBlochKato
```

In a separate Lean 4.37.0-rc1 test at `a28ad7ec8b9f5ff4ec448fe210d3ac57aacfffe1`, the physical `SatakeParameters.DmulMulDRight` built on its normal imports. Adding the provider reproduced 51 errors with high priority and 51 with default priority. Low priority brought that count to zero and passed kernel replay. The public source patch on 4.36 has exact parent `376bacf238f6f3a7a4f120aeb01c89d124ea7a66`. The genuine `ResBound` failure limits its use. [4.36 experiment](https://github.com/aliromman/riemann-hypothesis/commit/ef0cac9609130764c633dc4f471295f00e1fd1a2).
