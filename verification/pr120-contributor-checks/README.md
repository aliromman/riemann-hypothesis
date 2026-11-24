# Lean 4.36 checks for the chart and Galois repairs

Maugomez77 submitted both repairs to rohanarun's integration branch. Roy7 also identified the chart selection error. These checks use Lean 4.36.0 and Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. [Chart repair](https://github.com/rohanarun/riemann-hypothesis/pull/790) · [Galois repair](https://github.com/rohanarun/riemann-hypothesis/pull/796).

## Chart module

The parent `0da3667a166e6fb5ff5362fb7753cd4be7689a7a` gives eight diagnostics in `ChartDensityIntegrable`. The first error contains the namespace twice. Lean adds the namespace from `open N (...)` to each name in the list. That makes a rooted entry inside the list invalid. The remaining errors occur when the proof tries to use names from the rejected command. On `82e1833b15b64323a3ea24936377b600412a058e` the relative entries compile. Only one of the 1,532 project inputs changed. Stock Lake completed 21,313 jobs. The kernel replay passed and eight axiom records use only the permitted axioms.

Use a separate checkout for each revision. Run this command in each checkout.

```sh
lake build Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartDensityIntegrable
```

The two JSON files contain the source and input hashes. The kernel receipt includes the Lake dependency hash. To repeat the replay in the repaired checkout, use the Lean file from the adjacent verification directory.

```sh
printf '%s\n' Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartDensityIntegrable > /tmp/pr120-chart-target.txt
PR120_REPLAY_LIST=/tmp/pr120-chart-target.txt lake env lean "$evidence/../pr120-shard-roots/ReplayOriginalKernel.lean"
```

Set `evidence` to the absolute path of this directory.

## Galois decomposition subgroup

In the original compiler data, line 46, column 94 of `Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight` selects `ReciprocityTheory.Gal.Dec`. The column uses UTF-16 units and starts at zero. The corresponding site in the consolidated `Bundle0019` is line 53, column 94. Contributor commit `19130373c306d36f554f8f9689c4ef7f4b770c78` restores this exact name.

On the pre-consolidation revision `c7791603122c0328f79e49f6be5d7d4402effc53`, build the two providers. Then run the four example files from this directory with `lake env lean`.

```sh
lake build ReciprocityTheory.GaloisValuations.Global ReciprocityTheory.NeutralLocalFields.Duality
lake env lean "$evidence/bare.lean"
lake env lean "$evidence/recorded.lean"
lake env lean "$evidence/other.lean"
lake env lean "$evidence/SameSubgroup.lean"
```

The bare name gives one ambiguity. Both qualified forms compile. The last example proves their equality by `rfl`. The physical chart build and the Galois examples do not cover `Main` or the five final statements.
