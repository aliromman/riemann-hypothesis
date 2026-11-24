module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartSingleton
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Separation.Connected

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts

namespace GlobalTheory.CompanionTheory.MixZ

theorem curveInt : CurveInt := by
  intro Z _ q hq L M r hr
  refine ⟨fun σ => ?_, GlobalTheory.ArchDimZero.main ℤ Z q hq M L r hr⟩
  have := GlobalTheory.ArchDimZero.isProper hq
  have := GlobalTheory.ArchDimZero.finite_cxPts hq σ
  have h₁ : (L.φ σ).chernPart 0 1 = Measure.count := Measure.ext_iff_singleton.2 fun y => by
    rw [GlobalTheory.ArchDimZero.chernPart_singleton hq L σ 1 y, Measure.count_singleton]
    simp
  have h₂ : (L.φ σ).chernPart 0 (-1) = 0 := Measure.ext_iff_singleton.2 fun y => by
    rw [GlobalTheory.ArchDimZero.chernPart_singleton hq L σ (-1) y]
    simp
  refine ⟨?_, ?_⟩
  · rw [h₁]
    exact (Integrable.of_finite (μ := Measure.count) (f := logNorm (M.φ σ) r)).integrableOn
  · rw [h₂]
    exact (integrable_zero_measure : Integrable (logNorm (M.φ σ) r) 0).integrableOn

end GlobalTheory.CompanionTheory.MixZ
