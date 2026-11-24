module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.InvTransposeGLInvTransposeGL
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IwahoriDoubleCosets
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable

@[expose] public section

open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc

noncomputable section

namespace UpperTheory.ConvolutionTheory.Loc

variable {k E : Type} [Field k] [Field E] [Algebra k E] {n : ℕ} [TopologicalSpace k] [TopologicalSpace E]
  [MeasurableSpace (GL (Fin n) E)] [MeasurableSpace (GL (Fin n) k)]

def Match (σ : E ≃ₐ[k] E) (μE : Measure (GL (Fin n) E)) (μk : Measure (GL (Fin n) k)) (φ : GL (Fin n) E → ℂ) (f : GL (Fin n) k → ℂ) : Prop :=
  (∀ (δ : GL (Fin n) E) (γ : GL (Fin n) k) (h : GL (Fin n) E)
      (μδ : Measure (twCent (sigmaGL σ) δ)) (μγ : Measure (Subgroup.centralizer {γ})),
      IsTwRegSemisimple σ δ → normGL σ δ = h * incl γ * h⁻¹ → μδ.IsHaarMeasure → μγ.IsHaarMeasure →
      Measure.map (fun x : twCent (sigmaGL σ) δ => h⁻¹ * (x : GL (Fin n) E) * h) μδ =
        Measure.map (fun t : Subgroup.centralizer {γ} => incl (t : GL (Fin n) k)) μγ →
      twOrbIntegralC (sigmaGL σ) μE δ μδ φ = orbIntegralC μk γ μγ f) ∧
  ∀ (γ : GL (Fin n) k) (μγ : Measure (Subgroup.centralizer {γ})),
    IsRegSemisimple γ → (¬ ∃ δ : GL (Fin n) E, IsNormOf σ δ γ) → μγ.IsHaarMeasure → orbIntegralC μk γ μγ f = 0

end UpperTheory.ConvolutionTheory.Loc

end
