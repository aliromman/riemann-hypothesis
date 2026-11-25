module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
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

@[expose] public section

open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.twUniq_pf :
    TwUniq := by
  intro E _ _ _ n μ π φ t t' h₁ h₂
  obtain ⟨L₁, e₁, -, rfl⟩ := h₁
  obtain ⟨L₂, e₂, -, rfl⟩ := h₂
  obtain rfl : L₁ = L₂ := by
    refine LinearMap.ext fun ψ => Subtype.ext (Subtype.ext (funext fun x => ?_))
    rw [e₁ ψ x, e₂ ψ x]
  rfl
