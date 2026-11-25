module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVecUnitaryModule
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

open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.CoefSmooth

open scoped Matrix.Norms.Elementwise

theorem coef_smoothOnG (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (v : GlobalTheory.SmoothVecMod.smoothVec ε σ) (w : H) :
    Formalism.REAL.SmoothOnG ε (fun g => ⟪w, σ g (v : H)⟫_ℂ) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := v.2 g₀ hg₀
  refine ⟨U, fun x => ⟪w, F x⟫_ℂ, hU, hgU, ?_, fun g hg hgJ => ?_⟩
  · exact (((innerSL ℂ w).restrictScalars ℝ).contDiff.comp_contDiffOn hF)
  · exact congrArg (fun z => ⟪w, z⟫_ℂ) (hfF g hg hgJ)

end GlobalTheory.CompanionTheory.CoefSmooth
