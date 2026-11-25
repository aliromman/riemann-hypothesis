module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsOrthonormalOfLinearIndependent
import Mathlib.NumberTheory.Height.NumberField
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

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.PlueckerBound

theorem norm_det_inner_le {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {b : ℕ}
    (u w : Fin b → E) :
    ‖(Matrix.of fun a a' => ⟪u a, w a'⟫_ℂ).det‖ ≤ (∏ a, ‖u a‖) * ∏ a, ‖w a‖ := by
  have h := GlobalTheory.Hadamard.norm_det_apply_le (𝕜 := ℂ) (fun a => innerSL ℂ (u a)) w
  simp only [innerSL_apply_apply, innerSL_apply_norm] at h
  rw [mul_comm]
  exact h

theorem det_inner_sum_smul {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {b : ℕ}
    (u v : Fin b → E) (t : Matrix (Fin b) (Fin b) ℂ) :
    (Matrix.of fun a a' => ⟪u a, ∑ i, t i a' • v i⟫_ℂ).det
      = (Matrix.of fun a a' => ⟪u a, v a'⟫_ℂ).det * t.det := by
  rw [← Matrix.det_mul]
  congr 1
  ext a a'
  simp [Matrix.mul_apply, mul_comm]

theorem norm_det_inner_le_of_det_eq_one (n b : ℕ) (v u : Fin b → EuclideanSpace ℂ (Fin n))
    (t : Matrix (Fin b) (Fin b) ℂ) (ht : t.det = 1) :
    ‖(Matrix.of fun a a' => ⟪u a, v a'⟫_ℂ).det‖ ≤ (∏ a, ‖u a‖) * ∏ a, ‖∑ i, t i a • v i‖ := by
  have h := norm_det_inner_le u (fun a => ∑ i, t i a • v i)
  rwa [det_inner_sum_smul, ht, mul_one] at h

end GlobalTheory.PlueckerBound
