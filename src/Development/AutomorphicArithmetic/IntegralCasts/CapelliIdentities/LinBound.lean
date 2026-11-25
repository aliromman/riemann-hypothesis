module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Data.Matrix.Basis

@[expose] public section

theorem UpperTheory.Reformulated.B.Qj19.lin_bound.{u_1} :
    ∀ {ι : Type u_1} [Fintype ι] [DecidableEq ι] (L : Matrix ι ι ℂ →ₗ[ℂ] ℂ),
    ∃ (K : ℝ),
      (0 : ℝ) ≤ K ∧ ∀ (B : Matrix ι ι ℂ) (C : ℝ), (∀ (i j : ι), ‖B i j‖ ≤ C) → ‖(L : Matrix ι ι ℂ → ℂ) B‖ ≤ K * C := by
  intro ι _ _ L
  refine ⟨∑ i, ∑ j, ‖L (Matrix.single i j 1)‖, by positivity, fun B C hB => ?_⟩
  have h : L B = ∑ i, ∑ j, B i j * L (Matrix.single i j 1) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single B]

    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [h, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left (hB i j) (norm_nonneg _)
