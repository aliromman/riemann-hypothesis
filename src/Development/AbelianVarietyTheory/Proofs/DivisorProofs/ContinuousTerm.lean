module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussZero
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

noncomputable section

open NumberField

namespace GlobalTheory.HeckeMellin

variable {I : Type} [Fintype I]

def term (n : I → ℤ) (s : ℂ) (v : I → ℂ) (y : I → ℝ) : ℂ :=
  GlobalTheory.HeckeTheta.gauss n (GlobalTheory.HeckeTheta.dil y v) * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))

theorem term_zero {n : I → ℤ} (hn : ∃ i, n i ≠ 0) (s : ℂ) (y : I → ℝ) : term n s 0 y = 0 := by
  have : GlobalTheory.HeckeTheta.dil y (0 : I → ℂ) = 0 := by
    funext i; simp [GlobalTheory.HeckeTheta.dil]
  rw [term, this, GlobalTheory.HeckeTheta.gauss_zero hn, zero_mul]

end GlobalTheory.HeckeMellin
