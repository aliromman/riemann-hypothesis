module

public import Mathlib.Analysis.Complex.Norm
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

open scoped Classical

namespace PositivityTheory.Rg.BcB.F

def ExpSum : Prop := ∀ (ι : Type) [Fintype ι] (c lam : ι → ℂ) (ρ C : ℝ) (N : ℕ), 0 ≤ ρ →
  (∀ᶠ k : ℕ in Filter.atTop, ‖∑ i, c i * lam i ^ k‖ ≤ C * (1 + k) ^ N * ρ ^ k) →
  ∀ μ : ℂ, ρ < ‖μ‖ → ∑ i with lam i = μ, c i = 0

end PositivityTheory.Rg.BcB.F

end
