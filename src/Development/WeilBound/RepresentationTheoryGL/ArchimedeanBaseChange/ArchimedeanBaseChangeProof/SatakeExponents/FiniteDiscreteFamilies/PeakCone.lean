module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Basic.Complex.Basic
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

namespace PositivityTheory.Rg.BcB.F.F5

def coneGL (n : ℕ) (M : ℤ) : Set (Fin n → ℤ) := {x | ∀ i j : Fin n, i < j → x j + M ≤ x i}

def evalGL {n : ℕ} (c : (Fin n → ℤ) →₀ ℂ) (ξ : Fin n → ℂˣ) : ℂ :=
  c.sum fun x a => a * ((∏ i, ξ i ^ x i : ℂˣ) : ℂ)

def PeakCone : Prop := ∀ (n : ℕ) (M : ℤ) (α : Fin n → ℂˣ) (S : Finset (Fin n → ℂˣ)), α ∉ S →
  ∃ c : (Fin n → ℤ) →₀ ℂ, (↑c.support ⊆ coneGL n M) ∧ evalGL c α = 1 ∧ ∀ β ∈ S, evalGL c β = 0

end PositivityTheory.Rg.BcB.F.F5

end
