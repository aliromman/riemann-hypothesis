module

public import Mathlib.Data.Matrix.Mul
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

namespace GlobalTheory.LowerTriangularMul

theorem lowerTriangular_mul {S : Type} [CommRing S] {n : ℕ} (A B : Matrix (Fin n) (Fin n) S)
    (hA : ∀ (i j : Fin n), i < j → A i j = (0 : S))
    (hB : ∀ (i j : Fin n), i < j → B i j = (0 : S)) :
    ∀ (i j : Fin n), i < j → (A * B) i j = (0 : S) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge i k with hik | hki
  · rw [hA i k hik, zero_mul]
  · rw [hB k j (lt_of_le_of_lt hki hij), mul_zero]

alias main := _root_.GlobalTheory.LowerTriangularMul.lowerTriangular_mul

end GlobalTheory.LowerTriangularMul
