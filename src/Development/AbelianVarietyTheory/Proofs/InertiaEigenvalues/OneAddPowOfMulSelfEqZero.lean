module

public import Mathlib.Algebra.Ring.Defs
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

namespace GlobalTheory.OneAddPowSquareZero

theorem one_add_pow_of_mul_self_eq_zero :
    ∀ {S : Type} [inst : Ring S] (X : S), X * X = (0 : S) →
      ∀ (N : ℕ), ((1 : S) + X) ^ N = (1 : S) + (↑N : S) * X := by
  intro S _ X hX N
  induction N with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Nat.cast_succ, mul_add, mul_one, add_mul, one_mul, mul_assoc, hX,
      mul_zero, add_zero, add_mul, one_mul, add_assoc]

end GlobalTheory.OneAddPowSquareZero
