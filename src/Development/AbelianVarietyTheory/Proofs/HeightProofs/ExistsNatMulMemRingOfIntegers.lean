module

public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Tactic.Linter.Style
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

namespace GlobalTheory.NatMulMemRingOfIntegers

theorem exists_nat_mul_mem_ringOfIntegers {E : Type} [Field E] [NumberField E] (e : E) :
    ∃ (k : ℕ), 0 < k ∧ ∃ (r : NumberField.RingOfIntegers E), (r : E) = (k : E) * e := by
  have h0 : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have halg : IsAlgebraic ℤ e := (IsAlgebraic.of_finite ℚ e).restrictScalars ℤ
  obtain ⟨y, hy0, hint⟩ := halg.exists_integral_multiple
  rw [zsmul_eq_mul] at hint
  rcases Int.natAbs_eq y with hy | hy
  · refine ⟨y.natAbs, Int.natAbs_pos.mpr hy0, ⟨(y : E) * e, (mem_integralClosure_iff ℤ E).mpr hint⟩, ?_⟩
    show (y : E) * e = _
    rw [congrArg (Int.cast : ℤ → E) hy, Int.cast_natCast]
  · refine ⟨y.natAbs, Int.natAbs_pos.mpr hy0, ⟨-((y : E) * e), (mem_integralClosure_iff ℤ E).mpr hint.neg⟩, ?_⟩
    show -((y : E) * e) = _
    rw [congrArg (Int.cast : ℤ → E) hy, Int.cast_neg, Int.cast_natCast]
    ring

end GlobalTheory.NatMulMemRingOfIntegers
