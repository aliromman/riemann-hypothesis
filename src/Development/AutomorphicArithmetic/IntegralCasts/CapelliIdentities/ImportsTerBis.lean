module

public import Mathlib.NumberTheory.Padics.Complex
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

noncomputable def UpperTheory.Reformulated.B.PadicComplexRingOfIntegers.intRing :
    (p : ℕ) → [inst : Fact (Nat.Prime p)] → Subring ℂ_[p] :=
  fun p _ =>
    { carrier := {x : ℂ_[p] | ‖x‖ ≤ 1}
      mul_mem' := fun {a b} ha hb => by
        have ha' : ‖a‖ ≤ 1 := ha
        have hb' : ‖b‖ ≤ 1 := hb
        show ‖a * b‖ ≤ 1
        rw [norm_mul]
        exact mul_le_one₀ ha' (norm_nonneg b) hb'
      one_mem' := by
        show ‖(1 : ℂ_[p])‖ ≤ 1
        exact norm_one.le
      add_mem' := fun {a b} ha hb => by
        have ha' : ‖a‖ ≤ 1 := ha
        have hb' : ‖b‖ ≤ 1 := hb
        show ‖a + b‖ ≤ 1
        exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha' hb')
      zero_mem' := by
        show ‖(0 : ℂ_[p])‖ ≤ 1
        rw [norm_zero]
        exact zero_le_one
      neg_mem' := fun {a} ha => by
        have ha' : ‖a‖ ≤ 1 := ha
        show ‖-a‖ ≤ 1
        rwa [norm_neg] }
