module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
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

open MeasureTheory

namespace PositivityTheory.RgFd

def MomB : Prop :=
  ∀ (I : Type) [Fintype I] (α β : I → ℝ) (c : ℝ), (∀ i, 0 < α i) → (∀ i, 0 ≤ β i) → 0 ≤ c →
    ∃ (ν' : Measure (I → ℝ)) (U' : (I → ℝ) → ℝ), Measurable U' ∧ (∀ y, 0 < U' y ∧ U' y ≤ 1) ∧
      ∀ t : ℕ, ∫⁻ y, ENNReal.ofReal (U' y ^ t) ∂ν' = ENNReal.ofReal (c / ∏ i, (α i + t * β i))

def MomW : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → ENNReal) (U : Ω → ℝ) (I : Type) [Fintype I] (α β : I → ℝ)
    (c : ℝ) (t0 : ℕ), Measurable h → Measurable U → (∀ x, 0 ≤ U x ∧ U x ≤ 1) → (∀ i, 0 < α i) → (∀ i, 0 ≤ β i) → 0 ≤ c →
    (∀ t : ℕ, t0 ≤ t → ∫⁻ x, h x * ENNReal.ofReal (U x ^ t) ∂P = ENNReal.ofReal (c / ∏ i, (α i + t * β i))) →
    ∫⁻ x in {x | 0 < U x}, h x ∂P = ENNReal.ofReal (c / ∏ i, α i)

end PositivityTheory.RgFd
