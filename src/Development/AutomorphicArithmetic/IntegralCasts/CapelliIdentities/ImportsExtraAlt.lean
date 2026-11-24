module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Valuation.Integral
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

namespace UpperTheory.Reformulated.B.S6

theorem norm_le_one_of_isIntegral (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  let v : Valuation (PadicAlgCl l) NNReal := NormedField.valuation
  have hmem : ∀ a : ℤ_[l], algebraMap ℤ_[l] (PadicAlgCl l) a ∈ v.integer := by
    intro a
    have h : ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ ≤ 1 := by
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']
      exact a.2
    exact h
  let f : ℤ_[l] →+* v.integer := (algebraMap ℤ_[l] (PadicAlgCl l)).codRestrict v.integer hmem
  have hint : IsIntegral v.integer x := by
    obtain ⟨P, hP, hPx⟩ := hx
    refine ⟨P.map f, hP.map f, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hPx
  exact (Valuation.integer.integers v).mem_of_integral hint

end UpperTheory.Reformulated.B.S6
