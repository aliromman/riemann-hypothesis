module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.ExistsNatSmulMem
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.SimpleRing.Principal
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

namespace GlobalTheory.NatMulMemUnitaryExistence

open NumberField

theorem exists_nat_mul_mem {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ k : ℕ, 0 < k ∧ ∃ a : 𝓞 E, (a : E) = (k : E) * c := by
  obtain ⟨y, hy, hint⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic c)).exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩
  have hcast : ((y.natAbs : ℕ) : E) = ((y.natAbs : ℤ) : E) := (Int.cast_natCast _).symm
  have hint' : IsIntegral ℤ ((y.natAbs : E) * c) := by
    rcases Int.natAbs_eq y with h | h
    · rw [hcast, ← h, ← zsmul_eq_mul]; exact hint
    · have h2 : (y.natAbs : ℤ) = -y := by omega
      rw [hcast, h2, Int.cast_neg, neg_mul, ← zsmul_eq_mul]; exact hint.neg
  exact ⟨⟨_, hint'⟩, rfl⟩

theorem main {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ d : ℕ, 0 < d ∧ d • x ∈ L := by
  apply PI.WAU.exists_nat_smul_mem <;> assumption

alias target := _root_.GlobalTheory.NatMulMemUnitaryExistence.main

end GlobalTheory.NatMulMemUnitaryExistence
