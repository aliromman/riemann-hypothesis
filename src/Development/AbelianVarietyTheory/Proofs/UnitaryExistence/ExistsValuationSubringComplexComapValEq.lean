module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
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

namespace GlobalTheory

theorem exists_valuationSubring_complex_comap_val_eq (F : IntermediateField ℚ ℂ)
    (U : ValuationSubring F) (p : ℕ) (hp : (p : F) ∈ U.nonunits) :
    ∃ W : ValuationSubring ℂ, (p : ℂ) ∈ W.nonunits ∧ W.comap F.val.toRingHom = U := by
  obtain ⟨W, hW⟩ : ∃ W : ValuationSubring ℂ, W.comap (algebraMap F ℂ) = U :=
    exists_valuationSubring_comap_eq U _
  refine ⟨W, ?_, hW⟩
  rw [ValuationSubring.mem_nonunits_iff_or] at hp ⊢
  rcases hp with h | h
  · left
    simpa using congrArg (algebraMap F ℂ) h
  · right
    rw [← hW, ValuationSubring.mem_comap] at h
    simpa using h

end GlobalTheory
