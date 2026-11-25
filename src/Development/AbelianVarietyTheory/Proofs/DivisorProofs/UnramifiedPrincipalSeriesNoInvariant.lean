module

public import Mathlib.NumberTheory.LocalField.Basic
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
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.PrinTwo.NoFix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


variable (k) in
theorem exists_unif : ∃ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k := by
  obtain ⟨x, hx⟩ := valuation_surjective (uniformizer k)
  exact ⟨Units.mk0 x (by rintro rfl; exact uniformizer_ne_zero (R := k) (by simpa using hx.symm)), hx⟩

end GlobalTheory.PrinTwo.NoFix

namespace GlobalTheory.PrinTwo.NoFix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end GlobalTheory.PrinTwo.NoFix
