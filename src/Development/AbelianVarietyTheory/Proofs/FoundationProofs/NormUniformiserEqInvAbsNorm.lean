module

public import Formalism.SatakeDualWeyl.StatementE
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
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

open scoped NNReal
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem norm_uniformiser_eq_inv_absNorm :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ϖ : v.adicCompletion F),
      Formalism.UG.IsUnifV F v ϖ → ‖ϖ‖₊ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0)⁻¹ := by
  intro F _ _ v ϖ h
  apply NNReal.eq
  rw [coe_nnnorm, FinitePlace.norm_def]
  unfold Formalism.UG.IsUnifV at h
  rw [h]
  have hne : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≠ 0 :=
    WithZero.coe_ne_zero
  rw [WithZeroMulInt.toNNReal_neg_apply _ hne]
  simp only [WithZero.log, WithZero.recZeroCoe_coe, toAdd_ofAdd, zpow_neg, zpow_one, NNReal.coe_inv]

end GlobalTheory
