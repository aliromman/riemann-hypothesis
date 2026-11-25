module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Mathlib.Algebra.Algebra.Hom.Rat
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

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors

namespace GlobalTheory.FieldSize

theorem sz_fieldRange_embedding (K : Type) [Field K] [NumberField K] (φ : K →+* ℂ) :
    Sz φ.toRatAlgHom.fieldRange (Real.log (Module.finrank ℚ K))
      (Real.log |((discr K : ℤ) : ℝ)| / Module.finrank ℚ K) := by
  let e : K ≃ₐ[ℚ] φ.toRatAlgHom.fieldRange := AlgEquiv.ofInjectiveField φ.toRatAlgHom
  have hfd : FiniteDimensional ℚ φ.toRatAlgHom.fieldRange := e.toLinearEquiv.finiteDimensional
  refine ⟨hfd, ?_⟩
  let _ : NumberField φ.toRatAlgHom.fieldRange := NumberField.mk
  have h1 : Module.finrank ℚ φ.toRatAlgHom.fieldRange = Module.finrank ℚ K := e.toLinearEquiv.finrank_eq.symm
  have h2 : discr φ.toRatAlgHom.fieldRange = discr K := (NumberField.discr_eq_discr_of_algEquiv K e).symm
  rw [h1, h2]
  exact ⟨le_rfl, le_rfl⟩

end GlobalTheory.FieldSize
