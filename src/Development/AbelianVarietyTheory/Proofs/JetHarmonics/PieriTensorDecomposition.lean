module

public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesParameterUnique
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasicStatement
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFRepDualStandardUnitaryRep
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFRepExteriorPowerStandardRep
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyShapeGaps
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothMapsClosureStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorDecompositionParameters
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
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

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section TensOrthAux

end TensOrthAux

namespace GlobalTheory.TensExists

theorem l1_add_le {n : ℕ} (x y : Fin n → ℤ) : n1 (x + y) ≤ n1 x + n1 y := by
  unfold n1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => Int.natAbs_add_le _ _

theorem n1_eZ_eq_card {n : ℕ} (I : Finset (Fin n)) : n1 (eZ I) = I.card := by
  unfold n1 eZ
  have : ∀ i : Fin n, (if i ∈ I then (1 : ℤ) else 0).natAbs = if i ∈ I then 1 else 0 := by
    intro i; split_ifs <;> rfl
  simp [this]

end GlobalTheory.TensExists
