module

public import Formalism.PeriodIntegrals.UpqRep
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.HermitianCurvature.StatementI
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NotCdomAddRoot

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.DominantRootSums

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
private lemma sum_index_mul_root_eq_sub' {n : ℕ} (a b : Fin n) :
    ∑ i : Fin n, ((i : ℕ) : ℝ) * _root_.PI.UpqRep.root a b i = ((a : ℕ) : ℝ) - ((b : ℕ) : ℝ) := by
  simp [_root_.PI.UpqRep.root, Pi.single_apply, mul_sub, Finset.sum_sub_distrib]


open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
theorem _root_.GlobalTheory.DominantRootSums.not_cDom_add_root : ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℝ) (a b : Fin n), a < b →
    ¬ _root_.PI.UpqRep.CDom ε (Λ + _root_.PI.UpqRep.root a b) Λ := by
  apply _root_.GlobalTheory.CompanionTheory.DSHighestOfKType.not_cdom_add_root <;> assumption

end GlobalTheory.DominantRootSums
