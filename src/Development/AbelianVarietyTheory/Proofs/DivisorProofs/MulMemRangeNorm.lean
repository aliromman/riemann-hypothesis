module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Mathlib.Tactic.Linter.HaveILetI
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
import GroundTheory.AutomorphicForms.HermitianClassification
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal

@[expose] public section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp.NormIndex

theorem mul_mem_range_norm (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E]
    (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (x y : Fˣ)
    (hx : x ∉ (Units.map (Algebra.norm F : E →* F)).range)
    (hy : y ∉ (Units.map (Algebra.norm F : E →* F)).range) :
    x * y ∈ (Units.map (Algebra.norm F : E →* F)).range := by
  obtain ⟨b, -, -⟩ := hE.basis
  have h2 : Module.finrank F E = 2 := by rw [Module.finrank_eq_card_basis b]; simp
  have : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  have : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  have hN : Nat.card (Fˣ ⧸ (Units.map (Algebra.norm F : E →* F)).range) = 2 :=
    GroundTheory.Automorphic.natCard_quotient_range_normUnits_eq_two (F := F) (E := E)
  have hy' : y⁻¹ ∉ (Units.map (Algebra.norm F : E →* F)).range := fun h => hy (inv_mem_iff.mp h)
  rcases GroundTheory.Automorphic.mem_or_mul_inv_mem_of_natCard_eq_two hN hy' x with h | h
  · exact absurd h hx
  · rwa [inv_inv] at h

end GlobalTheory.KSp.NormIndex
