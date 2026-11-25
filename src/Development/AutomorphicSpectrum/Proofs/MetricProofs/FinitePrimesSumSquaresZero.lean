module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Localization.FractionRing
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

@[expose] public section

namespace GlobalTheory.CompanionTheory.QuadFin

theorem exists_eq_add_mul_of_mem_adjoin {E : Type*} [Field E] [Algebra ℚ E] (x : E) (c : ℚ)
    (hx : x ^ 2 = algebraMap ℚ E c) {y : E} (hy : y ∈ IntermediateField.adjoin ℚ {x}) :
    ∃ a b : ℚ, y = algebraMap ℚ E a + algebraMap ℚ E b * x := by
  have hint : IsIntegral ℚ x :=
    ⟨Polynomial.X ^ 2 - Polynomial.C c, Polynomial.monic_X_pow_sub_C c two_ne_zero, by simp [hx]⟩
  have hy' : y ∈ Algebra.adjoin ℚ {x} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hy
  refine Algebra.adjoin_induction (fun z hz => ?_) (fun r => ?_) (fun u v _ _ hu hv => ?_)
    (fun u v _ _ hu hv => ?_) hy'
  · exact ⟨0, 1, by rw [Set.mem_singleton_iff.mp hz]; simp⟩
  · exact ⟨r, 0, by simp⟩
  · obtain ⟨a, b, rfl⟩ := hu
    obtain ⟨a', b', rfl⟩ := hv
    exact ⟨a + a', b + b', by simp only [map_add (f := _)]; ring⟩
  · obtain ⟨a, b, rfl⟩ := hu
    obtain ⟨a', b', rfl⟩ := hv
    refine ⟨a * a' + b * b' * c, a * b' + a' * b, ?_⟩
    simp only [map_add (f := _), map_mul]
    linear_combination (algebraMap ℚ E b * algebraMap ℚ E b') * hx

end GlobalTheory.CompanionTheory.QuadFin
