module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsCoinv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvMonomialReduction, GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvPolynomialReduction

-- ===== clump member: GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvMonomialReduction =====
-- clump-header: {"m": "GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvMonomialReduction", "h": "module\n\npublic import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsCoinv\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Coinv

noncomputable section

theorem CoinvMonomialReduction.proof (h1 : CoinvStepReduction.Statement) :
    CoinvMonomialReduction.Statement := by
  intro K _ _ f n e
  classical
  let r : Fin f × Fin n → Fin f × Fin n → Prop := fun u v => toLex u < toLex v
  have : IsStrictTotalOrder (Fin f × Fin n) r :=
    inferInstanceAs (IsStrictTotalOrder (Lex (Fin f × Fin n)) (· < ·))
  have wf : WellFounded
      (Finsupp.Lex r (· < ·) : (Fin f × Fin n →₀ ℕ) → (Fin f × Fin n →₀ ℕ) → Prop) :=
    Finsupp.Lex.wellFounded_of_finite r wellFounded_lt
  induction e using wf.induction with
  | _ e ih =>
  by_cases hu : IsUnderStaircase e
  · exact ⟨monomial e 1, Submodule.subset_span ⟨e, hu, rfl⟩, by simp⟩
  · simp only [IsUnderStaircase, not_forall, not_le] at hu
    obtain ⟨⟨b, k⟩, hbk⟩ := hu
    obtain ⟨T, c, hT, hmem⟩ := h1 K f n b k e (by simpa using hbk)
    have hlt : ∀ e' ∈ T, Finsupp.Lex r (· < ·) e' e := by
      intro e' he'
      refine Finsupp.lex_def.mpr ⟨(b, k), fun j hj => (hT e' he').1 j ?_, (hT e' he').2⟩
      exact Prod.Lex.toLex_lt_toLex.mp hj
    choose! w hw hwm using fun e' (he' : e' ∈ T) => ih e' (hlt e' he')
    refine ⟨∑ e' ∈ T, c e' • w e',
      Submodule.sum_mem _ fun e' he' => Submodule.smul_mem _ _ (hw e' he'), ?_⟩
    have hsplit : monomial e (1 : K) - ∑ e' ∈ T, c e' • w e' =
        (monomial e 1 - ∑ e' ∈ T, c e' • monomial e' 1) +
          ∑ e' ∈ T, C (c e') * (monomial e' 1 - w e') := by
      simp only [smul_eq_C_mul, mul_sub, Finset.sum_sub_distrib]
      ring
    rw [hsplit]
    exact Ideal.add_mem _ hmem (Ideal.sum_mem _ fun e' he' => Ideal.mul_mem_left _ _ (hwm e' he'))

end

end GroundTheory.Heights₂.Heights.RestTerms
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvMonomialReduction =====

-- ===== clump member: GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvPolynomialReduction =====
-- clump-header: {"m": "GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvPolynomialReduction", "h": "module\n\npublic import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsCoinv\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Coinv

noncomputable section

theorem CoinvPolynomialReduction.proof (h1 : CoinvMonomialReduction.Statement) :
    CoinvPolynomialReduction.Statement := by
  intro K _ _ f n H
  choose v hv hvI using fun d => h1 K f n d
  refine ⟨∑ d ∈ H.support, AddMonoidAlgebra.coeff H d • v d, ?_, ?_⟩
  · exact Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _ (hv d)
  · have e1 : H - ∑ d ∈ H.support, AddMonoidAlgebra.coeff H d • v d =
        (∑ d ∈ H.support, monomial d (AddMonoidAlgebra.coeff H d)) - ∑ d ∈ H.support, AddMonoidAlgebra.coeff H d • v d := by
      rw [← H.as_sum]
    have e2 : (∑ d ∈ H.support, monomial d (AddMonoidAlgebra.coeff H d)) - ∑ d ∈ H.support, AddMonoidAlgebra.coeff H d • v d =
        ∑ d ∈ H.support, C (AddMonoidAlgebra.coeff H d) * (monomial d (1 : K) - v d) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [mul_sub, C_mul_monomial, mul_one, smul_eq_C_mul]
    rw [e1, e2]
    exact Ideal.sum_mem _ fun d _ => Ideal.mul_mem_left _ _ (hvI d)

end

end GroundTheory.Heights₂.Heights.RestTerms
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvPolynomialReduction =====
