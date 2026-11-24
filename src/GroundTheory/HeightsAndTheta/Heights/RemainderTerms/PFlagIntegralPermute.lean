module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.FlagBasic
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
-- Members: GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagIntegralAntisymmetrize, GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagIntegralPermute

-- ===== clump member: GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagIntegralAntisymmetrize =====
-- clump-header: {"m": "GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagIntegralAntisymmetrize", "h": "module\n\npublic import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag\nimport GroundTheory.HeightsAndTheta.Heights.RemainderTerms.FlagBasic\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

noncomputable section

theorem flagIntegral_sum_smul_blockPermute (f N : ℕ) (H : RootRing f N)
    (s : Finset (Fin f → Equiv.Perm (Fin N))) :
    flagIntegral f N (∑ w ∈ s, blockSign f N w • blockPermute f N w H) =
      ∑ w ∈ s, blockSign f N w * flagIntegral f N (blockPermute f N w H) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Flag.flagIntegral_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Flag.flagIntegral_add, ih, smul_eq_C_mul,
      Flag.flagIntegral_C_mul]

theorem FlagIntegralAntisymmetrize.proof (h1 : FlagIntegralPermute.Statement) :
    FlagIntegralAntisymmetrize.Statement := by
  intro f N H
  rw [antisymmetrize, flagIntegral_sum_smul_blockPermute]
  rw [Finset.sum_congr rfl fun w _ => by
    rw [h1 f N w H, ← mul_assoc, Flag.blockSign_mul_self, one_mul]]
  rw [Finset.sum_const, Finset.card_univ, Flag.card_blockPerm, nsmul_eq_mul]
  push_cast
  ring

end

end RestTerms

end GroundTheory.Heights₂.Heights
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagIntegralAntisymmetrize =====

-- ===== clump member: GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagIntegralPermute =====
-- clump-header: {"m": "GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagIntegralPermute", "h": "module\n\npublic import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag\nimport GroundTheory.HeightsAndTheta.Heights.RemainderTerms.FlagBasic\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

theorem FlagIntegralPermute.proof (h1 : FlagCoeffBlockPermute.Statement) :
    FlagIntegralPermute.Statement := by
  classical
  intro f N w H
  let e : Fin f × Fin N ≃ Fin f × Fin N := Equiv.prodShear (Equiv.refl _) w
  have hcomp : ∀ α : Fin f × Fin N →₀ ℕ,
      (Finsupp.equivFunOnFinite.symm fun p : Fin f × Fin N => α (p.1, w p.1 p.2)) =
        Finsupp.equivMapDomain e.symm α := by
    intro α; ext p; simp [Finsupp.equivMapDomain_apply, e, Equiv.prodShear]
  have hH : ∀ α, AddMonoidAlgebra.coeff (blockPermute f N w H) α = AddMonoidAlgebra.coeff H (Finsupp.equivMapDomain e.symm α) := by
    intro α; rw [h1, hcomp]
  have hD : ∀ α, AddMonoidAlgebra.coeff (blockVandermonde f N) (Finsupp.equivMapDomain e.symm α) =
      blockSign f N w * AddMonoidAlgebra.coeff (blockVandermonde f N) α := by
    intro α
    rw [← hcomp, ← h1, Flag.blockPermute_blockVandermonde, MvPolynomial.coeff_smul, smul_eq_mul]
  have hs2 : blockSign f N w * blockSign f N w = 1 := Flag.blockSign_mul_self f N w
  have hs0 : blockSign f N w ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hs2; exact zero_ne_one hs2
  have hfac : ∀ α : Fin f × Fin N →₀ ℕ,
      (Finsupp.equivMapDomain e.symm α).prod (fun _ n => (n.factorial : ℚ)) =
        α.prod (fun _ n => (n.factorial : ℚ)) := by
    intro α; rw [Finsupp.prod_equivMapDomain]
  unfold flagIntegral
  rw [Finset.mul_sum]
  refine Finset.sum_equiv (Finsupp.domCongr e.symm).toEquiv (fun α => ?_) (fun α _ => ?_)
  · simp only [MvPolynomial.mem_support_iff, AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv,
      Finsupp.domCongr_apply, hD]
    exact ⟨fun h => mul_ne_zero hs0 h, fun h h' => h (by rw [h', mul_zero])⟩
  · simp only [AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv, Finsupp.domCongr_apply, hH, hD, hfac]
    linear_combination (-(AddMonoidAlgebra.coeff H (Finsupp.equivMapDomain e.symm α) *
      AddMonoidAlgebra.coeff (blockVandermonde f N) α * α.prod (fun _ n => (n.factorial : ℚ)))) * hs2

end RestTerms

end GroundTheory.Heights₂.Heights
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagIntegralPermute =====
