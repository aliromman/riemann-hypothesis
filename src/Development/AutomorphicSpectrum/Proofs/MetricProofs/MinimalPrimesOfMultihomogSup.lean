module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.MemConePtsIffChartIdeal
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CycDim
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.MinHom

open MvPolynomial ReciprocityTheory.AnForm.R

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem isMultiHomogIdeal_of_mem_minimalPrimes_sup :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)),
      IsMultiHomogIdeal P → IsMultiHomogIdeal D →
        ∀ Q ∈ (P ⊔ D).minimalPrimes, IsMultiHomogIdeal Q := by
  intro K _ ι _ P D hP hD Q hQ
  classical
  have toGeo : ∀ I : Ideal (MvPolynomial (Σ k, ι k) ℂ), IsMultiHomogIdeal I →
      ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal (R := ℂ) (ι := ι) I := fun I h => h
  have hQ' : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal (R := ℂ) (ι := ι) Q :=
    ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isMultiHomogIdeal_of_isHomogeneous fun k =>
      ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isHomogeneous_of_mem_minimalPrimes _
        ((ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isHomogeneous_of_isMultiHomogIdeal (toGeo P hP) k).sup
          (ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isHomogeneous_of_isMultiHomogIdeal (toGeo D hD) k)) hQ
  exact hQ'

end GlobalTheory.CompanionTheory.Ar.Cmp.MinHom
