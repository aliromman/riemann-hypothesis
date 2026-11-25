module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.IsOpenAlt
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsVerticalDivOfIsVerticalDivisorAlt
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRat

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: GroundTheory.HeightsAndTheta.Heights.Intersections.AnalyticResolutionHypothesesProjectiveLine, GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothMetricOfIsSmoothHerm

-- ===== clump member: GroundTheory.HeightsAndTheta.Heights.Intersections.AnalyticResolutionHypothesesProjectiveLine =====
-- clump-header: {"m": "GroundTheory.HeightsAndTheta.Heights.Intersections.AnalyticResolutionHypothesesProjectiveLine", "h": "module\n\npublic import ReciprocityTheory.AnalyticForms.RegularLocalRings.IsOpenAlt\npublic import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily\npublic import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun\n\n"}
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial MeasureTheory Topology
open scoped ContDiff
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiHomog IsMultiHomogIdeal IsRelevant IsMultiProjPrime
  divCycle intNum)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection IsSNC HoloMap mInt MIntegrable
  logNormSec)

abbrev HLine {K : Type} [Fintype K] (ι : K → Type) := ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι

section Objects

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

abbrev MCone (ι : K → Type) := (Σ k, ι k) → ℂ


variable (ι) in
structure Res (P : Ideal (MRing ι ℂ)) (e : ℕ) where

  D : Ideal (MRing ι ℂ)
  homog : IsMultiHomogIdeal D
  not_le : ¬ D ≤ P

  R : ReciprocityTheory.AnForm.R.AlgRes ι P D e


def IsProjVarQ (P0 : Ideal (MRing ι ℚ)) (e : ℕ) : Prop :=
  IsMultiProjPrime P0 ∧ ringKrullDim (MRing ι ℚ ⧸ P0) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞)

end Objects

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.HeightsAndTheta.Heights.Intersections.AnalyticResolutionHypothesesProjectiveLine =====

-- ===== clump member: GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothMetricOfIsSmoothHerm =====
-- clump-header: {"m": "GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothMetricOfIsSmoothHerm", "h": "module\n\npublic import GroundTheory.HeightsAndTheta.Heights.Intersections.AnalyticResolutionHypothesesProjectiveLine\npublic import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsVerticalDivOfIsVerticalDivisorAlt\npublic import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRat\n\n"}
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing)

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]




theorem isProjVarQ_of_isArithVar {P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)} {e : ℕ}
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (e + 1)) :
    IsProjVarQ (P.map (MvPolynomial.map (Int.castRingHom ℚ))) e := by
  obtain ⟨-, ⟨hprime, ⟨S, hS, hPS⟩, hrel⟩, hhor, hdim⟩ := hP
  have := hprime
  have hch : ∀ m : ℤ, (C m : MvPolynomial (Σ k, ι k) ℤ) ∈ P → m = 0 := by
    intro m hm
    have hm' : m ∈ P.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) := Ideal.mem_comap.mpr hm
    rw [show P.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) = ⊥ from hhor, Ideal.mem_bot] at hm'
    exact hm'
  obtain ⟨hQ, hcomap, hd⟩ := ReciprocityTheory.AnForm.R.extQ_spec P hch
  refine ⟨(GroundTheory.Heights₂.Heights.NumbersDVR.Objects.isMultiProjPrime_iff _).mpr
    ⟨hQ, ⟨MvPolynomial.map (Int.castRingHom ℚ) '' S, ?_, ?_⟩, ?_⟩, ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, ha⟩ := hS f hf
    exact ⟨a, fun m hm k => ha m (MvPolynomial.support_map_subset _ _ hm) k⟩
  · rw [hPS, Ideal.map_span]
  · intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun h => hi ?_⟩
    rw [← hcomap, Ideal.mem_comap, MvPolynomial.map_X]
    exact h
  · have hd' : ringKrullDim (MvPolynomial (Σ k, ι k) ℚ ⧸
        P.map (MvPolynomial.map (Int.castRingHom ℚ))) + 1 =
        ((e + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      rw [← hdim]
      exact hd
    rw [Nat.add_right_comm e 1 (Fintype.card K), Nat.cast_add, Nat.cast_one] at hd'
    exact ENat.WithBot.add_one_cancel.mp hd'

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothMetricOfIsSmoothHerm =====
