module

public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.KernelFlatBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.InducedBlowupsFlatBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.StrictPullbackCriterion
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
import Mathlib.Tactic.Linter.Style
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
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.ChartFlatBaseChange

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

private theorem principalizationAlgorithm_toSequenceOfBlowups_congr_ideal (A : PrincipalizationAlgorithm.{u}) (k : Type u) [Field k] [CharZero k]
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p]
    (I J : X.IdealSheafData) (hIJ : I = J)
    (hI : NonzeroOnComponents I) (hJ : NonzeroOnComponents J)
    (E : List X.IdealSheafData) (hE hE' : InStrictNormalCrossingPosition p E) :
    (A k X p I hI E hE).toSequenceOfBlowups = (A k X p J hJ E hE').toSequenceOfBlowups := by
  subst hIJ
  rfl

private theorem isPullbackSequenceOfBlowups_congr_left {X X' : Scheme.{u}} {φ : X' ⟶ X}
    {s1 s2 : SequenceOfBlowups X'} {t : SequenceOfBlowups X} (h : s1 = s2) (H : IsPullbackBlowupSequence φ s1 t) :
    IsPullbackBlowupSequence φ s2 t := by
  subst h
  exact H

theorem embeddedResolutionRule_isPullbackBlowupSequence_of_smooth
    (A : PrincipalizationAlgorithm.{u}) (hA : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A)
    (k : Type u) [Field k] [CharZero k] (Y Y' : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) (p' : Y' ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType p] [AlgebraicGeometry.QuasiCompact p]
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.LocallyOfFiniteType p'] [AlgebraicGeometry.QuasiCompact p']
    [AlgebraicGeometry.IsReduced Y'] [AlgebraicGeometry.IsAffine Y']
    (D : EmbeddingDatum k Y p) (D' : EmbeddingDatum k Y' p')
    (φ : D'.ambient ⟶ D.ambient) [AlgebraicGeometry.Smooth φ] (ψ : Y' ⟶ Y)
    (hφ : φ ≫ D.ambientStruct = D'.ambientStruct)
    (hsq : IsPullback D'.emb ψ φ D.emb) :
    IsPullbackBlowupSequence ψ (embeddedResolutionRuleOfPrincipalization A hw k Y' p' D')
      (embeddedResolutionRuleOfPrincipalization A hw k Y p D) := by
  have : AlgebraicGeometry.Flat φ := inferInstance
  have : AlgebraicGeometry.QuasiCompact D.emb := inferInstance
  have : AlgebraicGeometry.QuasiCompact D'.emb := inferInstance
  have hker : D'.emb.ker = D.emb.ker.comap φ :=
    ker_eq_comap_ker_of_isPullback_of_flat hsq.flip
  have hI' : NonzeroOnComponents (D.emb.ker.comap φ) := hker ▸ D'.nonzeroOnComponents_ker
  have hE' : InStrictNormalCrossingPosition D'.ambientStruct
      (List.map (fun Z => Z.comap φ) ([] : List D.ambient.IdealSheafData)) := D'.sncEmpty
  have h0 := hA.smooth_pullback k D.ambient D.ambientStruct D.emb.ker
      D.nonzeroOnComponents_ker [] D.sncEmpty D'.ambient D'.ambientStruct φ hφ hI' hE'
  have hpb : IsPullbackBlowupSequence φ (D'.toEmbeddedBlowupSequence A).ambientSeq (D.toEmbeddedBlowupSequence A).ambientSeq := by
    rw [EmbeddingDatum.ambientBlowups_eq_toSequenceOfBlowups, EmbeddingDatum.ambientBlowups_eq_toSequenceOfBlowups]
    exact isPullbackSequenceOfBlowups_congr_left
      (principalizationAlgorithm_toSequenceOfBlowups_congr_ideal A k D'.ambient D'.ambientStruct
        (D.emb.ker.comap φ) D'.emb.ker hker.symm hI' _ [] hE' _) h0
  have hflat2 : AlgebraicGeometry.Flat
      (show (D'.toEmbeddedBlowupSequence A).ambient ⟶ (D.toEmbeddedBlowupSequence A).ambient from φ) :=
    (inferInstance : AlgebraicGeometry.Flat φ)
  rw [embeddedResolutionRuleOfPrincipalization_apply, embeddedResolutionRuleOfPrincipalization_apply]
  exact (chartFlatBaseChangeOfIsPullbackSeq (D.toEmbeddedBlowupSequence A) (D'.toEmbeddedBlowupSequence A) φ ψ
    hsq.flip hpb).isPullbackBlowupSequence_inducedBlowupsWithoutIso _ _

theorem embeddedResolutionRule_isCompatibleWithSmoothAmbientMaps
    (A : PrincipalizationAlgorithm.{u}) (hA : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A) :
    EmbeddedResolutionRule.IsCompatibleWithSmoothAmbientMaps (embeddedResolutionRuleOfPrincipalization A hw) := by
  intro k _ _ Y Y' p p' _ _ _ _ _ _ _ _ D D' φ _ ψ hφ hsq
  exact embeddedResolutionRule_isPullbackBlowupSequence_of_smooth A hA hw k Y Y' p p' D D' φ ψ hφ hsq

end FunctorialResolution.EmbeddedResolution
