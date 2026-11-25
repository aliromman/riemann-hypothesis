module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FinCover
public import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupIsoOffCenter
public import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProper
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

open CategoryTheory Limits AlgebraicGeometry

theorem UpperTheory.Gal.KunnethLefschetz.G.blOff :
    UpperTheory.Gal.KunnethLefschetz.G.BlowUpOff := by
  intro R _ _ Z W _ _ π hπ
  have hdg : IsClosedImmersion (Over.Hom.left (UpperTheory.Gal.KunnethLefschetz.G.dg Z)) := by
    change IsClosedImmersion (pullback.diagonal (Over.hom Z))
    infer_instance
  have hft : LocallyOfFiniteType (Over.hom (UpperTheory.Gal.KunnethLefschetz.G.XX Z)) := by
    change LocallyOfFiniteType (pullback.fst (Over.hom Z) (Over.hom Z) ≫ Over.hom Z)
    infer_instance
  have hln : IsLocallyNoetherian (Over.left (UpperTheory.Gal.KunnethLefschetz.G.XX Z)) :=
    LocallyOfFiniteType.isLocallyNoetherian (Over.hom (UpperTheory.Gal.KunnethLefschetz.G.XX Z))
  have hsupp : ((Scheme.Hom.ker (Over.Hom.left (UpperTheory.Gal.KunnethLefschetz.G.dg Z))).support : Set _) =
      Set.range (Over.Hom.left (UpperTheory.Gal.KunnethLefschetz.G.dg Z)) := by
    rw [Scheme.Hom.support_ker]
    exact (Scheme.Hom.isClosedEmbedding (Over.Hom.left (UpperTheory.Gal.KunnethLefschetz.G.dg Z))).isClosed_range.closure_eq
  refine ⟨FunctorialResolution.Blowup.isProper_of_isBlowupAlongIdealSheaf hπ, ?_, ?_⟩
  · change IsClosedImmersion (pullback.fst (Over.Hom.left π) (Over.Hom.left (UpperTheory.Gal.KunnethLefschetz.G.dg Z)))
    infer_instance
  · intro U hU
    have hUeq : U = (Scheme.Hom.ker (Over.Hom.left (UpperTheory.Gal.KunnethLefschetz.G.dg Z))).support.compl := by
      apply SetLike.coe_injective
      rw [hU]
      simp [hsupp]
    subst hUeq
    refine ⟨FunctorialResolution.Blowup.blowupIsIsoOffCenter _ _ _ _ hπ, ?_⟩
    change _ = (Set.range (pullback.fst (Over.Hom.left π) (Over.Hom.left (UpperTheory.Gal.KunnethLefschetz.G.dg Z))))ᶜ
    rw [Scheme.Pullback.range_fst]
    simp [hsupp]
