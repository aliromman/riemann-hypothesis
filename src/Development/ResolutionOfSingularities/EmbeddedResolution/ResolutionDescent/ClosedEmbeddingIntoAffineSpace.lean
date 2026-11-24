module

public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCoordinateCodimension
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRule
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

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

structure ClosedEmbeddingIntoAffineSpace {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    {p : Y ⟶ Spec (CommRingCat.of k)} (G : EmbeddingDatum k Y p) where
  codimBound : ℕ
  dim : ℕ
  toAffine : G.ambient ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin dim))
  one_le_codimBound : 1 ≤ codimBound
  one_le_dim : 1 ≤ dim
  isClosedImmersion_toAffine : AlgebraicGeometry.IsClosedImmersion toAffine
  toAffine_comp : toAffine ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin dim)) = G.ambientStruct
  locallyConstCodim :
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u} (Fin dim))) toAffine codimBound

namespace ClosedEmbeddingIntoAffineSpace

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
  {p : Y ⟶ Spec (CommRingCat.of k)} {G : EmbeddingDatum k Y p}

instance instIsClosedImmersionToAffine (P : ClosedEmbeddingIntoAffineSpace G) :
    AlgebraicGeometry.IsClosedImmersion P.toAffine :=
  P.isClosedImmersion_toAffine

end ClosedEmbeddingIntoAffineSpace

def EmbeddedResolutionRule.IsIndependentOfPresentedEmbedding (R : EmbeddedResolutionRule.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y] (D D' : EmbeddingDatum k Y p),
    ClosedEmbeddingIntoAffineSpace D → ClosedEmbeddingIntoAffineSpace D' →
    (R k Y p D).Isomorphic (R k Y p D')

end FunctorialResolution.EmbeddedResolution

end
