module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DerivedAndCoverTriples
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

namespace FunctorialResolution.EmbeddedResolution

namespace MaxContactCoverData

theorem surjective_coverMap (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (h : ∃ D : MaxContactReduction.FiniteOpenCoverWithIdeals T,
      MaxContactReduction.IsMaxContactCover T D hv.locallyOfFiniteType (balancedTunedIdeal T hv) (tunedMult T)) :
    Surjective (coverMap T hv) := by
  have hc := (isMaxContactCover_chosenCoverData T hv h).covers
  rw [coverMap_eq_sigmaOpensDesc]
  exact surjective_sigmaOpensDesc T.scheme (chosenCoverData T hv).opens hc

end MaxContactCoverData

end FunctorialResolution.EmbeddedResolution
