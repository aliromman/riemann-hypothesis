module

public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
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

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def StrictNormalCrossingsRestrictToClopen : Prop :=
  ∀ (k : Type u) [Field k] (W : Scheme.{u}) (p : W ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] (E : List W.IdealSheafData) (Z : W.IdealSheafData),
    InStrictNormalCrossingPosition p E → HasStrictNormalCrossingsWith p Z E →
    ∀ U : (Z.subscheme).Opens, IsClosed (U : Set ↥(Z.subscheme)) →
    (∀ D ∈ E, ∀ T ∈ irreducibleComponents (↥(U.toScheme)),
        ¬ ((U.ι ≫ Z.subschemeι).base '' T) ⊆ (D.support : Set ↥W)) →
    IsStrictNormalCrossingsDivisor ((E.prod.comap (U.ι ≫ Z.subschemeι)).radical)

end FunctorialResolution.EmbeddedResolution
