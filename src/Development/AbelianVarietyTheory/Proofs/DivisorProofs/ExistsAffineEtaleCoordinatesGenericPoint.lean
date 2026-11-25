module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordinateNearGenericPoint
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

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points

namespace GlobalTheory.GenericCoords

theorem exists_affine_etale_coords : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp k} {D : ℕ}, IsArithVar p D → ∃ U : X.Opens, IsAffineOpen U ∧ genericPoint X ∈ U ∧
      ∃ t : Fin D → Γ(X, U), (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U) t).Etale := by
  intro k _ X _ p D h
  obtain ⟨U, t, hU, hη, he⟩ := GlobalTheory.GenericEtale.exists_etale_coords h
  exact ⟨U, hU, hη, t, he⟩

end GlobalTheory.GenericCoords
