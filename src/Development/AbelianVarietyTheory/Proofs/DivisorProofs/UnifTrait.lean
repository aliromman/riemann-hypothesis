module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
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

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.Mum

def UnifTrait {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (G : Over (Sp R))
    [GrpObj G] (L : LB G.left) : Prop :=
  ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W) (G' : Over (Sp W)) (_ : GrpObj G')
    (_ : IsCommMonObj G') (β : G'.left ⟶ G.left) (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W)))
    (U' : Unif (maximalIdeal W) D' A' G'), GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧
      IsGrpPullback G' G (spMap φ) β ∧ LBIso U'.LG.L (L.pull β) ∧ Nonempty (IsPullDeg φ D.toPre D'.toPre)

end GlobalTheory.Mum
