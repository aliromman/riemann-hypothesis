module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DualCon

def LiftsAlong {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {U : Over (Sp R)} (M : LB (A ⊗ U).left)
    (B : Type) [CommRing B] (I : Ideal B) : Prop :=
  ∀ (T : Over (Sp R)) (N : LB (A ⊗ T).left), Fam A N → ∀ (y : Spec (CommRingCat.of B) ⟶ T.left)
    (u₀ : Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ y ≫ T.hom) ⟶ U),
    Same A N M (Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ y) (by simp) :
      Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ y ≫ T.hom) ⟶ T) u₀ →
    ∃ u : Over.mk (y ≫ T.hom) ⟶ U, Same A N M (Over.homMk y rfl : Over.mk (y ≫ T.hom) ⟶ T) u

end GlobalTheory.DualCon
