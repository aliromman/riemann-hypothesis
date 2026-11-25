module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GenTransl

variable {R : Type} [CommRing R] [IsDomain R] (G : Over (Sp R))

abbrev genOver : Over (Sp R) := Over.mk (pullback.snd G.hom (jK R) ≫ jK R)

def genPr : genOver G ⟶ G := Over.homMk (pullback.fst G.hom (jK R)) pullback.condition

def genPt (a : Over.mk (jK R) ⟶ G) : genOver G ⟶ G :=
  Over.homMk (pullback.snd G.hom (jK R) ≫ a.left) (by
    rw [Category.assoc, Over.w a]; rfl)

def IsGenTransl [GrpObj G] (L L₁ : LB G.left) (a : Over.mk (jK R) ⟶ G) : Prop :=
  LBIso (L₁.pull (pullback.fst G.hom (jK R))) (L.pull ((genPr G * genPt G a).left))

end GlobalTheory.GenTransl
