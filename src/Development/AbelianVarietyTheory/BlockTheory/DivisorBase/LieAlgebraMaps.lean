module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StAvDefs
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

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs

namespace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps

section Lie

variable {R : Type} [CommRing R]

abbrev torus (R : Type) [CommRing R] (r : ℕ) : Over (Spec (CommRingCat.of R)) :=
  splitTorus (Spec (CommRingCat.of R)) (Fin r → ℤ)

end Lie

abbrev baseChange (R A : Type) [CommRing R] [CommRing A] [Algebra R A] :
    Over (Spec (CommRingCat.of R)) ⥤ Over (Spec (CommRingCat.of A)) :=
  Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))

end GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps
