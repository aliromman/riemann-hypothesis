module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.Pinch

def IsSecFam {X : Scheme.{0}} (L : LB X) {J : Type} (D : J → X.Opens) (k : J → L.ι)
    (hD : ∀ j, D j ≤ L.U (k j)) (e : ∀ j, Γ(X, D j)) : Prop :=
  ∀ (j j' : J) (z : X) (hz : z ∈ D j) (hz' : z ∈ D j'),
    (X.presheaf.germ (D j) z hz).hom (e j) =
      (X.presheaf.germ (L.U (k j) ⊓ L.U (k j')) z ⟨hD j hz, hD j' hz'⟩).hom (L.g (k j) (k j')).val *
        (X.presheaf.germ (D j') z hz').hom (e j')

end GlobalTheory.Pinch
