module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Tactic.Linter.HaveILetI
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

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace GlobalTheory

theorem isPullback_fromSpec_app_preimage_of_affine {X T : Scheme.{0}} (p : X ⟶ T) {U : T.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen (p ⁻¹ᵁ U)) :
    IsPullback hV.fromSpec (Spec.map (p.app U)) p hU.fromSpec :=
  (IsOpenImmersion.isPullback _ _ _ _ (by
    rw [Scheme.Hom.app_eq_appLE, IsAffineOpen.SpecMap_appLE_fromSpec p hU hV]) (by simp)).flip

end GlobalTheory
