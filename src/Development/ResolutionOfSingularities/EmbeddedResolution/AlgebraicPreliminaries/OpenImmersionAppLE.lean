module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Combinatorics.Quiver.ReflQuiver
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

namespace AlgebraicGeometry

open CategoryTheory

universe u

namespace IsOpenImmersion

theorem bijective_appLE_of_image_eq {A B : Scheme.{u}} (f : A ⟶ B) [IsOpenImmersion f]
    (O : B.Opens) (S : A.Opens) (e : S ≤ f ⁻¹ᵁ O) (h : f ''ᵁ S = O) :
    Function.Bijective (CommRingCat.Hom.hom (Scheme.Hom.appLE f O S e)) := by
  subst h
  have : IsIso (Scheme.Hom.appLE f (f ''ᵁ S) S e) := by
    rw [← Scheme.Hom.appIso_hom' f S]
    infer_instance
  exact ConcreteCategory.bijective_of_isIso (Scheme.Hom.appLE f (f ''ᵁ S) S e)

end IsOpenImmersion

end AlgebraicGeometry
