module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace GlobalTheory.AffineThickening

theorem exists_isAffineOpen_preimage_eq_of_isNilpotent (A A' : Type) [CommRing A] [CommRing A']
    (g : A →+* A') (hg : Function.Surjective g) (hn : IsNilpotent (RingHom.ker g))
    (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)) (f' : X' ⟶ Spec (CommRingCat.of A'))
    (β : X' ⟶ X) (h : IsPullback β f' f (Spec.map (CommRingCat.ofHom g)))
    (D' : X'.Opens) (hD' : IsAffineOpen D') :
    ∃ D : X.Opens, IsAffineOpen D ∧ β ⁻¹ᵁ D = D' := by
  have h1 := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom g) hg
  have : IsClosedImmersion β := MorphismProperty.of_isPullback h.flip h1
  obtain ⟨O, hO, hO'⟩ := β.isClosedEmbedding.isInducing.isOpen_iff.mp D'.isOpen
  have e : β ⁻¹ᵁ ⟨O, hO⟩ = D' := Opens.ext hO'
  refine ⟨⟨O, hO⟩, ?_, e⟩
  subst e
  exact isAffine_of_isPullback_of_isNilpotent (RingHom.ker g) hn (CommRingCat.ofHom g) hg rfl
    ((isPullback_morphismRestrict β ⟨O, hO⟩).paste_vert h) hD'

end GlobalTheory.AffineThickening
