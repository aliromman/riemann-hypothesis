module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomOfFlatQuotientOfAffineKernel
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

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory


open CategoryTheory Limits AlgebraicGeometry in
theorem _root_.GlobalTheory.isAffineHom_of_isAffineHom_pullback_snd_of_fpqc :
    ∀ (X Y Y' : Scheme.{0}) (f : X ⟶ Y) (g : Y' ⟶ Y), Surjective g → Flat g → QuasiCompact g →
      IsAffineHom (pullback.snd f g) → IsAffineHom f := by
  intro X Y Y' f g hs hf hq h
  haveI := _root_.GlobalTheory.isAffineHom_descendsAlong_fpqc
  exact MorphismProperty.DescendsAlong.of_isPullback (P := @IsAffineHom)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (IsPullback.of_hasPullback f g).flip
    ⟨⟨hs, hf⟩, hq⟩ h

end GlobalTheory
