module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen
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

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.OrVert

def DomBy {X : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] (W : Subring Ω') (i : Ω →+* Ω')
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (q : Cpt ξ) : Prop :=
  (∀ a ∈ regAt ξ q, i a ∈ W) ∧ ∀ a ∈ regAt ξ q, a ≠ 0 → (i a)⁻¹ ∈ W → a⁻¹ ∈ regAt ξ q

end GlobalTheory.CompanionTheory.Ar.OrVert
