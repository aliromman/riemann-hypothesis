module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
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

namespace GlobalTheory.CompanionTheory.Ar.GeoModel

open AlgebraicGeometry CategoryTheory
open GlobalTheory.CompanionTheory.Ar.SncBase

def SncPts {X : Scheme.{0}} {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (e : ℕ)
    (B : Set (Cpt ξ)) : Prop :=
  ∀ p, Char0 ξ p → ∃ (A : Subalgebra ℚ Ω) (z : Fin e → A) (n : ℕ) (q : Ideal A),
    IsSncPatch (Pts ξ) (regAt ξ '' B) e A z n ∧ q.IsPrime ∧ IsLocAt A q (regAt ξ p)

end GlobalTheory.CompanionTheory.Ar.GeoModel
