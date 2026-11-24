module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
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

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E]
  {ξ : Spec (CommRingCat.of Ω) ⟶ X}

def IsCoeffAt (A B : Lat ξ E) (p q : ℕ) (a : ⋀[Ω]^p E) (b : ⋀[Ω]^q E) (x : Cpt ξ) (f : Ω) : Prop :=
  ∃ α β : Ω, α ≠ 0 ∧ β ≠ 0 ∧ A.wedge p x = Submodule.span (regAt ξ x) {α • a} ∧
    B.wedge q x = Submodule.span (regAt ξ x) {β • b} ∧ f * α = β

def IsLineGenOn (A B : Lat ξ E) (p q : ℕ) (a : ⋀[Ω]^p E) (b : ⋀[Ω]^q E) (T : Set (Cpt ξ)) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ ∀ x ∈ T, IsCoeffAt A B p q a b x 1

end GlobalTheory.CompanionTheory.Ar.Flat
