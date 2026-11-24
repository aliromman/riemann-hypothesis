module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
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

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.Amb

variable {k : Type} [CommRing k]

def PolyCovered {X : Scheme.{0}} (f : X ⟶ Sp k) (d : ℕ) : Prop :=
  ∃ ξ : X, (∀ y : Sp k, f ξ ⤳ y) ∧ ∀ x : X, ∃ (σ : Type) (_ : Fintype σ) (e : Sp (MvPolynomial σ k) ⟶ X), IsOpenImmersion e ∧
    Fintype.card σ = d ∧ e ≫ f = spMap (MvPolynomial.C : k →+* MvPolynomial σ k) ∧
    x ∈ Set.range e ∧ ξ ∈ Set.range e

end GlobalTheory.Amb
