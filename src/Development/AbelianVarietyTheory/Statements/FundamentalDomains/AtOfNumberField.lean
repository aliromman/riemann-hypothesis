module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
public import Mathlib.NumberTheory.NumberField.Basic
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow

noncomputable section
namespace GlobalTheory.KeyKa

def ConnFam : Prop :=
  ∀ x : KeyIn ℂ, ∃ (k : Type) (_ : Field k) (_ : NumberField k) (S : Type) (_ : CommRing S) (_ : Algebra k S)
    (y : KeyIn S) (s : S →+* ℂ) (s₀ : S →ₐ[k] k) (t₀ : k), Algebra.Smooth k S ∧
    (∀ (K : Type) [Field K] [Algebra k K], IsDomain (TensorProduct k K S)) ∧ KeyPB x y s ∧
    ∀ (e : k →+* ℂ) (x₀ : KeyIn ℂ), KeyPB x₀ y (e.comp s₀.toRingHom) →
      (∃ (τ M : Matrix (Fin x₀.P.g) (Fin x₀.P.g) ℂ) (a b : Fin x₀.P.g → ℂ) (c : ℂ),
        charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x₀ τ M a b c ∧ e t₀ = M.det ^ 4 / c ^ 8)

namespace ConnFamTest

end ConnFamTest
end GlobalTheory.KeyKa
end
