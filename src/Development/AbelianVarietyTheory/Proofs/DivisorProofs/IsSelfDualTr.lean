module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
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

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.EqCovol

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def IsLevGrp {H : Host E} (l : Level H) {r : ℕ} (Y : Data E r) : Prop :=
  ∀ γ : GL (Fin r) E, γ ∈ Y.Γ ↔ IsUStab Y.Gm Y.Λ γ ∧
    (∀ x ∈ (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) • Y.Λ, ∃ y ∈ Y.Λ,
      (γ : Matrix (Fin r) (Fin r) E).mulVec x - x = l.M • y) ∧
    (∀ x ∈ Y.Λ, ∃ y ∈ Y.Λ, (γ : Matrix (Fin r) (Fin r) E).mulVec x - x = l.A • y)

def IsSelfDualTr {r : ℕ} (Y : Data E r) : Prop :=
  ∀ x : Fin r → E, x ∈ Y.Λ ↔ ∀ y ∈ Y.Λ, ∃ n : ℤ, Algebra.trace ℚ E (-Y.ξ0 * herm Y.Gm x y) = n

end GlobalTheory.EqCovol
