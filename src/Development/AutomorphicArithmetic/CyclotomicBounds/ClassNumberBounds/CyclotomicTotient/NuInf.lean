module

public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.RingTheory.SimpleRing.Principal
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

namespace KStar.Tree

variable {Γ : Type} [Group Γ] (l : ℕ) [Fact l.Prime] (ε : Γ →* ℤ_[l]ˣ) (n : ℕ)

def nuOf : ℕ := sInf {k : ℕ | ∃ g, ¬ (l : ℤ_[l]) ^ (k + 1) ∣ ((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1}

def cyc (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] : (Ω ≃ₐ[E] Ω) →* ℤ_[l]ˣ :=
  (cyclotomicCharacter Ω l).comp (MulSemiringAction.toRingAut (Ω ≃ₐ[E] Ω) Ω)

end KStar.Tree
