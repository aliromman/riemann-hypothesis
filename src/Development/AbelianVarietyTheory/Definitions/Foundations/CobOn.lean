module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.ZMod.Defs
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
import Mathlib.Tactic.TypeStar

@[expose] public section

noncomputable section

namespace GlobalTheory.KEdge

variable {Γ : Type*} [Group Γ] {N : ℕ}

def edge (x y : Γ →* Multiplicative (ZMod N)) (η : Γ → ZMod N) (σ h : Γ) : ZMod N :=
  η (σ * h * σ⁻¹) - η h - (x h).toAdd * (y σ).toAdd + (x σ).toAdd * (y h).toAdd

def CobOn (Δ : Subgroup Γ) (x y : Γ →* Multiplicative (ZMod N)) (η : Γ → ZMod N) : Prop :=
  ∀ g ∈ Δ, ∀ h ∈ Δ, (x g).toAdd * (y h).toAdd = η h - η (g * h) + η g

end GlobalTheory.KEdge
