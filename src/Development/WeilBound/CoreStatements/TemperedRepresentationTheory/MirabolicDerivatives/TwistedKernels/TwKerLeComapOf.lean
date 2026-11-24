module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Basic.Complex.Basic
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

open GlobalTheory.PRep

namespace GlobalTheory.BZMir

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem twKer_le_comap_of (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (N : Subgroup G) (θ : N →* ℂˣ)
    (f : V →ₗ[ℂ] W) (hf : ∀ g v, f (ρ g v) = σ g (f v)) : twKer ρ N θ ≤ (twKer σ N θ).comap f := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨n, v, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap]
  refine Submodule.subset_span ⟨n, f v, ?_⟩
  rw [map_sub, map_smul, hf]

def twMap (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (N : Subgroup G) (θ : N →* ℂˣ)
    (f : V →ₗ[ℂ] W) (hf : ∀ g v, f (ρ g v) = σ g (f v)) : TwJacquet ρ N θ →ₗ[ℂ] TwJacquet σ N θ :=
  (twKer ρ N θ).mapQ (twKer σ N θ) f (twKer_le_comap_of ρ σ N θ f hf)

end GlobalTheory.BZMir

end
