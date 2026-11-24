module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecTExists
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
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

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL

namespace GlobalTheory.RecT

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GoodCusp.tw {y : IrrGL (k := k)} (hy : GoodCusp y) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    GoodCusp (y.tw χ hχ) := by
  rcases hy with h1 | ⟨hf, y₀, χ₀, hχ₀, hfix, rfl⟩
  · exact Or.inl h1
  · exact Or.inr ⟨hf, y₀, χ₀ * χ, hχ₀.mul hχ, hfix, IrrGL.tw_tw _ _ _ _ _⟩

theorem Good.tw {x : IrrGL (k := k)} (hx : Good x) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : Good (x.tw χ hχ) := by
  obtain ⟨s, hs, hg⟩ := hx
  refine ⟨s.map (·.tw χ hχ), (hs.tw χ hχ).of_equiv (x.twEquiv χ hχ), ?_⟩
  intro y hy
  obtain ⟨y', hy', rfl⟩ := Multiset.mem_map.1 hy
  exact (hg y' hy').tw χ hχ

theorem good_tw_iff (x : IrrGL (k := k)) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : Good (x.tw χ hχ) ↔ Good x :=
  ⟨fun h => by simpa only [IrrGL.tw_tw_inv] using h.tw χ⁻¹ hχ.inv, fun h => h.tw χ hχ⟩

theorem good_nu_iff (x : IrrGL (k := k)) (s : ℂ) : Good (x.nu s) ↔ Good x := good_tw_iff x _ _

end GlobalTheory.RecT

end
