module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HasQExpansionModularForm
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

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam

theorem HasQ.coeff_unique {N : ℕ} {f : ℍ → ℂ} {a b : ℕ → ℂ} (hN : 0 < N) (ha : HasQ N f a)
    (hb : HasQ N f b) : a = b := by
  have toSeries : ∀ c : ℕ → ℂ, HasQ N f c → GlobalTheory.HasQExpansion (N : ℝ) f (PowerSeries.mk c) := by
    intro c hc τ
    have hs := (hasQ_iff N f c).1 hc τ
    simpa [PowerSeries.coeff_mk, Function.Periodic.qParam] using hs
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hab := GlobalTheory.HasQExpansion.unique hN' (toSeries a ha) (toSeries b hb)
  funext n
  simpa using congrArg (PowerSeries.coeff n) hab

theorem HasQ.fun_unique {N : ℕ} {f g : ℍ → ℂ} {a : ℕ → ℂ} (hf : HasQ N f a) (hg : HasQ N g a) :
    f = g := by
  funext τ
  exact (hf τ).unique (hg τ)

theorem hasQ_unique_both :
    (∀ (N : ℕ) (f : ℍ → ℂ) (a b : ℕ → ℂ), 0 < N → HasQ N f a → HasQ N f b → a = b) ∧
    (∀ (N : ℕ) (f g : ℍ → ℂ) (a : ℕ → ℂ), HasQ N f a → HasQ N g a → f = g) :=
  ⟨fun _ _ _ _ hN ha hb => HasQ.coeff_unique hN ha hb, fun _ _ _ _ hf hg => HasQ.fun_unique hf hg⟩

end GlobalTheory.QFam
