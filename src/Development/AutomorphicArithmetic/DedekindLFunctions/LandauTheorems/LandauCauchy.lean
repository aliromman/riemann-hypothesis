module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Tactic.Linter.Style
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
public import Mathlib.Analysis.Complex.Liouville

@[expose] public section

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem landau_cauchy {Φ : ℂ → ℂ} {z : ℂ} {r r' : ℝ} (hd : DifferentiableOn ℂ Φ (Metric.ball z r))
    (h0 : 0 < r') (h1 : r' < r) :
    ∃ M : ℝ, ∀ k : ℕ, ‖iteratedDeriv k Φ z / (k.factorial : ℂ)‖ ≤ M / r' ^ k := by
  obtain ⟨M, hM⟩ := (isCompact_sphere z r').exists_bound_of_continuousOn
    (hd.continuousOn.mono (Metric.sphere_subset_ball h1))
  refine ⟨M, fun k => ?_⟩
  rw [norm_div, Complex.norm_natCast, div_le_iff₀ (by positivity), mul_comm, ← mul_div_assoc]
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k h0
    (hd.diffContOnCl_ball (Metric.closedBall_subset_ball h1)) hM

end Deduction

end
