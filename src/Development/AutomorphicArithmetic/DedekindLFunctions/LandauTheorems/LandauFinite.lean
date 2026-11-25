module

public import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.Height.NumberField
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

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem landau_finite {Z : Set ℂ} (hiso : ∀ z : ℂ, 0 < z.re → ∀ᶠ w in 𝓝[≠] z, w ∉ Z) {z : ℂ} {r : ℝ}
    (hr : r < z.re) : (Z ∩ Metric.closedBall z r).Finite := by
  by_contra h
  obtain ⟨w, hw, hacc⟩ := Set.Infinite.exists_accPt_of_subset_isCompact h
    (isCompact_closedBall z r) Set.inter_subset_right
  have hwpos : 0 < w.re := by
    simpa [Complex.sub_re] using
      (Complex.re_le_norm (z - w)).trans_lt ((mem_closedBall_iff_norm'.1 hw).trans_lt hr)
  exact ((accPt_iff_frequently_nhdsNE.mp hacc).mono fun _ hy => hy.1) (hiso w hwpos)

/-- If `d < cap` and `d < f w` for every `w` in the finite set `S`, some `r` with `d < r ≤ cap` is
at most every `f w`. Taking the minimum over `S` together with `cap` covers the case where `S` is
empty. -/
theorem exists_capped_radius {α : Type*} {S : Set α} (hS : S.Finite) (f : α → ℝ)
    {d cap : ℝ} (hcap : d < cap) (h : ∀ w ∈ S, d < f w) :
    ∃ r, d < r ∧ r ≤ cap ∧ ∀ w ∈ S, r ≤ f w := by
  obtain ⟨r, hr, hmin⟩ := Set.exists_min_image (insert cap (f '' S)) id
    ((hS.image f).insert cap) ⟨cap, by simp⟩
  refine ⟨r, ?_, hmin cap (by simp), fun w hw => hmin (f w) (Set.mem_insert_of_mem _ ⟨w, hw, rfl⟩)⟩
  rcases Set.mem_insert_iff.mp hr with rfl | ⟨w, hw, rfl⟩
  · exact hcap
  · exact h w hw

end Deduction

end
