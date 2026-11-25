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
  have hK : IsCompact (Metric.closedBall z r) := isCompact_closedBall z r
  have hpos : ∀ w ∈ Metric.closedBall z r, 0 < w.re := by
    intro w hw
    have h1 : ‖w - z‖ ≤ r := by simpa [dist_eq_norm] using hw
    have h2 : |(w - z).re| ≤ ‖w - z‖ := Complex.abs_re_le_norm _
    have h3 := (abs_le.mp (h2.trans h1)).1
    simp only [Complex.sub_re] at h3
    linarith
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun w => {v | v ∈ ({w}ᶜ : Set ℂ) → v ∉ Z})
    (fun w hw => eventually_nhdsWithin_iff.mp (hiso w (hpos w hw)))
  refine t.finite_toSet.subset ?_
  rintro v ⟨hvZ, hvK⟩
  obtain ⟨w, hw, hvw⟩ := Set.mem_iUnion₂.mp (ht hvK)
  by_cases h : v = w
  · rw [h]; exact hw
  · exact absurd hvZ (hvw h)

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
