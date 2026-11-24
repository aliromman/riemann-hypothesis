module

public import Mathlib.NumberTheory.LocalField.Basic
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
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.LocalFieldPow


open ValuativeRel in
theorem exists_unit_pow_tendsto_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], ∃ t : kˣ, Tendsto (fun n : ℕ => (t : k) ^ n) atTop (𝓝 0) := by
  intro k _ _ _ _
  obtain ⟨r, hr0, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := ValuativeRel.valuation k)
  have hr : r ≠ 0 := by simpa using hr0
  have : MulArchimedean (ValuativeRel.ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  refine ⟨Units.mk0 r hr, ?_⟩
  rw [(IsValuativeTopology.hasBasis_nhds_zero' k).tendsto_right_iff]
  intro γ hγ
  obtain ⟨m, hm⟩ := exists_pow_lt₀ hr1 (Units.mk0 γ hγ)
  rw [Units.val_mk0] at hm
  filter_upwards [eventually_ge_atTop m] with n hn
  have h : ValuativeRel.valuation k ((Units.mk0 r hr : kˣ) : k) ^ n ≤ ValuativeRel.valuation k r ^ m := by
    simpa using pow_le_pow_of_le_one zero_le' hr1.le hn
  simpa using lt_of_le_of_lt h hm

end GlobalTheory.CompanionTheory.LocalFieldPow
