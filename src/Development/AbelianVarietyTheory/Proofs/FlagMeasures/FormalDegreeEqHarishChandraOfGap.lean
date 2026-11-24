module

public import Formalism.LocalRingCardinality.DataTies
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLitG
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HarishChandraFormalDegreeCompactDualLargeGaps
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.DegIUp
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.FinalClosed
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

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory

theorem dsig_eq_fdegHC_of_gap : ∀ (D : D7), Ties D → ∀ (τ : D.what₂.Tau) (h : ℝ),
    Formalism.QuantumDeterminants.IsHCParam (lamSH D.R (D.hc τ)) → Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) (lamSH D.R (D.hc τ)) h →
    Formalism.MainNotions.GapDS.thrE (epsSH D.R) + 1 < h → D.dsig τ = Formalism.QuantumDeterminants.fdegHC (lamSH D.R (D.hc τ)) := by
  intro D hT τ h hlam hg hth
  have hth' : Formalism.MainNotions.GapDS.thrE (epsSH D.R) < h :=
    lt_trans (lt_add_of_pos_right _ zero_lt_one) hth
  obtain ⟨H, i1, i2, σ, hσ, -⟩ := ReciprocityTheory.ChartRestriction.DS.dsExistsG_closed _ (epsSH D.R) _ hlam h hg hth'
  have hpq := Formalism.MainNotions.S.Pv.DegI.minpq_pos D
  have hp : 1 ≤ ReciprocityTheory.ChartRestriction.DS.pOf (epsSH D.R) := le_trans hpq (min_le_left _ _)
  have hq : 1 ≤ ReciprocityTheory.ChartRestriction.DS.qOf (epsSH D.R) := le_trans hpq (min_le_right _ _)
  have htrue : ∃ a, epsSH D.R a = true := by
    unfold ReciprocityTheory.ChartRestriction.DS.pOf at hp
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (Nat.lt_of_lt_of_le Nat.zero_lt_one hp)
    exact ⟨a, (Finset.mem_filter.mp ha).2⟩
  have hfalse : ∃ a, epsSH D.R a = false := by
    unfold ReciprocityTheory.ChartRestriction.DS.qOf at hq
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (Nat.lt_of_lt_of_le Nat.zero_lt_one hq)
    exact ⟨a, (Finset.mem_filter.mp ha).2⟩
  have hd := _root_.GlobalTheory.FdegGap.fdeg_gap D.cd D.s.cdScale hT.cdScale_tie _ (epsSH D.R) _ h hlam htrue hfalse hg hth H σ hσ
  exact (hT.dsig_tie τ H σ _ hσ hd).symm

end GlobalTheory
