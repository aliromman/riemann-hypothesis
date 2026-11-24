module

public import Formalism.IncomingBounds.IncomingBound
public import Formalism.IncomingBounds.FlowDegreeBounds.MaxFlowValueAttained
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

open scoped BigOperators
open Formalism.IncomingBounds

theorem UpperTheory.exists_maxFlow_attained_and_isOptDual :
    ∀ (l d : ℕ) [NeZero d], 3 ≤ l → ∀ D : ZMod d → ℝ, 0 ≤ D →
    (∃ x, IsFlow l d D x ∧ flowVal d x = maxFlow l d D) ∧ ∃ sig, IsOptDual l d D sig := by
  intro l d _ hl D hD
  have hl1 : 1 ≤ l := by omega
  obtain ⟨x, hx, hmax⟩ := FlowLoadBounds.exists_opt_flow hl1 D hD
  obtain ⟨σ, hσ, hsum⟩ := FlowLoadBounds.strong hl1 D hD
  refine ⟨⟨x, hx, (FlowLoadBounds.maxFlow_eq hx hmax).symm⟩, σ, hσ, ?_⟩
  rw [Fnum, ← hsum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring
