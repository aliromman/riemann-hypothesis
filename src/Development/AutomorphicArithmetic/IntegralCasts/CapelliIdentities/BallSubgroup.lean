module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.MetricSpace.Ultra.Basic
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
public import Mathlib.Analysis.Normed.Group.Ultra

@[expose] public section

noncomputable def UpperTheory.Reformulated.B.BallSubgroup.ball :
    (L : Type) → [inst : NontriviallyNormedField L] → [IsUltrametricDist L] → ValuationSubring L :=
  fun L _ _ =>
    { carrier := {x : L | ‖x‖ ≤ 1}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [norm_mul]
        exact mul_le_one₀ ha (norm_nonneg b) hb
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        rwa [norm_neg]
      mem_or_inv_mem' := fun x => by
        simp only [Set.mem_setOf_eq]
        rcases le_total ‖x‖ 1 with h | h
        · exact Or.inl h
        · right
          rw [norm_inv]
          exact inv_le_one_of_one_le₀ h }
