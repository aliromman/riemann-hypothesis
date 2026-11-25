module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
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
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

namespace GlobalTheory

theorem eq_of_nodup_sum_multiset_of_eq (ι : Type) [Fintype ι] [DecidableEq ι]
    (B : ι → Multiset ℂ) (h : (∑ i, B i).Nodup) (i j : ι) (hi : B i ≠ 0) (hij : B i = B j) :
    i = j := by
  by_contra hne
  have hle : B i + B j ≤ ∑ k, B k := by
    rw [← Finset.sum_pair hne]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hnd : (B i + B j).Nodup := Multiset.nodup_of_le hle h
  rw [← hij] at hnd
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hi
  exact Multiset.disjoint_left.1 (Multiset.nodup_add.1 hnd).2.2 ha ha

end GlobalTheory
