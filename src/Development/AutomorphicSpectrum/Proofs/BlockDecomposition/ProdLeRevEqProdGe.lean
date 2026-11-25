module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
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
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace GlobalTheory.CompanionTheory.FinReversal

theorem prod_filter_le_rev {M : Type*} [CommMonoid M] (h : ℕ) (f : Fin h → M) (j : Fin h) :
    ∏ a ∈ Finset.univ.filter (fun a => a ≤ j), f (Fin.rev a)
      = ∏ i ∈ Finset.univ.filter (fun i => Fin.rev j ≤ i), f i := by
  refine Finset.prod_nbij' Fin.rev Fin.rev ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact Fin.rev_le_rev.mpr ha
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    rw [← Fin.rev_le_rev, Fin.rev_rev]
    exact ha
  · intro a _
    exact Fin.rev_rev a
  · intro a _
    exact Fin.rev_rev a
  · intro a _
    rfl

end GlobalTheory.CompanionTheory.FinReversal
