module

public import Mathlib.Data.ENat.Basic
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Order.CompletePartialOrder
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
public import Mathlib.Algebra.Order.AddGroupWithTop

@[expose] public section

theorem UpperTheory.Reformulated.B.Qn14.le_of_add_one_le_succ :
    ∀ {a : WithBot ℕ∞} {k : ℕ},
    a + (1 : WithBot ℕ∞) ≤ (↑(k + (1 : ℕ)) : WithBot ℕ∞) → a ≤ (↑k : WithBot ℕ∞) := by
  intro a k h
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have h1 : ((⊤ : ℕ∞) + 1 : ℕ∞) ≤ ((k + 1 : ℕ) : ℕ∞) := by
        rw [← WithBot.coe_le_coe]
        exact h
      rw [top_add, top_le_iff] at h1
      exact ENat.coe_ne_top _ h1
    | coe n =>
      have h1 : ((n : ℕ∞) + 1 : ℕ∞) ≤ ((k + 1 : ℕ) : ℕ∞) := by
        rw [← WithBot.coe_le_coe]
        exact h
      have h2 : n + 1 ≤ k + 1 := by exact_mod_cast h1
      have h3 : (n : ℕ∞) ≤ (k : ℕ∞) := by exact_mod_cast (Nat.le_of_succ_le_succ h2)
      exact WithBot.coe_le_coe.mpr h3
