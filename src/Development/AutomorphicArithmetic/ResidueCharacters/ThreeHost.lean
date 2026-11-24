module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
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

open NumberField Formalism Formalism.BasicNotions

namespace UpperTheory.N

theorem three_ne_q (D : D7) : 3 ≠ D.host.q ∧ 3 ≠ D.host.d := by
  obtain ⟨_, _, _, hd, _⟩ := D.host.hyp
  refine ⟨fun h => D.host.q_ne_three h.symm, fun h => ?_⟩
  omega

theorem three_ne_g (D : D7) (k : Fin 2) : 3 ≠ D.host.g k := by
  intro h
  have hc := D.ntypes.g_cond k
  rw [← h] at hc
  obtain ⟨_, _, hq, hd, _⟩ := D.host.hyp
  have hq3 := D.host.q_ne_three
  have hS : 1 ≤ D.host.QS := D.host.QS_pos
  have h1 : 11 ≤ D.host.q := by omega
  have h2 : 1 ≤ D.host.d := by omega
  have hM : 3 < D.host.QS * D.host.q * D.host.d :=
    calc 3 < 1 * 11 * 1 := by norm_num
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul hS h1) h2
  rw [Nat.mod_eq_of_lt hM] at hc
  omega

end UpperTheory.N
