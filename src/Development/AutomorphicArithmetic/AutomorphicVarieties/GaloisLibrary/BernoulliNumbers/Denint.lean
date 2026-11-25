module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Expand
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Primden
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

open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_denint :
    ∀ (N k a : ℕ), 0 < N → ∃ z : ℤ, (den N k : ℚ) * bcoef N k a = z := by
  intro N k a hN
  suffices h : (den N k : ℚ) * bcoef N k a ∈ (Int.castRingHom ℚ).range by
    obtain ⟨z, hz⟩ := h
    exact ⟨z, hz.symm⟩
  rw [b_expand N k a hN, Finset.mul_sum]
  refine Subring.sum_mem _ fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  obtain ⟨z, hz⟩ := b_primden k j hjk
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpow : (N : ℚ) * (N : ℚ) ^ ((j : ℤ) - 1) = (N : ℚ) ^ j := by
    rw [← zpow_one_add₀ hN', add_sub_cancel, zpow_natCast]
  refine ⟨(k.choose j : ℤ) * z * (N : ℤ) ^ j * (a : ℤ) ^ (k - j), ?_⟩
  unfold den
  rw [eq_intCast]
  push_cast
  rw [← hz, ← hpow]
  ring
