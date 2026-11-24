module

import Development.EtaleCohomology.EtaleSheaves.DomOpenPf
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

open Polynomial

namespace GlobalTheory.FractionRingRootRange

theorem root_mem_range {A B : Type} [CommRing A] [Nontrivial A] [CommRing B] [IsDomain B] [Algebra A B]
    (h : GlobalTheory.EtC.AIC A) (z : B) :
    ∀ (n : ℕ) (p : A[X]), p.natDegree = n → p.Monic → aeval z p = 0 → ∃ a : A, algebraMap A B a = z := by
  intro n
  induction n with
  | zero =>
    intro p hdeg hmon hz
    rw [Polynomial.eq_one_of_monic_natDegree_zero hmon hdeg, map_one] at hz
    exact absurd hz one_ne_zero
  | succ n ih =>
    intro p hdeg hmon hz
    obtain ⟨a, ha⟩ := h p hmon (by omega)
    have hmul : (X - C a) * (p /ₘ (X - C a)) = p := mul_divByMonic_eq_iff_isRoot.mpr ha
    have hqmon : (p /ₘ (X - C a)).Monic :=
      (monic_X_sub_C a).of_mul_monic_left (by rw [hmul]; exact hmon)
    have hqdeg : (p /ₘ (X - C a)).natDegree = n := by
      rw [natDegree_divByMonic p (monic_X_sub_C a), natDegree_X_sub_C, hdeg]
      omega
    rw [← hmul, map_mul] at hz
    simp only [map_sub, aeval_X, aeval_C] at hz
    rcases mul_eq_zero.mp hz with h1 | h1
    · exact ⟨a, (sub_eq_zero.mp h1).symm⟩
    · exact ih _ hqdeg hqmon h1

theorem isAlgClosed_fractionRing (A : Type) [CommRing A] [IsDomain A] (h : GlobalTheory.EtC.AIC A) :
    IsAlgClosed (FractionRing A) := by
  apply LateralTheory.E.DomOpenPf.algClosed_of_AIC <;> assumption

end GlobalTheory.FractionRingRootRange
