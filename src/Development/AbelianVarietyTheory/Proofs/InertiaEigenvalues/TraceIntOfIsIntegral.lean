module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.RingTheory.Trace.Basic

@[expose] public section

noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

theorem IsUnrExt.ne_zero {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E} (hU : IsUnrExt K K' d φ) : d ≠ 0 := by
  intro hd
  have h1 : Nat.card (IsLocalRing.ResidueField K'.O) = 1 := by
    rw [K'.card_res, hU.1, hd, pow_zero, one_pow]
  have h2 := Finite.one_lt_card (α := IsLocalRing.ResidueField K'.O)
  omega

theorem trace_int_of_isIntegral {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E} (hU : IsUnrExt K K' d φ) (z : K'.E)
    (hz : @IsIntegral K.O K'.E _ _ (φ.comp (algebraMap K.O K.E)).toAlgebra z) :
    ∃ a : K.O, @Algebra.trace K.E K'.E _ _ φ.toAlgebra z = algebraMap K.O K.E a := by
  letI : Algebra K.E K'.E := φ.toAlgebra
  letI : Algebra K.O K'.E := (φ.comp (algebraMap K.O K.E)).toAlgebra
  haveI : IsScalarTower K.O K.E K'.E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FiniteDimensional K.E K'.E :=
    Module.finite_of_finrank_pos (by rw [hU.2.2.2.2]; exact Nat.pos_of_ne_zero hU.ne_zero)
  have h := Algebra.isIntegral_trace (R := K.O) (L := K.E) hz
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  exact ⟨a, ha.symm⟩

end GlobalTheory.UnitLemma.Unr
