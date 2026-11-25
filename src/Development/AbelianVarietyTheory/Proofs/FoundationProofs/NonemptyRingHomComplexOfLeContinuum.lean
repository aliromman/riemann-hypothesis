module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyRingHomComplexOfFg
public import Formalism.LocalRingCardinality.DataDIV
public import Mathlib.Algebra.MvPolynomial.Cardinal
public import Mathlib.FieldTheory.IsAlgClosed.Classification
public import Mathlib.RingTheory.Algebraic.Cardinality
public import Mathlib.RingTheory.Localization.Cardinality
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

open Formalism.BasicNotions NumberField

namespace GlobalTheory.WittFracComplex


open Cardinal in
theorem nonempty_ringHom_complex_of_le_continuum (K : Type) [Field K] [CharZero K] (hK : #K ≤ 𝔠) :
    Nonempty (K →+* ℂ) := by
  apply _root_.GlobalTheory.FGFieldEmb.nonempty_ringHom_complex_of_mk_le <;> assumption

theorem charZero_wittVector (p : ℕ) [hp : Fact p.Prime] (k : Type) [Field k] [CharP k p] :
    CharZero (WittVector p k) := by
  obtain ⟨q, hq⟩ := CharP.exists (WittVector p k)
  have h1 : ((q : ℕ) : k) = 0 := by
    have := congrArg (WittVector.constantCoeff : WittVector p k →+* k) (CharP.cast_eq_zero (WittVector p k) q)
    rwa [map_natCast, map_zero] at this
  have h2 : p ∣ q := (CharP.cast_eq_zero_iff k p q).1 h1
  rcases CharP.char_is_prime_or_zero (WittVector p k) q with h | h
  · have h3 : p = q := (Nat.prime_dvd_prime_iff_eq hp.out h).1 h2
    subst h3
    exact absurd (CharP.cast_eq_zero (WittVector p k) p) (WittVector.p_nonzero p k)
  · subst h
    exact CharP.charP_to_charZero _


open Cardinal in
theorem mk_wittVector_le (p : ℕ) (k : Type) (hk : #k ≤ ℵ₀) : #(WittVector p k) ≤ 𝔠 := by
  have h : Function.Injective (WittVector.coeff : WittVector p k → ℕ → k) :=
    fun x y h => WittVector.ext (fun n => congrFun h n)
  refine (Cardinal.mk_le_of_injective h).trans ?_
  rw [← Cardinal.power_def, Cardinal.mk_nat, ← Cardinal.aleph0_power_aleph0]
  exact Cardinal.power_le_power_right hk


open Cardinal in
theorem nonempty_ringHom_complex : ∀ (p : ℕ) [Fact p.Prime], Nonempty (DV.KW p →+* ℂ) := by
  intro p _
  have hk : #(AlgebraicClosure (ZMod p)) ≤ ℵ₀ := by
    have := Algebra.IsAlgebraic.cardinalMk_le_max (ZMod p) (AlgebraicClosure (ZMod p))
    rwa [max_eq_right (Cardinal.lt_aleph0_of_finite _).le] at this
  have := charZero_wittVector p (AlgebraicClosure (ZMod p))
  have : CharZero (DV.KW p) :=
    (RingHom.charZero_iff (IsFractionRing.injective (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p))).1 this
  refine nonempty_ringHom_complex_of_le_continuum _ ?_
  rw [Cardinal.mk_fractionRing]
  exact mk_wittVector_le p _ hk

end GlobalTheory.WittFracComplex
