module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem rootSum_isAdditive_and_pow_X_sub_one :
    ∀ (F : Type) [Field F] (θ : AlgebraicClosure F →* ℂ) (k : ℕ),
      IsAdditive (rootSum θ k) ∧ ∀ j : ℕ, rootSum θ k ((X - C 1 : F[X]) ^ j) = j := by
  intro F _ θ k
  refine ⟨fun P Q hP hQ => ?_, fun j => ?_⟩
  · unfold rootSum
    rw [Polynomial.map_mul, Polynomial.roots_mul ((hP.map _).mul (hQ.map _)).ne_zero,
      Multiset.map_add, Multiset.sum_add]
  · unfold rootSum
    rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      Polynomial.roots_pow, Polynomial.roots_X_sub_C, Multiset.map_nsmul, Multiset.sum_nsmul]
    simp

end GlobalTheory.CuspGL
