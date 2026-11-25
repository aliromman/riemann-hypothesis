module

public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PiTensorProduct
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

@[expose] public section

namespace GlobalTheory.PicDiv

variable {R : Type*} [CommRing R]

noncomputable def hasse (l : ℕ) : PowerSeries R →ₗ[R] PowerSeries R where
  toFun φ := PowerSeries.mk fun n => ((n + l).choose l : R) * PowerSeries.coeff (n + l) φ
  map_add' φ ψ := by ext n; simp [mul_add]
  map_smul' c φ := by ext n; simp [mul_left_comm]

theorem coeff_hasse (l n : ℕ) (φ : PowerSeries R) :
    PowerSeries.coeff n (hasse l φ) = ((n + l).choose l : R) * PowerSeries.coeff (n + l) φ := by
  simp [hasse]

theorem constantCoeff_hasse (l : ℕ) (φ : PowerSeries R) :
    PowerSeries.constantCoeff (hasse l φ) = PowerSeries.coeff l φ := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_hasse]; simp

theorem coeff_one_hasse (l : ℕ) (φ : PowerSeries R) :
    PowerSeries.coeff 1 (hasse l φ) = ((l + 1 : ℕ) : R) * PowerSeries.coeff (l + 1) φ := by
  rw [coeff_hasse, add_comm 1 l, Nat.choose_succ_self_right]

theorem hasse_zero (φ : PowerSeries R) : hasse 0 φ = φ := by
  ext n; simp [coeff_hasse]

end GlobalTheory.PicDiv
