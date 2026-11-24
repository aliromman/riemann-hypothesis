module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Field
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
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE

@[expose] public section

namespace PositivityTheory.HtPt.Gc

theorem dvr_of_height_one {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (q : Ideal A) [q.IsPrime] (h1 : q.height = 1) :
    IsDiscreteValuationRing (Localization.AtPrime q) := by
  have hdim : ringKrullDim (Localization.AtPrime q) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q, h1]; rfl
  have hnf : ¬ IsField (Localization.AtPrime q) := fun hf => by
    rw [ringKrullDim_eq_zero_of_isField hf] at hdim
    exact zero_ne_one hdim
  have hic : IsIntegrallyClosed (Localization.AtPrime q) :=
    isIntegrallyClosed_of_isLocalization _ q.primeCompl q.primeCompl_le_nonZeroDivisors
  have hk : Ring.KrullDimLE 1 (Localization.AtPrime q) := by
    rw [Ring.krullDimLE_iff, hdim]; rfl
  have hD : IsDedekindDomain (Localization.AtPrime q) := by
    have : Ring.DimensionLEOne (Localization.AtPrime q) :=
      ⟨fun {P} hP hP' => (Ring.krullDimLE_one_iff_of_noZeroDivisors.1 hk) P hP hP'⟩
    exact {}
  exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime q) hnf).out 1 3).2 hD

end PositivityTheory.HtPt.Gc
