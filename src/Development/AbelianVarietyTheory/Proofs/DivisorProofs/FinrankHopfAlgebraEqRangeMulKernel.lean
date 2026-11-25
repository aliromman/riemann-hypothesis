module

public import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.FibreRankCompOfSurjective
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
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective

@[expose] public section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem finrank_eq_range_mul_ker : ∀ (k : Type) [Field k] (A : Type) [CommRing A] [HopfAlgebra k A]
    [IsCocomm k A] [Module.Finite k A] (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C]
    [Module.Finite k C] (f : C →ₐc[k] A),
    Module.finrank k A = Module.finrank k (LinearMap.range (f : C →ₐ[k] A).toLinearMap) *
      Module.finrank k (A ⧸ kerIdeal f) := by
  intro k _ A _ _ _ _ C _ _ _ _ f
  rw [GlobalTheory.PDiv.finrank_eq_ker_mul_range k A C f, mul_comm]

end GlobalTheory.Dieu
