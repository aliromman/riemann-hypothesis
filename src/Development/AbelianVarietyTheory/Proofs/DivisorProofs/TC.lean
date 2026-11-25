module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
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

noncomputable section

open GlobalTheory.LKTrip
open scoped TensorProduct

namespace GlobalTheory.TorCls

def TC (D : Type) [Ring D] [Algebra ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D) (R : Type) [CommRing R] [Algebra ℚ R]
    (z : (R ⊗[ℚ] D)ˣ × Rˣ) : Prop :=
  (z.1 : R ⊗[ℚ] D) * ((1 : R) ⊗ₜ β) * (starT σ R (z.1 : R ⊗[ℚ] D)).unop =
      algebraMap R (R ⊗[ℚ] D) (z.2 : R) * ((1 : R) ⊗ₜ β) ∧
    Commute (z.1 : R ⊗[ℚ] D) ((1 : R) ⊗ₜ y)

end GlobalTheory.TorCls
