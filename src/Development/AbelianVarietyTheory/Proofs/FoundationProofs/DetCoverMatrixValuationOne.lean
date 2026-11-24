module

import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AntitoneZeroOneEqOfSumEq
public import Formalism.SatakeDualWeyl.StatementE
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

open NumberField IsDedekindDomain
open Formalism.UG (GLint)

noncomputable section
namespace GlobalTheory.GLintCover

section
variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

theorem v_eq_one_of_mul {x y : v.adicCompletion F} (hx : x ∈ Formalism.UG.Ov F v) (hy : y ∈ Formalism.UG.Ov F v)
    (hxy : x * y = 1) : Valued.v x = 1 := by
  have h1 : Valued.v x * Valued.v y = 1 := by rw [← map_mul, hxy, map_one]
  have hy1 : Valued.v y ≤ 1 := hy
  have hx1 : Valued.v x ≤ 1 := hx
  refine le_antisymm hx1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = Valued.v x * Valued.v y := h1.symm
    _ ≤ Valued.v x := mul_le_of_le_one_right' hy1

variable {n : ℕ} {ϖ : v.adicCompletion F} {a : Fin n → ℤ}

end
end GlobalTheory.GLintCover

noncomputable section
namespace GlobalTheory.GLintCover

end GlobalTheory.GLintCover

noncomputable section
namespace GlobalTheory.GLintCover

end GlobalTheory.GLintCover
