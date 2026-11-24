module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SumMulCoPtSbEqSumInv
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

noncomputable section

namespace GlobalTheory.LambdaValuationPowers

variable {K : Type*} [Field K] [CharZero K]

def chiProj (N p m k : ℕ) [NeZero N] (ψ : DirichletCharacter K (p ^ m)) (χ : ℕ → K) (c d x : ℤ) (s : ℕ) : K :=
  ∑ δ : (ZMod N)ˣ, χ (δ : ZMod N).val * coPtSb N p m k ψ c d (x * ((δ : ZMod N).val : ℤ)) ((δ : ZMod N).val : ℤ) s

end GlobalTheory.LambdaValuationPowers
