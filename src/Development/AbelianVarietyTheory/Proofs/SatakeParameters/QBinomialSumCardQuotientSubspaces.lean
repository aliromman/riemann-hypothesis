module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussBinomMulProd
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

namespace GlobalTheory

theorem qBinomial_subspaces : ∀ (k V : Type) [Field k] [Finite k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (X : ℂ),
    ∑ j ∈ Finset.range (Module.finrank k V + 1),
        (-1 : ℂ) ^ j * (Nat.card k : ℂ) ^ (j * (j - 1) / 2) *
          (Nat.card {W : Submodule k V // Module.finrank k (V ⧸ W) = j} : ℂ) * X ^ j =
      ∏ i ∈ Finset.range (Module.finrank k V), (1 - (Nat.card k : ℂ) ^ i * X) := by
  intro k V _ _ _ _ _ X
  simp only [GlobalTheory.GaussCount.card_codim]
  exact GlobalTheory.GaussCount.gauss_formula (Nat.card k) ℂ X (Module.finrank k V)

end GlobalTheory
