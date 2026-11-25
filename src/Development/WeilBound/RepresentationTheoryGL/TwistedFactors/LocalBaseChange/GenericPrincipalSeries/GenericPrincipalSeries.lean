module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
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
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel

namespace PositivityTheory.Lbc

def torusChar {k : Type} [Field k] {n : ℕ} (ξ : Fin n → (kˣ →* ℂˣ))
    (t : ∀ _ : Fin n, GL (Fin 1) k) : ℂ :=
  ∏ a, ((ξ a (Matrix.GeneralLinearGroup.det (t a)) : ℂˣ) : ℂ)

end PositivityTheory.Lbc

end
