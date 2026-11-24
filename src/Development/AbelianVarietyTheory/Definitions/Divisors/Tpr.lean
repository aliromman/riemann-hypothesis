module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
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

open NumberField Matrix GlobalTheory.CuspRep Formalism.REAL

namespace GlobalTheory.WigAlg

def cx {E : Type} [Field E] {a : ℕ} {N : Type} [AddCommGroup N] [Module ℂ N] (τ : E →+* ℂ) (φ : Lie E a → N)
    (i j : Fin a) : N :=
  (1 / 2 : ℂ) • (φ (toL (Matrix.single i j (atEmb τ 1))) - Complex.I • φ (toL (Matrix.single i j (atEmb τ Complex.I))))

end GlobalTheory.WigAlg

end
