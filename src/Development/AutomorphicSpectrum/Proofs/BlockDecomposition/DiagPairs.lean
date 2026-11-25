module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
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
public import Mathlib.NumberTheory.LocalField.Basic

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix ValuativeRel

namespace GlobalTheory.CompanionTheory.IwJac

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)

variable {k n}

def tor (ϖ : kˣ) (x : Fin n → ℤ) : GL (Fin n) k := diagT k (Fin n) fun i => ϖ ^ x i

end GlobalTheory.CompanionTheory.IwJac

end
