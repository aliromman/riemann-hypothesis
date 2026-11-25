module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
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

open Formalism.REAL Formalism.MainNotions.S

namespace UpperTheory.Lit.Cusp

def wt {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) : ℝ := (1 + Real.sqrt (hs (umat g))) ^ (2 * n ^ 2 + 1)

def Decays {n : ℕ} {ε : Fin n → Bool} (f : UJ ε → ℂ) : Prop := ∃ C : ℝ, ∀ g, ‖f g‖ * wt g ≤ C

end UpperTheory.Lit.Cusp

end
