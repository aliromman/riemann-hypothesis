module

public import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEnds
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

open NumberField

namespace GlobalTheory.RowLatXS

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ} {T : E}

def Ia (Λ : Submodule (𝓞 E) S.V) (F : Formalism.MainNotions.S.FlagG S r T) (a : Fin r) : Submodule (𝓞 E) E :=
  Submodule.span (𝓞 E) {t | ∃ x ∈ Λ, x ∈ F.Xa (a.val + 1) ∧ F.coefX x a = t}

end GlobalTheory.RowLatXS
