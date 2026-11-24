module

public import Formalism.PeriodIntegrals.UpqRep
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

open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.DiscreteSeries

theorem isDS_sk_imp_upqRep (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    Formalism.MainNotions.S.IsDS ε lam σ → PI.UpqRep.IsDS ε lam σ :=
  fun h => h

end GlobalTheory.CompanionTheory.DiscreteSeries
