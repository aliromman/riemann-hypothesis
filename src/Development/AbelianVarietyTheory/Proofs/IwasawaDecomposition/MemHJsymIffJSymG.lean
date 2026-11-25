module

public import Formalism.LocalToGlobal.Columns.LevGSym
public import Formalism.LocalToGlobal.HermitianForms.DefsSym
public import Formalism.LocalToGlobal.Columns.RecLevelSymF
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

open Formalism.L2.Col

namespace GlobalTheory

theorem mem_HJsym_iff_JSymG : ∀ (κ : Type) [Field κ] (n k r t m rS : ℕ) (h : r ≤ n), r = k + 2 * rS + 1 → 0 < t → n = r + m * t →
    ∀ M : GL (Fin n) κ, M ∈ HJsym κ n k r t m rS h ↔ M ∈ Formalism.L2.Forms.JSymG κ n k rS t false := by
  intro κ _ n k r t m rS h hr ht hn M
  subst hr
  rw [HJsym_eq_JSymG ht (by omega) h]

end GlobalTheory
