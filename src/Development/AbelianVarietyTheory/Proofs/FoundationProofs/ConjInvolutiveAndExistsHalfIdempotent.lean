module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfIdem
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

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

namespace GlobalTheory.NormSum.HalfIdempotent

theorem conj_involutive_and_exists_half_idempotent : ∀ (D : D7), (∀ y : AE D, sgA D (sgA D y) = y) ∧ ∃ ε ∈ OhE D, ε * ε = ε ∧ ε * sgA D ε = 0 ∧ ∀ q : ℕ, q.Prime → (InertQ D q → ZeroAt D q (ε + sgA D ε)) ∧ (¬ InertQ D q → ZeroAt D q (1 - (ε + sgA D ε))) :=
  fun D => ⟨GlobalTheory.NormSum.VacMove.sgA_sgA D, GlobalTheory.NormSum.VacMove.exists_half_idem D⟩

end GlobalTheory.NormSum.HalfIdempotent
