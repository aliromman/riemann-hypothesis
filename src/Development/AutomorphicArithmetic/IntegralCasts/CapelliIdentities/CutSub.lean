module

public import Mathlib.NumberTheory.NumberField.Basic
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

noncomputable def UpperTheory.Reformulated.B.FirstCoordinatesSubmodule.cutSub :
    (K : Type) → [inst : Field K] → [NumberField K] → (r : ℕ) → ℕ → Submodule (NumberField.RingOfIntegers K) (Fin r → K) :=
  fun K _ _ r n =>
    { carrier := {v : Fin r → K | ∀ i : Fin r, n ≤ (i : ℕ) → v i = 0}
      add_mem' := by
        intro v w hv hw i hi
        rw [Pi.add_apply, hv i hi, hw i hi, add_zero]
      zero_mem' := fun _ _ => rfl
      smul_mem' := by
        intro c v hv i hi
        rw [Pi.smul_apply, hv i hi, smul_zero] }
