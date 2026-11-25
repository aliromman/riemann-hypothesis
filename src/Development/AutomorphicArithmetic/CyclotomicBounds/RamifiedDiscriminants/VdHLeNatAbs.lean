module

public import Development.AutomorphicArithmetic.PrimeDiscriminants.SlopeTestRemainingChoices
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

theorem Formalism.HC.HostRaw.vdH_le_natAbs {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) (p : ℕ) :
    H.vdH p ≤ ((NumberField.discr H.E).natAbs : ℝ) := by
  unfold Formalism.HC.HostRaw.vdH
  have h1 : (1 : ℝ) ≤ (Module.finrank ℚ H.E : ℝ) := by exact_mod_cast Module.finrank_pos
  have h2 : padicValNat p (NumberField.discr H.E).natAbs ≤ (NumberField.discr H.E).natAbs :=
    Nat.padicValNat_def ▸ Nat.multiplicity_le_self _
  have h3 : (padicValNat p (NumberField.discr H.E).natAbs : ℝ) ≤ ((NumberField.discr H.E).natAbs : ℝ) := by exact_mod_cast h2
  exact (div_le_self (Nat.cast_nonneg _) h1).trans h3
