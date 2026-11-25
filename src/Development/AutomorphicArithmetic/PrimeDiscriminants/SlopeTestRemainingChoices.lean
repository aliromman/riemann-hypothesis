module

public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
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

namespace Formalism.HC

namespace HostRaw

variable {φ : Frame} (H : HostRaw φ)

def vdH (p : ℕ) : ℝ := (padicValNat p (NumberField.discr H.E).natAbs : ℝ) / (Module.finrank ℚ H.E : ℝ)

theorem vdH_nonneg (p : ℕ) : 0 ≤ H.vdH p := by unfold vdH; positivity

end HostRaw

end Formalism.HC

end
