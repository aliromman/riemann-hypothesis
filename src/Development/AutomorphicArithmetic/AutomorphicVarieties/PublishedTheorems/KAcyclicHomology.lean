module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem
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

open CategoryTheory UpperTheory.V.KL

namespace UpperTheory.V.Published

def KStability : Prop :=
  ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ i n : ℕ, 2 * i + s + 2 ≤ n →
    IsIso (grpHMap (stab R n (n + 1) (Nat.le_succ n)) i)

end UpperTheory.V.Published

end
