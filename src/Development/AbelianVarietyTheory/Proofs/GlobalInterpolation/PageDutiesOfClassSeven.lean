module

public import Formalism.SharpRestriction.LevelLetterCocycles.AlignN
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
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

namespace GlobalTheory.EX.DQ

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX

theorem tameList_eq {g m : ℕ} (χ : Fin m → (ZMod g)ˣ) : DC.tameList χ = Formalism.MainNotions.tameList χ := by
  funext o
  rcases o with _ | ⟨j, _ | _⟩ <;> rfl

theorem tameDistinct_iff (r g : ℕ) [Fact g.Prime] {m : ℕ} (χ : Fin m → (ZMod g)ˣ) :
    DC.TameDistinct r g χ ↔ Formalism.MainNotions.TameDistinct r g χ := by
  unfold DC.TameDistinct Formalism.MainNotions.TameDistinct
  rw [tameList_eq]

end GlobalTheory.EX.DQ
