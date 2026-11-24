module

public import Formalism.SharpRestriction.DesignExistsOfChoices
public import Development.AutomorphicArithmetic.CharacterBoxes.Supply
public import Formalism.SharpRestriction.MuTuOfTuSize
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

namespace UpperTheory.Top

open Formalism.BasicNotions Formalism.MainNotions Formalism.HC GlobalTheory.EX

def ExS (𝒜 : FamClass) (cT : ℝ → ℝ → ℝ) : Prop :=
  ∀ (la : ℝ) (G : FReq), 1 < la → HostExW la G.req →
    Formalism.MainNotions.DesignChoices (Formalism.MainNotions.WithTw fun Fm => 𝒜 Fm ∧ G.cls la Fm) 3 cT

end UpperTheory.Top

end
