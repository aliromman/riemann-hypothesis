module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
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

open scoped Matrix
open Formalism.BasicNotions Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

namespace PositivityTheory.GramSchwartzFunctions

def PullSchLI : Prop :=
  ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m r n : ℕ) (c : Matrix (Fin r) (Fin n) D.host.E), LinearIndependent D.host.E c →
    ∀ φ : Mx D m n → ℂ, φ ∈ schwartzA θ m n → pull c φ ∈ schwartzA θ m r

end PositivityTheory.GramSchwartzFunctions
