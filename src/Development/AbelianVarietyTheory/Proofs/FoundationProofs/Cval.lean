module

public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
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
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section
namespace GlobalTheory.ThetaTransl

variable {p : ℕ} [Fact p.Prime]

def cval (g : GL3Theta.G1 p) (s : ℂ) : ℂ_[p] := lamC g.lam (U1 g.abelian₂ s (sgStar g.abelian₂) 0)

def tau (g : GL3Theta.G1 p) (s : ℂ) : PowerSeries ℂ_[p] :=
  (ePhi1 g.lam g.abelian₂ g.C g.wq)⁻¹ * g.atU (U1 g.abelian₂ s (sgStar g.abelian₂))

def logc (g : GL3Theta.G1 p) (s : ℂ) : ℝ := if s ∈ g.abelian₂ then 0 else Real.log ‖cval g s‖

end GlobalTheory.ThetaTransl
