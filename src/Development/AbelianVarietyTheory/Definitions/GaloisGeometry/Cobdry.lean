module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.MvPowerSeries.Substitution
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
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

noncomputable section

namespace GlobalTheory.ThStr

open Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta NumberField Classical

variable {l : ℕ} [Fact l.Prime]

def laS (l : ℕ) [Fact l.Prime] (d : ℕ) (s : ZMod d) : MvPowerSeries (ZMod d) ℂ_[l] :=
  fun n => ∑ e ∈ Finset.range ((n.sum fun _ k => k) + 1),
    if n = Finsupp.single (s - ((2 * e : ℕ) : ZMod d)) (l ^ (2 * e)) then ((l : ℂ_[l]) ^ e)⁻¹ else 0

def laAt {d : ℕ} {κ : Type} (ι : ZMod d → κ) (s : ZMod d) : MvPowerSeries κ ℂ_[l] :=
  MvPowerSeries.subst (fun r : ZMod d => (MvPowerSeries.X (ι r) : MvPowerSeries κ ℂ_[l])) (laS l d s)

end GlobalTheory.ThStr
