module

import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DenseKFiniteVectorsUnitaryGroupRep
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothVec
public import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfSt
public import Formalism.PeriodIntegrals.QuotInv
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.OrbitDerivatives.EtaleClosedPointLiftsSimpleRootsMonic
public import Development.WeilBound.HeckeVectors.SmoothVectors.SobolevApproximation.SobApproxHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BesselDerivatives.ExpSup
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.ExpIntertwine
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.KFiniteSmoothVectors.Garding
import Mathlib.Tactic.Linter.Style
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Matrix Topology
open scoped ComplexOrder

noncomputable section

namespace CompanionTheory.D.gk.HC

open Formalism.BasicNotions.TH (GrpData URep GKMod)

open scoped Matrix.Norms.Elementwise

section UJ

variable {n : ℕ} (ε : Fin n → Bool)

variable {ε} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem kfinDense_UJC (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) : Dense {v : H | Formalism.MainNotions.S.IsKFin ε σ v} := by
  apply GlobalTheory.CompactRep.dense_isKFin <;> assumption

end UJ

end CompanionTheory.D.gk.HC
