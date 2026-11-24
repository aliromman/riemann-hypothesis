module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.NormEqOneOfIsUnitarisableU
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.TemperedEigenvalueNorms.Centred
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

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace PositivityTheory.Gud.Pf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isCentred_of_unitCC {Δ : Segment k} {δ : IrrGL (k := k)} (hL : IsLSeg Δ δ.rep)
    (hU : PositivityTheory.RgUd.UOrder.UnitCC δ.rep) : PositivityTheory.UdReth2.IsCentred Δ :=
  fun _ hω z => PositivityTheory.RgUd.UOrder.log_norm_centralChar_u hL hU hω z

end PositivityTheory.Gud.Pf

end
