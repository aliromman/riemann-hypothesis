module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualLatticeActions
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DisjointSpanPerpLat
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsOfFixedInt
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

namespace GlobalTheory.UnramSelfDualClosed

theorem selfDualLatticeLemmas : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.SelfDualLatticeLemmas :=
  GlobalTheory.SelfDualLatticeCompare.selfDualLattices_iff.1 GlobalTheory.UnramSelfDual.selfDualLattices

end GlobalTheory.UnramSelfDualClosed
