module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCorrOpOfAvg
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsWtZero
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericMulOfProd

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt)
open UpperTheory.Gal.crystallineComparison (PtId fn heckePol)

namespace UpperTheory.Gal.Mod

def CorrOpEq : Prop := ∀ (l : ℕ) [Fact l.Prime] {S : Scheme.{0}} (c : TranscendenceTraces.Corr S S) [Etale c.p], c.w = Wt.const _ 1 →
  IsUnit (l : Γ(S, ⊤)) → ∀ T, IsCorrOp l c.p c.f T → T = DirectSum.lmap fun k : ℤ => c.opQ l k 0

end UpperTheory.Gal.Mod

end
