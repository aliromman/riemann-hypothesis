module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtSide
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.IsKumCoc
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

open CategoryTheory AlgebraicGeometry

namespace CrystallineSemistableComparison

def ModelComponents : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
  CompM (Model.Sm (l := l) (K := K)) ∧ CompM (Model.Good (l := l) (K := K))

def GeometricGenericComponents : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (M : Model l K), M.Good →
  ∀ d, M.Conn d → M.Geo

structure FormalIn : Prop where
  a1 : GlobalTheory.EtC.A1
  a6nat : GlobalTheory.EtC.DivisorNaturality
  a6ring : GlobalTheory.EtC.DivisorRingCompatibility
  a7 : GlobalTheory.EtC.A7
  a8 : GlobalTheory.EtC.A8
  a9 : GlobalTheory.EtC.A9
  a10 : GlobalTheory.EtC.A10
  et : E.EtIn

def RootsOfUnityFormal : Prop := FormalIn → InRoot

def SumInputFromFormal : Prop := FormalIn → InSum

end CrystallineSemistableComparison
