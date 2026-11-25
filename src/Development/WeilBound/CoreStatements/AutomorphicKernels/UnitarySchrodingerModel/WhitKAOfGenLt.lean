module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenLowOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.WhitKAOfGen
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

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

namespace PositivityTheory.PfSWUS

open GlobalTheory.StdUnn GlobalTheory.CompanionTheory.IwaAd

def AnisoOfRange : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D), InRange V n →
    n + 2 ≤ V.rank ∨ ∀ x : Fin V.rank → D.host.E, HeckeCharacterZeroLocus.SiegelWeilU.hE D.sp.cm.sig (HSpace.gram V) x x = 0 → x = 0

def WhitKAOfGenLt : Prop := PositivityTheory.SiegelWeilFormula.Gen.WhitGenLt → DictKA → AnisoOfRange → WhitKA

end PositivityTheory.PfSWUS

end
