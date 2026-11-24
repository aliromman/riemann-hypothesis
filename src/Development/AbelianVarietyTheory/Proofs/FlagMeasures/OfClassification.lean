module

public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConsequencesOfDsClass
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

namespace GlobalTheory.DiscreteSeriesConsequences

theorem of_classification : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Dec.LowKMultOne ∧ GlobalTheory.Dec.DSInfChar ∧
    GlobalTheory.Dec.DSExists ∧ GlobalTheory.Dec.DSUnique ∧ GlobalTheory.Published.DiscreteSeriesUpqExists := by
  intro h
  obtain ⟨hE, -, hU, hI, hM, -, -⟩ :=
    GlobalTheory.ClassificationConsequences.consequences_of_dsClass (GlobalTheory.Published.discreteSeriesClassification_iff.1 h)
  exact ⟨hM, hI, hE, hU, GlobalTheory.Published.discreteSeriesUpqExists_iff_dsExists.2 hE⟩

end GlobalTheory.DiscreteSeriesConsequences
