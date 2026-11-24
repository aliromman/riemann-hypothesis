module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatA
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.LatticeAndConstantUnique
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatB

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatB

namespace GlobalTheory.ModelLatExamples

theorem eq_latP {r : ℕ} (D : D7) (Λ L : Submodule (𝓞 D.host.E) (Fin r → D.host.E))
    (h : Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ L, v = a • u}) : L = lattice₂ D Λ := by
  have h2 := lat_eq_span Formalism.IndefR.Fin.factPrincipalDatum Λ
  apply le_antisymm
  · exact GlobalTheory.ModelLatticeCheck.le_of_span_le _ (GlobalTheory.ModelLatticeCheck.AA_ne_zero D) _ _ (by rw [← h, ← h2])
  · exact GlobalTheory.ModelLatticeCheck.le_of_span_le _ (GlobalTheory.ModelLatticeCheck.AA_ne_zero D) _ _ (by rw [← h, ← h2])

end GlobalTheory.ModelLatExamples
