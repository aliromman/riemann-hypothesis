module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
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

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

noncomputable section

namespace GlobalTheory.PairStep

theorem exists_localEqn_of_isQCart : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), ∀ (D : X → ℚ), IsQCart D → ∀ x : X, ∃ (m : ℕ) (f : X.functionFieldˣ), 0 < m ∧ RegAt x (f : X.functionField) ∧ ∀ z, z ⤳ x → ∀ E : DivOver p, E.IsAt z → D z = (E.ord f : ℚ) / m := by
  intro X _ _ p D hD x
  obtain ⟨m, D₀, hm, hEff, rfl⟩ := hD
  obtain ⟨f, hf⟩ := D₀.exists_isEqn x
  obtain ⟨V, hV, hfV⟩ := hf.exists_nhds
  refine ⟨m, f, hm, CartierDiv.eff_iff.1 hEff x f hf, fun z hz E hE => ?_⟩
  rw [qWeil, (hfV z (hz.mem_open V.isOpen hV)).mult_eq, ← hE.ord_eq]

end GlobalTheory.PairStep
