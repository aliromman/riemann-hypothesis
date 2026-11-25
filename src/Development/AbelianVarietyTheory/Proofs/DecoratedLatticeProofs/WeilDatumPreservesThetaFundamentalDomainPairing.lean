module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFunctionScalarProductPreservedIsometry
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
open GlobalTheory.Unf

namespace GlobalTheory.WeilPairing

theorem thPair_om_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χ χ' : ((AE D)ˣ →* Circle)) (om : Om S T), IsWeilDatumO ψ S T χ χ' om → ∀ (v : VolM D T.rank S.rank) p f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → thPair v.μ v.𝓕 (om p f) (om p f') = thPair v.μ v.𝓕 f f' := by
  intro D ψ S T χ χ' om hW v p f f' hf hf'
  obtain ⟨hμ, h𝓕, -⟩ := v.covol
  have h𝓕' : IsAddFundamentalDomain (ratL T S) v.𝓕 v.μ := h𝓕
  exact GlobalTheory.Mem.LiftPolar.scalar_eq D ψ hW.std S T v.μ v.𝓕 hμ h𝓕' (om p) (fun g hg => hW.om_pres p g hg)
    (fun g hg => hW.om_unit v.μ v.𝓕 hμ h𝓕' p g hg) f f' hf hf'

end GlobalTheory.WeilPairing

end
