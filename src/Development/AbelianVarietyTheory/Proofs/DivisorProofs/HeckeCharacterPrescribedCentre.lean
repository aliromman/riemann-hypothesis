module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChiDetSplitCentre
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

open NumberField

namespace GlobalTheory.SplitCentreChar

theorem exists_hChar_splitCentre : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (d : ℕ), 0 < d →
    ∀ s : ℂ, ∃ χ : Formalism.L2.Host.HChar E, ∀ t : ℝ,
      ((GlobalTheory.CuspRep.chiDet d χ (GlobalTheory.UnitaryBC.splitCentre E d t) : ℂˣ) : ℂ) = Complex.exp (-(t * s)) := by
  intro E _ _ _ d hd s
  obtain ⟨χ, hχ⟩ := GlobalTheory.CuspQuot.exists_chiDet_splitCentre (E := E) hd (-s)
  exact ⟨χ, fun t => by rw [hχ t]; congr 1; ring⟩

end GlobalTheory.SplitCentreChar
