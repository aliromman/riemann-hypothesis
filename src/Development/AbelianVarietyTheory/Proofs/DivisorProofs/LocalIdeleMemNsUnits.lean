module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
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

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.MuExist

def nsUnits (E : Type) [Field E] [NumberField E] [IsCMField E] : Subgroup (Neutral.B1.Ideles E) :=
  Subgroup.closure {x | ∃ (w : HeightOneSpectrum (𝓞 E)) (u : (w.adicCompletion E)ˣ), ¬ GlobalTheory.UnitaryBC.IsSplitAt w ∧
    Valued.v (u : w.adicCompletion E) = 1 ∧ x = Neutral.B1.localIdele E w u}

theorem localIdele_mem_nsUnits {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E))
    (u : (w.adicCompletion E)ˣ) (hw : ¬ GlobalTheory.UnitaryBC.IsSplitAt w) (hu : Valued.v (u : w.adicCompletion E) = 1) :
    Neutral.B1.localIdele E w u ∈ nsUnits E :=
  Subgroup.subset_closure ⟨w, u, hw, hu, rfl⟩

end GlobalTheory.MuExist
