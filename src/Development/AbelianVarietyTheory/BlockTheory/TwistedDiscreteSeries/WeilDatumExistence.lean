module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum

namespace GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumExistenceCriterion

def WeilDatumExists (D : D7) : Prop :=
  ∀ (S T : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle),
    IsStdChar D ψ (-1) → IsHeckeChar D χS → IsHeckeChar D χT → ResEta D χS S.rank → ResEta D χT T.rank →
      ∃ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeilDatumO ψ S T χS χT om

theorem weilDatumExists_iff (D : D7) :
    WeilDatumExists D ↔ ∀ (S T : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle),
      ((∃ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeilDatumO ψ S T χS χT om) ↔
        IsStdChar D ψ (-1) ∧ IsHeckeChar D χS ∧ IsHeckeChar D χT ∧ ResEta D χS S.rank ∧ ResEta D χT T.rank) := by
  constructor
  · intro h S T ψ χS χT
    constructor
    · rintro ⟨om, H⟩
      exact ⟨H.std, H.hecS, H.hecT, H.resS, H.resT⟩
    · rintro ⟨hψ, h1, h2, h3, h4⟩
      exact h S T ψ χS χT hψ h1 h2 h3 h4
  · intro h S T ψ χS χT hψ h1 h2 h3 h4
    exact (h S T ψ χS χT).2 ⟨hψ, h1, h2, h3, h4⟩

end GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumExistenceCriterion

end
