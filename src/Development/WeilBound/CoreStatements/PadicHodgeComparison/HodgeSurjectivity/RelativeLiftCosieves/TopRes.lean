module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
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

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace CrystallineSemistableComparison.Onto

theorem topRes_pf : TopRes := by
  intro R _ C _ F U Q hU n
  let L : C ⥤ U.FullSubcategory := U.lift (𝟭 C) hU
  have back : ∀ z : CH.Cn F n, ∀ s : ComposableArrows C n,
      (CH.Mor.restrict F U.ι).pullC n z (s ⋙ L) = z s := fun _ _ => rfl
  refine ⟨⟨fun z z' h => funext fun s => ?_, fun w => ⟨fun s => w (s ⋙ L), ?_⟩⟩, fun z => ⟨?_, ?_⟩⟩
  · rw [← back z s, ← back z' s, h]
  · funext t
    rfl
  · intro hz s hs
    rw [← back z s]
    exact hz (s ⋙ L) hs
  · intro hz t ht
    exact hz (t ⋙ U.ι) ht

end CrystallineSemistableComparison.Onto

end
