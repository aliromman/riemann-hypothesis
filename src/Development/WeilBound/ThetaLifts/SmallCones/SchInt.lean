module

public import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
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
import Development.WeilBound.ThetaLifts.LatticeBasics.SchwartzFunctionalEqZeroOfDense

@[expose] public section

noncomputable section

namespace PositivityTheory.ThKCT

theorem schInt : SchInt := by
  intro V _ _ _ α _ _ _ _ μ G hG hI
  obtain ⟨f, hf⟩ := ThKOwn.SchI.exists_int hG hI
  refine ⟨f, fun T => ?_⟩
  obtain ⟨s, T', hT⟩ := ThKOwn.SchI.factor T
  have hi : MeasureTheory.Integrable (fun a (i : s) => ThKOwn.SchI.J i.1.1 i.1.2 (G a)) μ :=
    MeasureTheory.Integrable.of_eval fun i => ThKOwn.SchI.int_J hG hI _ _
  simp only [hT]
  refine ⟨T'.integrable_comp hi, ?_⟩
  rw [T'.integral_comp_comm hi]
  congr 1
  funext i
  rw [hf]
  exact (ContinuousLinearMap.proj (R := ℂ) i).integral_comp_comm hi

end PositivityTheory.ThKCT

end
