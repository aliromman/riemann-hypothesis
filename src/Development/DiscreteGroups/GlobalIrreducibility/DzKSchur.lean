module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
public import Mathlib.RepresentationTheory.FinGroupCharZero
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

open CategoryTheory

noncomputable section

namespace DiscreteGroups.sglob.DzType.Kon

variable {G : Type} [Group G] [Fintype G]

theorem simple_of_isIrr (τ : FDRep ℂ G) (h : GlobalTheory.GLq.IsIrr τ.character) : Simple τ := by
  obtain ⟨V, hV, hch⟩ := h
  rw [FDRep.simple_iff_char_is_norm_one] at hV ⊢
  simpa only [hch] using hV

end DiscreteGroups.sglob.DzType.Kon
