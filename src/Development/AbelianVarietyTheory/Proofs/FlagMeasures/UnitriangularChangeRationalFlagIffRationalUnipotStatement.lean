module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularChangeRationalFlagIffRationalUnipot
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

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical

theorem _root_.GlobalTheory.T.unitriangularChange_rationalFlag_iff_rationalUnipotent : ∀ (D : D7) {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T), T ≠ 0 → (∀ A : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, Uni A → ∃ F₁ : LFlag (D.sp.Y 0) D.R.rS T, Chg (frame F) A (frame F₁)) ∧ (∀ F₁ : LFlag (D.sp.Y 0) D.R.rS T, Tri D.host.E (frame F) (frame F₁) ↔ ∃ n ∈ Formalism.L2.SG.NGData.NRat F, ∀ a, frame F₁ a = n (frame F a)) := by
  first | exact @GlobalTheory.FlagChange.flag_change
