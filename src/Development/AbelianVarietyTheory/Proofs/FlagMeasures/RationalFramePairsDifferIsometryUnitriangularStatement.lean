module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalFramePairsDifferIsometryUnitriangular
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

theorem _root_.GlobalTheory.T.rationalFramePairs_differ_isometry_unitriangular : ∀ (D : D7) {T T' : D.host.E} (F F00 : LFlag (D.sp.Y 0) D.R.rS T) (F' F'0 : LFlag (D.sp.Y 0) D.R.rS T') (w : Point D.host.E (D.R.rS + 1)), T ≠ 0 → T' ≠ 0 → Gval F F' ≠ 0 → IsInCell (ZhatOM (ZhatL F F')) w → ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 = Gval F F' ∧ ∃ γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT, Tri D.host.E (frame F00) (fun a => γ (frame F a)) ∧ Tri D.host.E (frame F'0) (fun a => γ (frame F' a)) := by
  first | exact @GlobalTheory.LocOver.witt_frames_at_point
