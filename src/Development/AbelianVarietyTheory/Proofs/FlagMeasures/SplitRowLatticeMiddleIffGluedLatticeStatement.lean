module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitRowLatticeMiddleIffGluedLattice
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

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.splitRowLattice_middle_iff_gluedLattice : ∀ (D : D7) (u : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), 1 ≤ Tu D u → IsBase D u F0 → IsRowLat D F0 Λ → (IsSplit D F0 Λ → Λ ⊓ toO (hS D) (Wb D) ∈ glueSet D u (L0X D Λ (lf D F0)) ∧ Lsub Λ (lf D F0) = (Λ ⊓ toO (hS D) (Wb D)) ⊔ toO (hS D) F0.X) ∧ (∀ L' : LatW D, ∀ L ∈ glueSet D u L', IsRowLat D F0 (XS D F0 ⊔ L ⊔ YS D) ∧ IsSplit D F0 (XS D F0 ⊔ L ⊔ YS D) ∧ (XS D F0 ⊔ L ⊔ YS D) ⊓ toO (hS D) (Wb D) = L) := by
  first | exact @GlobalTheory.LoopC.RowGlue.main
