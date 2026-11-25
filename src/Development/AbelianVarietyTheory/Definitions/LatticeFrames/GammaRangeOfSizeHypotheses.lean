module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DiagAtScale
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
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2
namespace GlobalTheory.Core.Diag

def OneOn (S : Set ℝ) (gen : Bool) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ C : ℝ, 0 ≤ C ∧ ∃ thr : ℝ, ∀ C0 ∈ S, ∀ C' Cl : ℝ, thr ≤ C' → thr ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.BasicNotions.Ties D →
      Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → ConcTie X Y → (Y.tO u u).AbsConv →
      (Y.tO u u).pairSum ((Y.tO u u).one (if gen then (Y.tO u u).genSet else (Y.tO u u).ngSet)) ≤
        gamL D large₂.sc.L C * ddC X Y u u

end GlobalTheory.Core.Diag
