module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ConstC
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
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf
namespace GlobalTheory.TypeAsm

theorem eqC_holds : EqC := by
  intro D X Y u t₁ t₂ h1 h2 h
  obtain ⟨l, m, l', m', c⟩ := t₁
  obtain ⟨l₂, m₂, l₂', m₂', c₂⟩ := t₂
  simp only at h1 h2
  subst h1 h2
  have hc : c = c₂ := by
    rw [← Quot.out_eq c, ← Quot.out_eq c₂]
    exact Quot.sound h
  subst hc
  rfl
end GlobalTheory.TypeAsm
