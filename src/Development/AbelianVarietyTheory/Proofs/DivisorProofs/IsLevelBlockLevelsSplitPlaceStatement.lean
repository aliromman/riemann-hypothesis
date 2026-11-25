module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DgMatOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLevelBlockLevelsSplitPlace
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

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct

theorem _root_.GlobalTheory.T.isLevel_blockLevels_splitPlace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E)
    (N : Subgroup (GLw n w)) (μ : (w.adicCompletion E)ˣ →* ℂˣ), IsSplitAt w → IsOpen (N : Set (GLw n w)) →
    IsOpen {x | μ x = 1} →
    IsLevel (thL a w) (GlobalTheory.LFun.KGL w (n := a)) (lev₁ h w N μ) ∧ IsLevel (thL b w) (GlobalTheory.LFun.KGL w (n := b)) (lev₂ h w N μ) := by
  first | exact @GlobalTheory.BCT.CtLevel.isLevel_lev_split
