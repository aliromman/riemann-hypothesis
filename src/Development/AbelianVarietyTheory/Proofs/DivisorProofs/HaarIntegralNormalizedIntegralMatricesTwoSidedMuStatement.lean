module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedIntegralMatricesTwoSidedMu
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DgMatOne

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct

theorem _root_.GlobalTheory.T.haarIntegralNormalized_integralMatrices_twoSidedMul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E)
    (u : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) → ℂ) (A : GLw a w) (B : GLw b w),
    A ∈ GlobalTheory.LFun.KGL w (n := a) → B ∈ GlobalTheory.LFun.KGL w (n := b) →
    hint (intMat a b w) (fun X => u (Multiplicative.ofAdd (A.val * Multiplicative.toAdd X * B.val))) =
      hint (intMat a b w) u := by
  first | exact @GlobalTheory.BCT.HintInv.hint_intMat_mul_mul
