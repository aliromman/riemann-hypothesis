module

public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
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

open scoped TensorProduct Matrix ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace GlobalTheory.DblTargetDelta

open Formalism.IndefR.DatumF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {nS nT : ℕ}

def topR (x : WOF F E nS (nT + nT)) : WOF F E nS nT := x.submatrix (finSumFinEquiv ∘ Sum.inl) id

def botR (x : WOF F E nS (nT + nT)) : WOF F E nS nT := x.submatrix (finSumFinEquiv ∘ Sum.inr) id

def deltaT (f₁ f₂ : WOF F E nS nT → ℂ) : WOF F E nS (nT + nT) → ℂ :=
  fun x => f₁ (topR x) * conj (f₂ (-botR x))

theorem deltaT_apply (f₁ f₂ : WOF F E nS nT → ℂ) (x : WOF F E nS (nT + nT)) :
    deltaT f₁ f₂ x = f₁ (topR x) * conj (f₂ (-botR x)) := rfl

end GlobalTheory.DblTargetDelta

end
