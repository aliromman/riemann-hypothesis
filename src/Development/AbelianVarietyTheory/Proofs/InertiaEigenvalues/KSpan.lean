module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WordAppendSingle
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
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

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.MSpanDecay

variable (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)

def kSpan : Submodule ℂ (GA E a → ℂ) :=
  Submodule.span ℂ {F | ∃ (X : Type) (_ : MeasurableSpace X) (ν : Measure X) (_ : SFinite ν) (k : X → ℂ)
    (γ : X → GL (Fin a) (Cinf E)) (G : GA E a → ℂ), GlobalTheory.JSW.IsRapidInf ν k γ ∧ Good G ∧
      F = fun g => ∫ x, k x * G (g * infGL E a (γ x)) ∂ν}

end GlobalTheory.MSpanDecay
