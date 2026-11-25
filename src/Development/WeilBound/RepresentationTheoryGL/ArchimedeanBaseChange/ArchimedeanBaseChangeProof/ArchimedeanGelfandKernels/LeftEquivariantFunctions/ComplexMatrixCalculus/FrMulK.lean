module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.InstBorelUK
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

namespace PositivityTheory.RgBcC

variable {n : ℕ}

def FrOne : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ), lefFr n lam 1 = 1

def FrMulK : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ) (k k' : Matrix.unitaryGroup (Fin n) ℂ),
  lefFr n lam (k * k').1 = lefFr n lam k.1 * lefFr n lam k'.1

def FrIso : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ) (k : Matrix.unitaryGroup (Fin n) ℂ) (v : EV n lam), ‖lefFr n lam k.1 v‖ = ‖v‖

def FrCont : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ), Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => lefFr n lam k.1

end PositivityTheory.RgBcC
