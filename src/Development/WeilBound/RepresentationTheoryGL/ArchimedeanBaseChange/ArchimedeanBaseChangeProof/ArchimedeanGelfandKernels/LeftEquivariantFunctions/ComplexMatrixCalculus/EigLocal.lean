module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
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

open Matrix
open scoped ComplexConjugate Kronecker ContDiff

namespace PositivityTheory.RgBcC

open PositivityTheory.RgTw (Mat hb)

open scoped Matrix.Norms.Elementwise

def MatrixFrechetDerivativeAtZero : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ), DifferentiableAt ℝ (fr0 lam) (1 : Mat n) ∧ ∀ X : Mat n, X.IsHermitian →
  fderiv ℝ (fr0 lam) 1 X = (fderiv ℝ (fun x : Mat n => gamM (Mt x⁻¹)ᵀ) 1 X) ⊗ₖ (1 : Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ) +
    (1 : Matrix (Finset (Md n)) (Finset (Md n)) ℂ) ⊗ₖ fderiv ℝ (rhoW lam) 1 X

def EigLocal : Prop := ∀ (n : ℕ) (χ : Inf n) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f f' : Mat n → V),
  (∀ x ∈ GLs n, f x = f' x) → IsEig χ f → IsEig χ f'

end PositivityTheory.RgBcC
