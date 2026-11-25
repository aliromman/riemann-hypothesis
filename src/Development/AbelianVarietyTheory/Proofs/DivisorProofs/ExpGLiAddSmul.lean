module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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

open NumberField

namespace GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E]

def expGLi (a : ℕ) (X : Matrix (Fin a) (Fin a) (Cinf E)) : GL (Fin a) (Cinf E) :=
  (Matrix.isUnit_exp X).unit

@[simp] theorem val_expGLi (a : ℕ) (X : Matrix (Fin a) (Fin a) (Cinf E)) :
    (expGLi a X).val = NormedSpace.exp X := rfl

theorem expGLi_add_smul (a : ℕ) (X : Matrix (Fin a) (Fin a) (Cinf E)) (s t : ℝ) :
    expGLi a ((s + t) • X) = expGLi a (s • X) * expGLi a (t • X) :=
  Units.ext (by
    rw [Units.val_mul, val_expGLi, val_expGLi, val_expGLi, add_smul]
    exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t))

@[simp] theorem expGLi_zero (a : ℕ) : expGLi a (0 : Matrix (Fin a) (Fin a) (Cinf E)) = 1 :=
  Units.ext (by rw [val_expGLi, NormedSpace.exp_zero, Units.val_one])

end GlobalTheory.CuspRep
