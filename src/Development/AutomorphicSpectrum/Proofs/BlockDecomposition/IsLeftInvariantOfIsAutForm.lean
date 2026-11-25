module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.HasModerateGrowthZero
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

open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.LeftInv

theorem ratGL_eq_diagonal (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (γ : GL (Fin a) E) : ratGL E a γ = AdelicGLn.diagonal E a γ :=
  Units.ext (Matrix.ext fun _ _ => rfl)

theorem isLeftInvariant_of_isAutForm : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    (a : ℕ) (φ : Sm E a), IsAutForm φ → AutomorphicForm.IsLeftInvariant φ.1 := by
  intro E _ _ _ a φ h γ g
  rw [← ratGL_eq_diagonal]
  exact h.left γ g

end GlobalTheory.CompanionTheory.LeftInv
