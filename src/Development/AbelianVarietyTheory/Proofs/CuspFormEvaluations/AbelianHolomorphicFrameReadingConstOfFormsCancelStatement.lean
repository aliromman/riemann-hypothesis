module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AbelianHolomorphicFrameReadingConstOfFormsCancel
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianHolomorphicFrame_reading_const_of_forms_cancel : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (Z : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L.L φ ε)), t.IsGen → ∀ (N : ℕ) (q : (Fin N → ℂ) → (Sp ℂ ⟶ Z)) (Λ : K → (Fin N → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Ga : AddSubgroup (Fin N → ℂ)), IsHolFam q → (∀ z k, q z ≫ φ k = (Φ.e (Λ k z)).left) → Submodule.span ℝ (Ga : Set (Fin N → ℂ)) = ⊤ → (∀ gm ∈ Ga, (∀ z, q (z + gm) = q z) ∧ ∀ k, Λ k gm ∈ Φ.lat) → (∀ z w, ∑ k, (ε k : ℂ) * hermForm Φ.Hm (Λ k z) (Λ k w) = 0) → (∃ v : ℂ, v ≠ 0 ∧ ∀ z, Φ.GenRd φ ε t (q z) (fun k => Λ k z) v) ∧ ∀ gm ∈ Ga, ∏ k, Φ.χ (Λ k gm) ^ ε k = 1 := by
  first | exact @GlobalTheory.AnVal.genRd_const
