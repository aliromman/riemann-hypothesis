module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.PeriodSpan

variable {X : Scheme.{0}} (G : Over X) [GrpObj G] (y : Sp ℂ ⟶ X)

def torusPts (E : TorusExtension ((Over.pullback y).obj G)) : Set (Over.mk y ⟶ G) :=
  letI := E.addCommGroup
  {x | ∃ t : Over.mk (𝟙 (Sp ℂ)) ⟶ splitTorus (Spec (.of ℂ)) E.X, (t ≫ E.i).left ≫ pullback.fst G.hom y = x.left}

def IsPerHol (ψ : ℂ → (Over.mk y ⟶ G)) : Prop :=
  (∀ s t, ψ (s + t) = ψ s * ψ t) ∧ IsHolTo Set.univ (fun s => (ψ s).left) ∧
    ψ (2 * Real.pi * Complex.I) = 1

def perHolSub : Subgroup (Over.mk y ⟶ G) :=
  Subgroup.closure (⋃ (ψ : ℂ → (Over.mk y ⟶ G)) (_ : IsPerHol G y ψ), Set.range ψ)

end GlobalTheory.PeriodSpan
