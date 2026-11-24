module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.SharpIdent

theorem lift_comp_square {S S' : Scheme.{0}} {G : Over S} {G₁ G₂ T : Over S'} {φ : G₁.left ⟶ G.left}
    {ψ : G₂.left ⟶ G.left} {φ₂ : (G₁ ⊗ G₁).left ⟶ (G ⊗ G).left} {ψ₂ : (G₂ ⊗ G₂).left ⟶ (G ⊗ G).left}
    (hφ : IsSquare φ φ₂) (hψ : IsSquare ψ ψ₂) (x x' : T ⟶ G₁) (y y' : T ⟶ G₂) (h : x.left ≫ φ = y.left ≫ ψ)
    (h' : x'.left ≫ φ = y'.left ≫ ψ) : (lift x x').left ≫ φ₂ = (lift y y').left ≫ ψ₂ := by
  have e₁ : ((lift x x').left ≫ φ₂) ≫ (fst G G).left = ((lift y y').left ≫ ψ₂) ≫ (fst G G).left := by
    rw [Category.assoc, Category.assoc, hφ.1, hψ.1, ← Category.assoc, ← Category.assoc, ← Over.comp_left,
      ← Over.comp_left, lift_fst, lift_fst, h]
  have e₂ : ((lift x x').left ≫ φ₂) ≫ (snd G G).left = ((lift y y').left ≫ ψ₂) ≫ (snd G G).left := by
    rw [Category.assoc, Category.assoc, hφ.2, hψ.2, ← Category.assoc, ← Category.assoc, ← Over.comp_left,
      ← Over.comp_left, lift_snd, lift_snd, h']
  exact pullback.hom_ext e₁ e₂

end GlobalTheory.Poinc.SharpIdent
