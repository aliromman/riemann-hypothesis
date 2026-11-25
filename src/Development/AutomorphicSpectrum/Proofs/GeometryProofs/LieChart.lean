module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

def LieChart {S : Scheme.{0}} (G : Over S) [GrpObj G] {R : Type} [CommRing R] (x : Sp R ⟶ S) (f : R) : Prop :=
  ∃ (P : Type) (_ : AddCommGroup P) (_ : Module R P) (_ : Module (Localization.Away f) P)
    (_ : IsScalarTower R (Localization.Away f) P) (_ : Module.Finite (Localization.Away f) P)
    (_ : Module.Projective (Localization.Away f) P)
    (m : ∀ (C : Type) [CommRing C] [Algebra R C], IsUnit (algebraMap R C f) →
      LieModel G (spMap (algebraMap R C) ≫ x) (P →ₗ[R] C)),
    ∀ (C C' : Type) [CommRing C] [CommRing C'] [Algebra R C] [Algebra R C']
      (hC : IsUnit (algebraMap R C f)) (hC' : IsUnit (algebraMap R C' f)) (c : C →ₐ[R] C') (w : P →ₗ[R] C),
      ((m C' hC').pt (c.toLinearMap ∘ₗ w)).left = spMap (dualMap c.toRingHom) ≫ ((m C hC).pt w).left

end GlobalTheory.CompanionTheory.Ar
