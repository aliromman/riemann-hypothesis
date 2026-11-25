module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBasicOpenKTrivOfFibre
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

theorem kTriv_away_of_kTriv_fibre : Out.GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (L : LB A.left) (K : Type) [Field K] (x : R →+* K), IsAbelianScheme A → L.IsLB → Out.RelAmple A L → Out.KTriv ((Over.pullback (spMap x)).obj A) (L.pull (pullback.fst A.hom (spMap x))) → ∃ f : R, x f ≠ 0 ∧ Out.KTriv ((Over.pullback (spMap (algebraMap R (Localization.Away f)))).obj A) (L.pull (pullback.fst A.hom (spMap (algebraMap R (Localization.Away f))))) := by
  intro _ R _ _ A _ L K _ x hA hL hR hK
  obtain ⟨f, hf, H⟩ := _root_.GlobalTheory.KTrivSpread.exists_kTriv_of_isUnit R A L K x ((Over.pullback (spMap x)).obj A)
    (pullback.fst A.hom (spMap x)) hA hL hR (ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback A (spMap x)) hK
  exact ⟨f, hf, H (Localization.Away f) (algebraMap R (Localization.Away f)) _ _
    (IsLocalization.Away.algebraMap_isUnit f) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback A _)⟩

end GlobalTheory
