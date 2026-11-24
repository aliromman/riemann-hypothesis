module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Mathlib.RingTheory.SimpleRing.Principal
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

theorem isIntegral_of_isAbelianScheme_field (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A]
    (hA : IsAbelianScheme A) : IsIntegral A.left := by
  have := hA.smooth
  have := hA.geomConnected
  have := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres A.hom
  exact GeometricallyIntegral.isIntegral_of_subsingleton A.hom

theorem polAV_isIntegral_of_isAlgClosed :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)), IsIntegral P.A.left :=
  fun K _ _ P => isIntegral_of_isAbelianScheme_field K P.A P.isAb

end GlobalTheory
