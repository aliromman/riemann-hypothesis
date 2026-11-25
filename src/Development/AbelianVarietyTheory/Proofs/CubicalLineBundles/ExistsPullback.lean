module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsOfCmTriplePullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem PAT.exists_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (S S' : Scheme.{0}) (f : S' ⟶ S) (T : PAT H S), ∃ (T' : PAT H S') (_ : SABMap T'.t T.t f), T'.g = T.g := by
  intro E _ _ _ H S S' f T
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull f T.t
  obtain ⟨⟨T', ht, hg⟩, -⟩ := _root_.GlobalTheory.CM.PAT.exists_of_sabMap E H S S' f T _ m
  exact ⟨T', ht ▸ m, hg⟩

end GlobalTheory.CM
