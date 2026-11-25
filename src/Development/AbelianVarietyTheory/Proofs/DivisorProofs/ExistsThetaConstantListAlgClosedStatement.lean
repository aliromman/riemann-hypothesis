module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantListAlgClosed
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_thetaConstantList_algClosed : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (θ : SecAt G L x), Odd m → (m : K) ≠ 0 → N = m ^ (4 * g) → PolFib G L g x → ∃ (pt : Fin N → (Over.mk x ⟶ G)) (c : Fin N → K), ThList G L ρ m x θ pt c := by
  first | exact @GlobalTheory.UMin.exists_thList
